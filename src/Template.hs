{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}

module Template where

import Prelude hiding (lookup)
import Expr
import Control.Monad.Trans.State.Strict
import qualified Data.IntMap.Lazy as L
import qualified Data.Map.Strict as S
import Control.Monad
import Control.Monad.Fix
import Data.Coerce
import Data.Maybe
import Control.Applicative
import Debug.Trace
import qualified Data.List as List

type D m = m (Value m)
data Value m = Fun (D m -> D m) | Con ConTag [D m]
type Env m = S.Map Name (D m)

instance Show (Value m) where
  show (Fun _) = show "Fun"
  show (Con k _) = show k

class Monad m => MonadAlloc m where
  alloc :: (D m -> D m) -> m (D m)

class Monad m => MonadTrace m where
  stuck :: m v
  lookup :: Name -> m v -> m v
  update :: m v -> m v
  app1 :: m v -> m v
  app2 :: m v -> m v
  bind :: m v -> m v
  case1 :: m v -> m v
  case2 :: m v -> m v

insertMany :: Env m -> [Name] -> [D m] -> Env m
insertMany env xs ds = foldr (uncurry S.insert) env (zip xs ds)

eval :: (MonadAlloc m, MonadTrace m) => Expr -> Env m -> D m
eval e env = case e of
  Var x -> S.findWithDefault stuck x env
  App e x -> case S.lookup x env of
    Nothing -> stuck
    Just d  -> app1 $ eval e env >>= \case
      Fun f -> f d
      _     -> stuck
  Lam x e -> return (Fun (\d -> app2 (eval e (S.insert x d env))))
  Let x e1 e2 -> do
    let ext d = S.insert x (lookup x d) env
    d1 <- alloc (\d1 -> eval e1 (ext d1))
    bind (eval e2 (ext d1))
  ConApp k xs -> case traverse (env S.!?) xs of
    Just ds
      | length xs == conArity k
      -> return (Con k ds)
    _ -> stuck
  Case e alts -> case1 $ eval e env >>= \case
    Con k ds
      | Just (_,xs,rhs) <- List.find (\(k',_,_) -> k' == k) alts
      , length xs == length ds
      , length xs == conArity k
      -> case2 (eval rhs (insertMany env xs ds))
    _ -> stuck

-----------------------
-- By-name
-----------------------
newtype ByName m a = ByName { unByName :: (m a) }
  deriving newtype (Functor,Applicative,Monad)
instance Monad m => MonadAlloc (ByName m) where
  alloc f = pure (fix f)

thingName :: (m v -> m v) -> ByName m v -> ByName m v
thingName f (ByName m) = ByName (f m)

instance MonadTrace m => MonadTrace (ByName m) where
  stuck = ByName stuck
  lookup x = thingName (lookup x)
  update = thingName update
  app1 = thingName app1
  app2 = thingName app2
  bind = thingName bind
  case1 = thingName case1
  case2 = thingName case2
instance Show (ByName m a) where
  show _ = "_"


-----------------------
-- By-need
-----------------------
type Addr = Int
type Heap m = L.IntMap (D m) -- Addr -> D m
newtype ByNeed m a = ByNeed { unByNeed :: StateT (Heap (ByNeed m)) m a }
  deriving newtype (Functor,Applicative,Monad)
fetch :: Monad m => Addr -> D (ByNeed m)
fetch a = join (ByNeed $ (L.! a) <$> get) -- This is μ(a)(μ)!
memo :: MonadTrace m => Addr -> D (ByNeed m) -> D (ByNeed m)
memo a d = do
  v <- d
  ByNeed $ modify (L.insert a (return v))
  update (return v)
instance MonadTrace m => MonadAlloc (ByNeed m) where
  alloc f = do
    a <- ByNeed $ maybe 0 (\(k,_) -> k+1) . L.lookupMax <$> get
    let d = fetch a
    ByNeed $ modify (L.insert a (memo a (f d)))
    return d
thingNeed :: (forall a. m a -> m a) -> ByNeed m a -> ByNeed m a
thingNeed f (ByNeed (StateT m)) = ByNeed (StateT (\h -> f (m h)))
instance MonadTrace m => MonadTrace (ByNeed m) where
  stuck = ByNeed (StateT (const stuck))
  lookup x = thingNeed (lookup x)
  update = thingNeed update
  app1 = thingNeed app1
  app2 = thingNeed app2
  bind = thingNeed bind
  case1 = thingNeed case1
  case2 = thingNeed case2
instance Show (ByNeed m a) where
  show _ = "_"


-----------------------
-- By-value
-----------------------
newtype ByValue m a = ByValue { unByValue :: (m a) }
  deriving newtype (Functor,Applicative,Monad,MonadFix)
instance MonadFix m => MonadAlloc (ByValue m) where
  alloc f = do
    v <- mfix $ \v -> f (return v)
    return (return v)
thingValue :: (forall a. m a -> m a) -> ByValue m a -> ByValue m a
thingValue f (ByValue m) = ByValue (f m)
instance MonadTrace m => MonadTrace (ByValue m) where
  stuck = ByValue stuck
  lookup x = thingValue (lookup x)
  update = thingValue update
  app1 = thingValue app1
  app2 = thingValue app2
  bind = thingValue bind
  case1 = thingValue case1
  case2 = thingValue case2
instance Show (ByValue m a) where
  show _ = "_"


-----------------------
-- Clairvoyant By-value
-----------------------
data Fork f a = Empty | Single !a | Fork (f a) (f a)
  deriving Functor
newtype ParT m a = ParT { unParT :: m (Fork (ParT m) a) }
  deriving Functor
instance Monad m => Applicative (ParT m) where
  pure a = ParT (pure (Single a))
  (<*>) = ap
instance Monad m => Alternative (ParT m) where
  empty = ParT (pure Empty)
  l <|> r = ParT (pure (Fork l r))
instance Monad m => Monad (ParT m) where
  ParT mas >>= k = ParT $ mas >>= \case
    Empty -> pure Empty
    Single a -> unParT (k a)
    Fork l r -> pure (Fork (l >>= k) (r >>= k))

left :: Fork (ParT m) a -> ParT m a
left (Fork l _) = l

right :: Fork (ParT m) a -> ParT m a
right (Fork _ r) = r

leftT :: Monad m => ParT m a -> ParT m a
leftT (ParT m) = ParT $ m >>= \case
  Fork l _ -> unParT l

rightT :: Monad m => ParT m a -> ParT m a
rightT (ParT m) = ParT $ m >>= \case
  Fork _ r -> unParT r

parFix :: MonadFix m => (Fork (ParT m) a -> ParT m a) -> ParT m a
parFix f = ParT $ mfix (unParT . f) >>= \case
    Empty -> pure Empty
    Single a -> pure (Single a)
    Fork l r -> pure (Fork (parFix (leftT . f)) (parFix (rightT . f)))

-- mfix f = ListT $ mfix (runListT . f . head) >>= \ xs -> case xs of
--     [] -> return []
--     x:_ -> liftM (x:) (runListT (mfix (mapListT (liftM tail) . f)))
-- {-# INLINE mfix #-}
-- instance MonadFix m => MonadFix (ParT m) where
--   mfix f = ParT $ mfix g
--     where
--       g as = let ~(a,as') = case as of
--                    [] -> error "Did not produce anything"
--                    a:as' -> (a,as')
--              in unParT (f a) <> [ mas | a <- as', mas <- unParT (f a) ]

instance (Show a, forall a. Show a => Show (m a)) => Show (Fork (ParT m) a) where
  show Empty = "Empty"
  show (Single a) = show a
  show (Fork l r) = "Fork(" ++ show l ++ "," ++ show r ++ ")"

instance (Show a, forall a. Show a => Show (m a)) => Show (ParT m a) where
  show (ParT m) = show m

-- This is VERY weird
class Monad m => MonadRecord m where
  recordIfJust :: m (Maybe a) -> Maybe (m a)

newtype Clairvoyant m a = Clairvoyant { unClair :: ParT m a }
  deriving newtype (Functor,Applicative,Monad)
instance (MonadFix m, forall a. Show a => Show (m a)) => MonadAlloc (Clairvoyant m) where
  alloc f = Clairvoyant (skip <|> let_)
    where
      skip = return (Clairvoyant empty)
      let_ = do
        v <- parFix $ unClair . f . Clairvoyant . ParT . pure
        return (return v)
thingClair :: (forall a. m a -> m a) -> Clairvoyant m a -> Clairvoyant m a
thingClair f (Clairvoyant (ParT mforks)) = Clairvoyant $ ParT $ f mforks
instance MonadTrace m => MonadTrace (Clairvoyant m) where
  stuck = Clairvoyant (ParT stuck)
  lookup x = thingClair (lookup x)
  update = thingClair update
  app1 = thingClair app1
  app2 = thingClair app2
  bind = thingClair bind
  case1 = thingClair case1
  case2 = thingClair case2
instance (Show a, forall a. Show a => Show (m a)) => Show (Clairvoyant m a) where
  show (Clairvoyant m) = show m

headParT :: MonadRecord m => ParT m a -> m (Maybe a)
headParT m = go m
  where
    go :: MonadRecord m => ParT m a -> m (Maybe a)
    go (ParT m) = m >>= \case
      Empty    -> pure Nothing
      Single a -> pure (Just a)
      Fork l r -> case recordIfJust (go l) of
        Nothing -> go r
        Just m  -> Just <$> m

runClair :: MonadRecord m => D (Clairvoyant m) -> m (Value (Clairvoyant m))
runClair (Clairvoyant m) = headParT m >>= \case
  Nothing -> error "There should have been at least one Clairvoyant trace"
  Just t  -> pure t

evalByName :: forall m. MonadTrace m => Expr -> m (Value (ByName m))
evalByName e = unByName $ eval @(ByName m) e S.empty

evalByNeed :: forall m. MonadTrace m => Expr -> m (Value (ByNeed m), Heap (ByNeed m))
evalByNeed e = runStateT (unByNeed (eval @(ByNeed m) e S.empty)) L.empty

evalByValue :: forall m. (MonadFix m, MonadTrace m) => Expr -> m (Value (ByValue m))
evalByValue e = unByValue $ eval @(ByValue m) e S.empty

evalClairvoyant :: forall m. (MonadRecord m, MonadFix m, MonadTrace m, forall a. Show a => Show (m a)) => Expr -> m (Value (Clairvoyant m))
evalClairvoyant e = runClair $ eval @(Clairvoyant m) e S.empty

