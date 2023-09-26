{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE TypeFamilies #-}

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
import Later
import Data.Kind
import Data.Functor.Identity

type D m = m (Value m)
data Value m = Stuck | Fun (D m -> D m) | Con ConTag [D m]
type Env = S.Map Name

instance Show (Value m) where
  show (Fun _) = show "λ"
  show (Con k _) = show k
  show Stuck = "🗲"

class (Functor (L m), Monad m) => MonadTrace m where
  type L m :: Type -> Type
  lookup :: Name -> L m (m v) -> m v
  app1 :: m v -> m v
  app2 :: m v -> m v
  bind :: m v -> m v
  case1 :: m v -> m v
  case2 :: m v -> m v
  let_ :: m v -> m v
  update :: m v -> m v

-- | The reason we have a full type class rather than just a Galois Connection
--   P(Value m) <-> Val m (where Val is the abstract value)
-- is that we don't want to enumerate all of P(Value m) in the select case!
-- So this is about efficiency -- Posets are quite an inefficient representaiton
-- compared to symbolic reasoning (such as in GHC's `SubDemand`).
class Monad m => IsValue m v where
  stuck :: m v -- stuck >>= k = stuck
  injFun :: (m v -> m v) -> m v
  apply :: v -> m v -> m v
  injCon :: ConTag -> [m v] -> m v
  select :: v -> [(ConTag, [m v] -> m v)] -> m v

class (MonadTrace m) => MonadAlloc m v where
  alloc :: (L m (m v) -> m v) -> m (L m (m v))

eval :: forall m v. (MonadTrace m, IsValue m v, MonadAlloc m v) => Expr -> Env (m v) -> m v
eval e env = case e of
  Var x -> S.findWithDefault stuck x env
  App e x -> case S.lookup x env of
    Nothing -> stuck
    Just d  -> app1 (eval e env) >>= \v -> apply v d
  Lam x e -> injFun (\d -> app2 (eval e (S.insert x d env)))
  Let x e1 e2 -> do
    let ext d = S.insert x (lookup x d) env
    d1 <- alloc (\d1 -> eval e1 (ext d1))
    bind (eval e2 (ext d1))
  ConApp k xs -> case traverse (env S.!?) xs of
    Just ds
      | length xs == conArity k
      -> injCon k ds
    _ -> stuck
  Case e alts -> case1 $ eval e env >>= \v ->
    select v [ (k, alt_cont xs rhs) | (k,xs,rhs) <- alts ]
    where
      alt_cont xs rhs ds
        | length xs == length ds = case2 (eval rhs (insertMany env xs ds))
        | otherwise              = stuck
      insertMany :: Env (m v) -> [Name] -> [m v] -> Env (m v)
      insertMany env xs ds = foldr (uncurry S.insert) env (zip xs ds)

--  Case e alts -> case1 $ eval e env >>= \case
--    Con k ds
--      | Just (_,xs,rhs) <- List.find (\(k',_,_) -> k' == k) alts
--      , length xs == length ds
--      , length xs == conArity k
--      -> case2 (eval rhs (insertMany env xs ds))
--    _ -> stuck
--    where
--      insertMany :: Env m -> [Name] -> [D m] -> Env m
--      insertMany env xs ds = foldr (uncurry S.insert) env (zip xs ds)

-- | The type of coinductive traces, in the sense that @MonadCoindTrace m => m@
-- denotes a potentially infinite program trace.
type MonadCoindTrace m = (MonadTrace m, L m ~ Later)
-- | The type of inductive traces, in the sense that @MonadIndTrace m => m@
-- denotes a finite program trace.
type MonadIndTrace m = (MonadTrace m, L m ~ Identity)

instance MonadTrace m => IsValue m (Value m) where
  stuck = return Stuck
  injFun f = return (Fun f)
  injCon k ds = return (Con k ds)
  apply (Fun f) d = f d
  apply _       _ = stuck
  select v alts
    | Con k ds <- v
    , Just (_,alt) <- List.find (\(k',_) -> k' == k) alts
    = alt ds
    | otherwise
    = stuck

-----------------------
-- By-name
-----------------------
newtype ByName m a = ByName { unByName :: (m a) }
  deriving newtype (Functor,Applicative,Monad)

liftName :: (m v -> m v) -> ByName m v -> ByName m v
liftName f (ByName m) = ByName (f m)

liftNameL :: Functor l => (l (m v) -> m v) -> l (ByName m v) -> ByName m v
liftNameL f = ByName . f . fmap unByName

instance MonadCoindTrace m => MonadTrace (ByName m) where
  type L (ByName m) = Later
  lookup x = liftNameL (lookup x)
  app1 = liftName app1
  app2 = liftName app2
  bind = liftName bind
  case1 = liftName case1
  case2 = liftName case2
  update = liftName update
  let_ = liftName let_

instance (MonadTrace (ByName m)) => MonadAlloc (ByName m) (Value (ByName m)) where
  alloc f = pure (\_α -> (löb f))

instance Show (ByName m a) where
  show _ = "_"


-----------------------
-- By-need
-----------------------
type Addr = Int
type Heap m = L.IntMap (Later (D m)) -- Addr -> Later a
newtype ByNeed m a = ByNeed { unByNeed :: StateT (Heap (ByNeed m)) m a }
  deriving newtype (Functor,Applicative,Monad)

liftNeed :: (forall a. m a -> m a) -> ByNeed m a -> ByNeed m a
liftNeed f (ByNeed (StateT m)) = ByNeed (StateT (\h -> f (m h)))

liftNeedL :: Functor l => (forall a. l (m a) -> m a) -> l (ByNeed m v) -> ByNeed m v
liftNeedL f m = ByNeed (StateT (\h -> f (fmap (($ h) . runStateT . unByNeed) m)))

instance MonadCoindTrace m => MonadTrace (ByNeed m) where
  type L (ByNeed m) = Later
  lookup x = liftNeedL (lookup x)
  app1 = liftNeed app1
  app2 = liftNeed app2
  bind = liftNeed bind
  case1 = liftNeed case1
  case2 = liftNeed case2
  update = liftNeed update
  let_ = liftNeed let_

fetch :: Monad m => Addr -> Later (D (ByNeed m))
fetch a α = do
  μ <- ByNeed get
  (μ L.! a) α

memo :: MonadCoindTrace m => Addr -> D (ByNeed m) -> D (ByNeed m)
memo a d = do
  v <- d
  update $ do
    ByNeed $ modify (L.insert a (\_α -> (return v)))
    return v

instance MonadCoindTrace m => MonadAlloc (ByNeed m) (Value (ByNeed m)) where
  alloc f = do
    a <- ByNeed $ maybe 0 (\(k,_) -> k+1) . L.lookupMax <$> get
    let ld = fetch a
    ByNeed $ modify (L.insert a (\_α -> memo a (f ld)))
    return ld

instance Show (ByNeed m a) where
  show _ = "_"


-----------------------
-- By-value
-----------------------
newtype ByValue m a = ByValue { unByValue :: (m a) }
  deriving newtype (Functor,Applicative,Monad,MonadFix)

liftValue :: (forall a. m a -> m a) -> ByValue m a -> ByValue m a
liftValue f (ByValue m) = ByValue (f m)

liftValueL :: Functor l => (l (m v) -> m v) -> l (ByValue m v) -> ByValue m v
liftValueL f = ByValue . f . fmap unByValue

instance MonadCoindTrace m => MonadTrace (ByValue m) where
  type L (ByValue m) = Later
  lookup x = liftValueL (lookup x)
  app1 = liftValue app1
  app2 = liftValue app2
  bind = liftValue bind
  case1 = liftValue case1
  case2 = liftValue case2
  update = liftValue update
  let_ = liftValue let_

instance (MonadFix m, MonadTrace m, L m ~ Later) => MonadAlloc (ByValue m) (Value (ByValue m)) where
  -- | `mfix` is generally untypable in guarded type theory.
  -- We'd need to communicate the number of steps that `m v` needs
  -- to produce the value `Later v`, and the `Later v` can only be used
  -- in `m v` after it has performed that many steps.
  --
  -- Such termination properties must be guaranteed by a strong object type
  -- system.
  -- In the untyped case, we'd need an explicit heap for the
  -- initial black hole, which would be a bit more complicated and
  -- rather like call-by-need.
  --
  -- We will simply assume that all letrecs are "statically constructive"
  -- as in OCaml.
  alloc f = do
    v <- let_ $ mfix $ \v -> f (\_α -> return v)
    return (\_α -> return v)

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

parLöb :: MonadFix m => (Later (Fork (ParT m) a) -> ParT m a) -> ParT m a
parLöb f = ParT $ mfix (unParT . f . pure) >>= \case
    Empty -> pure Empty
    Single a -> pure (Single a)
    Fork l r -> pure (Fork (parLöb (leftT . f)) (parLöb (rightT . f)))

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

liftClair :: (forall a. m a -> m a) -> Clairvoyant m a -> Clairvoyant m a
liftClair f (Clairvoyant (ParT mforks)) = Clairvoyant $ ParT $ f mforks

liftClairL :: Functor l => (forall a. l (m a) -> m a) -> l (Clairvoyant m a) -> Clairvoyant m a
liftClairL f lm = Clairvoyant $ ParT $ f $ fmap (unParT . unClair) lm

instance MonadCoindTrace m => MonadTrace (Clairvoyant m) where
  type L (Clairvoyant m) = Later
  lookup x = liftClairL (lookup x)
  app1 = liftClair app1
  app2 = liftClair app2
  bind = liftClair bind
  case1 = liftClair case1
  case2 = liftClair case2
  update = liftClair update
  let_ = liftClair let_

instance forall m. (MonadFix m, MonadTrace m, L m ~ Later) => MonadAlloc (Clairvoyant m) (Value (Clairvoyant m)) where
  alloc f = Clairvoyant (skip <|> let')
    where
      skip = return (\_α -> Clairvoyant empty)
      let' = do
        v <- parLöb $ unClair . let_ . f . fmap (Clairvoyant . ParT . pure)
        return (\_α -> return v)

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

evalByName :: forall m. MonadCoindTrace m => Expr -> m (Value (ByName m))
evalByName e = unByName $ eval @(ByName m) e S.empty

evalByNeed :: forall m. MonadCoindTrace m => Expr -> m (Value (ByNeed m), Heap (ByNeed m))
evalByNeed e = runStateT (unByNeed (eval @(ByNeed m) e S.empty)) L.empty

evalByValue :: forall m. (MonadFix m, MonadCoindTrace m) => Expr -> m (Value (ByValue m))
evalByValue e = unByValue $ eval @(ByValue m) e S.empty

evalClairvoyant :: forall m. (MonadRecord m, MonadFix m, MonadCoindTrace m) => Expr -> m (Value (Clairvoyant m))
evalClairvoyant e = runClair $ eval @(Clairvoyant m) e S.empty


-- Want this, but hard to get because we need a Monad instance for FinSim:
--
-- boundT :: (MonadCoindTrace m1, MonadIndTrace m2) => Int -> m1 v -> Maybe (m2 v)
-- boundT 0 _ = Nothing
-- boundT n (Delay t) = Delay . Identity <$> boundT (n-1) (t unsafeTick)
-- boundT _ Stuck = Just Stuck
-- boundT _ (Ret v) = Just (Ret v)
--
-- newtype FinSim m a = FinSim { unFinSim :: Int -> Maybe (m a) }
--   deriving Functor

-- instance Applicative f => Applicative (FinSim f) where
--   pure = FinSim . const . Just . pure
--   FinSim f <*> FinSim a = FinSim $ \n -> f n <*>

-- liftSpendFuel :: Monad m => (m v -> m v) -> FinSim m v -> FinSim m v
-- liftSpendFuel f (FinSim m) = FinSim $ ReaderT $ \n -> do
--   guard (n > 0)
--   runReaderT m (n-1)

-- instance (MonadTrace m, Applicative (L m)) => MonadTrace (FinSim m) where
--   type L (FinSim m) = Identity
--   stuck = FinSim (lift $ lift stuck)
--   lookup x (Identity m) = FinSim $ mapReaderT (mapMaybeT (lookup x . pure)) (unFinSim (spendFuel m))
