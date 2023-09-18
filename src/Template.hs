{-# LANGUAGE DerivingStrategies #-}

module Template where

import Prelude hiding (lookup)
import Expr
import Control.Monad.Trans.State.Strict
import qualified Data.IntMap.Lazy as L
import qualified Data.Map.Strict as S
import Control.Monad
import Control.Monad.Fix

type D m = m (Value m)
newtype Value m = Fun (D m -> D m)
type Env m = S.Map Name (D m)
type Heap m = L.IntMap (D m)

instance Show (Value m) where
  show (Fun _) = show "Fun"

class Monad m => MonadAlloc m where
  alloc :: (D m -> D m) -> m (D m)

class Monad m => MonadTrace m where
  stuck :: m v
  lookup :: Name -> m v -> m v
  update :: m v -> m v
  app1 :: m v -> m v
  app2 :: m v -> m v
  bind :: m v -> m v

ev :: (MonadAlloc m, MonadTrace m) => (Expr -> Env m -> D m) -> Expr -> Env m -> D m
ev ev e env = case e of
  Var x -> S.findWithDefault stuck x env
  App e x -> case S.lookup x env of
    Nothing -> stuck
    Just d  -> app1 (ev e env >>= \(Fun f) -> f d)
  Lam x e -> return (Fun (\d -> app2 (ev e (S.insert x d env))))
  Let x e1 e2 -> do
    let ext d = S.insert x (lookup x d) env
    d1 <- alloc (ev e1 . ext)
    bind (ev e2 (ext d1))

eval :: (MonadAlloc m, MonadTrace m) => Expr -> Env m -> D m
eval = ev eval

-----------------------
-- By-name
-----------------------
newtype ByName m a = ByName { unByName :: (m a) }
  deriving newtype (Functor,Applicative,Monad)
instance Monad m => MonadAlloc (ByName m) where
  alloc f = pure (fix f)

thingName :: (forall v. m v -> m v) -> ByName m v -> ByName m v
thingName f (ByName m) = ByName (f m)

instance MonadTrace m => MonadTrace (ByName m) where
  stuck = ByName stuck
  lookup x = thingName (lookup x)
  update = thingName update
  app1 = thingName app1
  app2 = thingName app2
  bind = thingName bind
instance Show (ByName m a) where
  show _ = "_"


-----------------------
-- By-need
-----------------------
newtype ByNeed m a = ByNeed { unByNeed :: StateT (Heap (ByNeed m)) m a }
  deriving newtype (Functor,Applicative,Monad)
fetch :: Monad m => Addr -> D (ByNeed m)
fetch a = join (ByNeed $ (L.! a) <$> get) -- This is μ(a)(μ)!
memo :: Monad m => Addr -> D (ByNeed m) -> D (ByNeed m)
memo a d = do
  v <- d
  ByNeed $ modify (L.insert a (return v))
  -- update (return v) -- URGH FIXME
  return v
instance Monad m => MonadAlloc (ByNeed m) where
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
instance Show (ByValue m a) where
  show _ = "_"

evalByName :: MonadTrace m => Expr -> m (Value (ByName m))
evalByName e = unByName $ eval e S.empty

evalByNeed :: MonadTrace m => Expr -> m (Value (ByNeed m), Heap (ByNeed m))
evalByNeed e = runStateT (unByNeed (eval e S.empty)) L.empty

evalByValue :: (MonadFix m, MonadTrace m) => Expr -> m (Value (ByValue m))
evalByValue e = unByValue $ eval e S.empty
