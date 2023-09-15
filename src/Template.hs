{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DefaultSignatures #-}
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
--  alloc :: Name -> Env m -> (Env m -> D m) -> m (Env m)
  alloc :: (D m -> D m) -> m (D m)

class Monad m => MonadCompute m where
  stuck :: m a
  lookup :: m a -> m a
  update :: m a -> m a
  app1 :: m a -> m a
  app2 :: m a -> m a
  bind :: m a -> m a


ev :: (MonadAlloc m, MonadCompute m) => (Expr -> Env m -> D m) -> Expr -> Env m -> D m
ev ev e env = case e of
  Var x -> S.findWithDefault stuck x env
  App e x -> case S.lookup x env of
    Nothing -> stuck
    Just d  -> app1 (ev e env >>= \(Fun f) -> f d)
  Lam x e -> return (Fun (\d -> app2 (ev e (S.insert x d env))))
  Let x e1 e2 -> do
--    env' <- alloc x env (lookup . ev e1)
    let ext d = S.insert x (lookup d) env
    d1 <- alloc (ev e1 . ext)
    bind (ev e2 (ext d1))

eval :: (MonadAlloc m, MonadCompute m) => Expr -> Env m -> D m
eval = ev eval

newtype ByName m a = ByName { unByName :: (m a) }
  deriving newtype (Functor,Applicative,Monad)
instance Monad m => MonadAlloc (ByName m) where
  alloc f = pure (fix f)
thingName :: (forall a. m a -> m a) -> ByName m a -> ByName m a
thingName f (ByName m) = ByName (f m)
instance MonadCompute m => MonadCompute (ByName m) where
  stuck = ByName stuck
  lookup = thingName lookup
  update = thingName update
  app1 = thingName app1
  app2 = thingName app2
  bind = thingName bind
instance Show (ByName m a) where
  show _ = "_"
evalByName :: Expr -> Compute (Value (ByName Compute))
evalByName e = unByName $ eval e S.empty


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
instance MonadCompute m => MonadCompute (ByNeed m) where
  stuck = ByNeed (StateT (const stuck))
  lookup = thingNeed lookup
  update = thingNeed update
  app1 = thingNeed app1
  app2 = thingNeed app2
  bind = thingNeed bind
instance Show (ByNeed m a) where
  show _ = "_"
evalByNeed :: Expr -> Compute (Value (ByNeed Compute), Heap (ByNeed Compute))
evalByNeed e = runStateT (unByNeed (eval e S.empty)) L.empty


newtype ByValue m a = ByValue { unByValue :: (m a) }
  deriving newtype (Functor,Applicative,Monad,MonadFix)
instance Monad m => MonadAlloc (ByValue m) where
  alloc f = do
    v <- fix f -- TODO: FIXME
    return (return v)
thingValue :: (forall a. m a -> m a) -> ByValue m a -> ByValue m a
thingValue f (ByValue m) = ByValue (f m)
instance MonadCompute m => MonadCompute (ByValue m) where
  stuck = ByValue stuck
  lookup = thingValue lookup
  update = thingValue update
  app1 = thingValue app1
  app2 = thingValue app2
  bind = thingValue bind
instance Show (ByValue m a) where
  show _ = "_"
evalByValue :: Expr -> Compute (Value (ByValue Compute))
evalByValue e = unByValue $ eval e S.empty


data Compute a = Step (Compute a) | Ret !a | Stuck
  deriving Functor

instance Show a => Show (Compute a) where
  show (Step trc) = 'L':show trc
  show Stuck = "🗲"
  show (Ret a) = '⟨':show a++"⟩"

instance Applicative Compute where
  pure = Ret
  Step f <*> a = Step (f <*> a)
  Stuck <*> _ = Stuck
  f <*> Step a = Step (f <*> a)
  _ <*> Stuck = Stuck
  Ret f <*> Ret a = Ret (f a)

instance Monad Compute where
  Stuck >>= _ = Stuck
  Step d >>= k = Step (d >>= k)
  Ret a >>= k = k a

instance MonadCompute Compute where
  stuck = Stuck
  lookup = Step
  update = Step
  app1 = Step
  app2 = Step
  bind = Step
