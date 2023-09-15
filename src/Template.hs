{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
module Template where

import Prelude hiding (lookup)
import Expr
import Control.Monad.Trans.State.Strict
import qualified Data.IntMap.Lazy as L
import qualified Data.Map.Strict as S
import Control.Monad.Trans.Class

type D m = MemoT m (Value m)
newtype Value m = Fun (D m -> D m)
type Env m = S.Map Name (D m)

data Compute a = Step (Compute a) | Ret !a | Stuck
  deriving Functor

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

type Heap m = L.IntMap (D m)
newtype MemoT m a = MemoT (StateT (Heap m) m a)
  deriving newtype (Functor, Applicative, Monad)

instance MonadTrans MemoT where
  lift m = MemoT (lift m)

class Monad m => MonadCompute m where
  stuck :: m a
  lookup :: m a -> m a
  update :: m a -> m a
  app1 :: m a -> m a
  app2 :: m a -> m a
  bind :: m a -> m a

alloc :: Monad m => MemoT m Addr
alloc = MemoT $ (maybe 0 (\(k,_) -> k+1) . L.lookupMax) <$> get

upd :: Monad m => Addr -> D m -> MemoT m ()
upd a d = MemoT $ modify (L.insert a d)

fetch :: Monad m => Addr -> D m
fetch a = do
  d <- MemoT $ (L.! a) <$> get
  d

deref :: MonadCompute (MemoT m) => Addr -> D m
deref a = lookup (fetch a)

memo :: MonadCompute (MemoT m) => Addr -> D m -> D m
memo a d = do
  v <- d
  update (v <$ upd a (return v))

ev :: MonadCompute (MemoT m) => (Expr -> Env m -> D m) -> Expr -> Env m -> D m
ev ev e env = case e of
  Var x -> S.findWithDefault stuck x env
  App e x -> case S.lookup x env of
    Nothing -> stuck
    Just d  -> app1 (ev e env >>= \(Fun f) -> f d)
  Lam x e -> return (Fun (\d -> app2 (ev e (S.insert x d env))))
  Let x e1 e2 -> do
    a <- alloc
    let env' = S.insert x (deref a) env
    let d1 = ev e1 env'
    upd a (memo a d1)
    bind (ev e2 env')
