{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DerivingStrategies #-}
module PCF where

import Prelude hiding (lookup, succ, pred)
import Data.Kind
import Numeric.Natural
import qualified Data.Map.Strict as S
import Later
import Bare
import Data.Functor.Identity

type Name = String
type Label = Int

data Expr
  = Var Label Name
  | Lam Label Name Expr
  | App Label Expr Expr
  | Y Name Expr
  | Zero
  | Succ Expr
  | Pred Expr
  | IfZero Expr Expr Expr
  deriving Show

type Env = S.Map Name

class (Functor (L m), Monad m) => MonadTrace m where
  type L m :: Type -> Type
  unroll :: L m (m v) -> m v
  lookup :: Label -> m v -> m v
  app1 :: m v -> m v
  app2 :: m v -> m v
  app3 :: m v -> m v

class Monad m => IsValue m v where
  stuck :: m v
  zero :: m v
  succ :: v -> m v
  pred :: v -> m v
  ifZero :: v -> m v -> m v -> m v
  injFun :: Label -> (m v -> m v) -> m v
  apply :: Label -> v -> m v -> m v

class (MonadTrace m) => MonadAlloc m v where
  alloc :: (L m (m v) -> m v) -> m (L m (m v))

-- | The type of coinductive traces, in the sense that @MonadCoindTrace m => m@
-- denotes a potentially infinite program trace.
type MonadCoindTrace m = (MonadTrace m, L m ~ Later)
-- | The type of inductive traces, in the sense that @MonadIndTrace m => m@
-- denotes a finite program trace.
type MonadIndTrace m = (MonadTrace m, L m ~ Identity)

eval :: forall m v. (MonadTrace m, IsValue m v, MonadAlloc m v) => Expr -> Env (m v) -> m v
eval e env = case e of
  Var l x -> lookup l (S.findWithDefault stuck x env)
  App l e a -> do
    ve <- app1 (eval e env)
    va <- app2 (eval a env) -- TODO: transitions??
--    d <- lookup <$> alloc (\_ld -> return va)
    apply l ve (return va)
  Lam l x e -> injFun l (\d -> app3 (eval e (S.insert x d env)))
  Y x f -> do
    ld <- alloc (\ld -> eval f (S.insert x (unroll ld) env))
    unroll ld
  Zero -> zero
  Succ e -> eval e env >>= succ
  Pred e -> eval e env >>= pred
  IfZero c t e -> eval c env >>= \v -> ifZero v (eval t env) (eval e env)

type D m = m (Value m)
data Value m = Lit Natural | Fun (D m -> D m)

-----------------------
-- By-value
-----------------------
newtype ByValue m a = ByValue { unByValue :: (m a) }
  deriving newtype (Functor,Applicative,Monad)

liftValue :: (forall a. m a -> m a) -> ByValue m a -> ByValue m a
liftValue f (ByValue m) = ByValue (f m)

liftValueL :: Functor l => (l (m v) -> m v) -> l (ByValue m v) -> ByValue m v
liftValueL f = ByValue . f . fmap unByValue

instance MonadCoindTrace m => MonadTrace (ByValue m) where
  type L (ByValue m) = Later
  unroll = liftValueL unroll
  lookup l = liftValue (lookup l)
  app1 = liftValue app1
  app2 = liftValue app2
  app3 = liftValue app3

instance (MonadCoindTrace m) => MonadAlloc (ByValue m) (Value (ByValue m)) where
  alloc f = pure (\_α -> löb f)

instance Show (ByValue m a) where
  show _ = "_"

blah = eval @LBare
