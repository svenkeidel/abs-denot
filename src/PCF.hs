module PCF where
import Data.Kind
import Numeric.Natural
import qualified Data.Map.Strict as S

type Name = String

data Expr
  = Var Name
  | Lam Name Expr
  | App Expr Expr
  | Y Name Expr
  | Zero
  | Succ Expr
  | Pred Expr
  | IfZero Expr Expr Expr

type D m = m (Value m)
data Value m = Lit Natural | Fun (D m -> D m)
type Env = S.Map Name

class (Functor (L m), Monad m) => MonadTrace m where
  type L m :: Type -> Type
  lookup :: Name -> L m (m v) -> m v
  unroll :: Name -> L m (m v) -> m v
  app1 :: m v -> m v
  app2 :: m v -> m v
  bind :: m v -> m v
  case1 :: m v -> m v
  case2 :: m v -> m v
  let_ :: m v -> m v
  update :: m v -> m v

class Monad m => IsValue m v where
  stuck :: m v
  injLit :: Natural -> m v
  ifZero :: v -> m v -> m v -> m v
  injFun :: (m v -> m v) -> m v
  apply :: v -> m v -> m v

class (MonadTrace m) => MonadAlloc m v where
  alloc :: (L m (m v) -> m v) -> m (L m (m v))

eval :: forall m v. (MonadTrace m, IsValue m v, MonadAlloc m v) => Expr -> Env v -> m v
eval e env = case e of
  Var x -> S.findWithDefault stuck x env
  App e a -> do
    v <- eval a env
    case S.lookup x env of
    Nothing -> stuck
    Just d  -> app1 (eval e env) >>= \v -> apply v d
  Lam x e -> injFun (\d -> app2 (eval e (S.insert x d env)))
  Y x f -> do
    ld <- alloc (\ld -> eval f (S.insert x (unroll ld) env))
    unroll ld
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

