{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
module Concrete where

import Prelude hiding (lookup, id, const)

import Generic(Expr(..),MonadEnv(..),MonadStore(..),MonadAlloc(..),IsValue(..),IsThunk(..))
import qualified Generic

import Data.Map.Strict(Map)
import qualified Data.Map.Strict as Map

import Text.Printf

newtype Env = Env (Map String Addr) deriving (Show, Eq)
newtype Store = Store (Map Addr MaybeThunk) deriving (Show, Eq)
type Addr = Int

data Val = Closure Env String Expr deriving (Show,Eq)
data MaybeThunk = Thunk Env Expr | Evaluated Val deriving (Show,Eq)

eval :: Expr -> Interp Val
eval expr = Generic.eval expr
{-# INLINE eval #-}

newtype Interp a = Interp {runInterp :: Env -> Store -> Either String (Store, a)}

instance MonadEnv Env String Addr Interp where
  getEnv = Interp (\env store -> return (store, env))
  lookupVar var = Interp $ \(Env env) store ->
    case Map.lookup var env of
      Just addr -> return (store, addr)
      Nothing -> Left (printf "Variable %s not bound in %s" var (show env))
  withEnv env (Interp f) = Interp (\_ store -> f env store)
  withExtendedEnv (Env env) var addr (Interp f) = Interp (\_ store -> f (Env (Map.insert var addr env)) store)
  {-# INLINE getEnv #-}
  {-# INLINE lookupVar #-}
  {-# INLINE withEnv #-}
  {-# INLINE withExtendedEnv #-}

instance MonadStore Addr MaybeThunk Interp where
  update addr tnk = Interp (\_ (Store store) -> return (Store (Map.insert addr tnk store), ()))
  lookupAddr addr = Interp $ \_ st@(Store store) ->
    case Map.lookup addr store of
      Just tnk -> return (st, tnk)
      Nothing -> Left (printf "Address %s not bound in %s" (show addr) (show store))
  {-# INLINE update #-}
  {-# INLINE lookupAddr #-}

instance MonadAlloc Addr Interp where
  fresh = Interp $ \_ s@(Store store) ->
    let addr = if Map.null store then 0 else fst (Map.findMax store) + 1
    in return (s, addr)
  {-# INLINE fresh #-}

instance IsValue Val Env String Expr Interp where
  type JoinVal Interp a = ()
  closure env param body = return (Closure env param body)
  matchClosure val k =
    case val of
      Closure env param body ->
        k env param body
  {-# INLINE closure #-}
  {-# INLINE matchClosure #-}

instance IsThunk MaybeThunk Env Expr Val Interp where
  type JoinThunk Interp a = ()
  thunk env e = return (Thunk env e)
  evaluated val = return (Evaluated val)
  matchThunk thunk k1 k2 =
    case thunk of
      Thunk env expr -> k1 env expr
      Evaluated val -> k2 val
  {-# INLINE thunk #-}
  {-# INLINE evaluated #-}
  {-# INLINE matchThunk #-}


instance Functor Interp where
  fmap f (Interp g) = Interp $ \env store -> case g env store of
    Right (store', a) -> Right (store', f a)
    Left err -> Left err
  {-# INLINE fmap #-}

instance Applicative Interp where
  pure a = Interp (\_ store -> Right (store, a))
  Interp f <*> Interp g = Interp $ \env store ->
    case f env store of
      Right (store', f') ->
        case g env store' of
          Right (store'', g') -> Right (store'', f' g')
          Left err -> Left err
      Left err -> Left err
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}

instance Monad Interp where
  return = pure
  Interp f >>= k = Interp $ \env store ->
    case f env store of
      Right (store', a) -> runInterp (k a) env store'
      Left err -> Left err
  {-# INLINE return #-}
  {-# INLINE (>>=) #-}

instance MonadFail Interp where
  fail err = Interp (\_ _ -> Left err)
  {-# INLINE fail #-}

-- Tests

id :: Expr
id = Lam "x" (Var "x")

const :: Expr
const = Lam "x" (Lam "y" (Var "y"))

e1 :: Expr
e1 = App id const

e2 :: Expr
e2 = App (App const id) id

runEval :: Expr -> Env -> Store -> Either String (Store, Val)
runEval e = runInterp (eval e)

runEval' :: Expr -> Either String (Store, Val)
runEval' e = runEval e (Env Map.empty) (Store Map.empty)
