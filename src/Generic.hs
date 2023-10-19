{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE TypeFamilies #-}
module Generic where

import GHC.Exts (Constraint)

class Monad m => MonadEnv env var addr m | m -> env var addr where
  getEnv :: m env
  lookupVar :: var -> m addr
  withEnv :: env -> m v -> m v
  withExtendedEnv :: env -> var -> addr -> m v -> m v

class Monad m => MonadStore addr thunk m | m -> addr thunk where
  update :: addr -> thunk -> m ()
  lookupAddr :: addr -> m thunk

class Monad m => MonadAlloc addr m | m -> addr where
  fresh :: m addr

class Monad m => IsValue val env var expr m | m -> val env var expr where
  type JoinVal m a :: Constraint
  closure :: env -> var -> expr -> m val
  matchClosure :: JoinVal m a => val -> (env -> var -> expr -> m a) -> m a

class Monad m => IsThunk thunk env expr val m | m -> thunk env expr val where
  type JoinThunk m a :: Constraint
  thunk :: env -> Expr -> m thunk
  evaluated :: val -> m thunk
  matchThunk :: JoinThunk m a => thunk -> (env -> expr -> m a) -> (val -> m a) -> m a

data Expr = Var String | Lam String Expr | App Expr Expr deriving (Show,Eq)

eval :: (MonadEnv env String addr m,
         MonadStore addr thunk m,
         MonadAlloc addr m,
         MonadFail m,
         IsValue val env String Expr m,
         IsThunk thunk env Expr val m,
         JoinThunk m val, JoinVal m val)
     => Expr -> m val
eval expr = case expr of
  Var x -> do
    addr <- lookupVar x
    thunk <- lookupAddr addr
    matchThunk thunk
      -- Thunk env e
      (\env e -> do
        val' <- withEnv env (eval e)
        ev <- evaluated val'
        update addr ev
        return val'
      )
      -- Evaluated v
      (\v -> do
        return v
      )
  Lam x e -> do
    env <- getEnv
    closure env x e
  App e1 e2 -> do
    fun <- eval e1
    matchClosure fun $ \envFun param body -> do
      addr <- fresh
      env <- getEnv
      tnk <- thunk env e2
      update addr tnk
      withExtendedEnv envFun param addr (eval body)
{-# INLINABLE eval #-}
