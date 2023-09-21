module Seq where

import Prelude hiding (lookup)
import Expr
import Template
import Control.Monad.Fix

type Evt f = forall v. f v -> f v

data Seq f v = Step (Evt f) (Seq f v) | Ret !v | Stuck
  deriving (Functor)

instance Applicative (Seq f) where
  pure = Ret
  Step s f <*> a = Step s (f <*> a)
  Stuck <*> _ = Stuck
  f <*> Step s a = Step s (f <*> a)
  _ <*> Stuck = Stuck
  Ret f <*> Ret a = Ret (f a)

instance Monad (Seq f) where
  Stuck >>= _ = Stuck
  Step s d >>= k = Step s (d >>= k)
  Ret a >>= k = k a

instance MonadFix (Seq f) where
  mfix f = trc
    where
      (trc,v) = go (f v)
      go (Step s t) = (Step s t', v)
        where
          (t', v) = go t
      go (Ret v) = (Ret v, v)
      go Stuck = (Stuck, undefined)

instance MonadTrace m => MonadTrace (Seq (m )) where
  stuck = Stuck
  lookup x = Step (lookup x)
  update = Step update
  app1 = Step app1
  app2 = Step app2
  bind = Step bind

getApproxSeq :: MonadTrace m => Seq m v -> [m ()]
getApproxSeq s = return () : case s of
  Step f s' -> map f (getApproxSeq s')
  _ -> []

evalByName :: MonadTrace m => Expr -> [m ()]
evalByName = getApproxSeq . Template.evalByName

evalByNeed :: MonadTrace m => Expr -> [m ()]
evalByNeed = getApproxSeq . Template.evalByNeed

evalByValue :: MonadTrace m => Expr -> [m ()]
evalByValue = getApproxSeq . Template.evalByValue
