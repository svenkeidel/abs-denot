module PrefixTrace where

import Prelude hiding (lookup)
import Expr
import Template
import Control.Monad.Fix

type Evt f = forall v. f v -> f v

data PrefixTrace f v = Step (Evt f) (PrefixTrace f v) | Ret !v | Stuck
  deriving (Functor)

instance Applicative (PrefixTrace f) where
  pure = Ret
  Step s f <*> a = Step s (f <*> a)
  Stuck <*> _ = Stuck
  f <*> Step s a = Step s (f <*> a)
  _ <*> Stuck = Stuck
  Ret f <*> Ret a = Ret (f a)

instance Monad (PrefixTrace f) where
  Stuck >>= _ = Stuck
  Step s d >>= k = Step s (d >>= k)
  Ret a >>= k = k a

instance MonadFix (PrefixTrace f) where
  mfix f = trc
    where
      (trc,v) = go (f v)
      go (Step s t) = (Step s t', v)
        where
          (t', v) = go t
      go (Ret v) = (Ret v, v)
      go Stuck = (Stuck, undefined)

instance MonadTrace m => MonadTrace (PrefixTrace (m )) where
  stuck = Stuck
  lookup x = Step (lookup x)
  update = Step update
  app1 = Step app1
  app2 = Step app2
  bind = Step bind

getPrefixTraces :: MonadTrace m => PrefixTrace m v -> [m ()]
getPrefixTraces s = return () : case s of
  Step f s' -> map f (getPrefixTraces s')
  _ -> []

evalByName :: MonadTrace m => Expr -> [m ()]
evalByName = getPrefixTraces . Template.evalByName

evalByNeed :: MonadTrace m => Expr -> [m ()]
evalByNeed = getPrefixTraces . Template.evalByNeed

evalByValue :: MonadTrace m => Expr -> [m ()]
evalByValue = getPrefixTraces . Template.evalByValue
