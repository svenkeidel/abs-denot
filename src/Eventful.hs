module Eventful where

import Prelude hiding (lookup)

import Expr
import Template
import Control.Monad.Fix

data Evt = Look | Upd | App1 | App2 | Bind

data Eventful a = Delay Evt (Eventful a) | Ret !a | Stuck
  deriving Functor

instance Show Evt where
  show Look = "L"
  show Upd = "U"
  show App1 = "a"
  show App2 = "A"
  show Bind = "B"

instance Show a => Show (Eventful a) where
  show (Delay evt trc) = show evt ++ show trc
  show Stuck = "🗲"
  show (Ret a) = '⟨':show a++"⟩"

instance Applicative Eventful where
  pure = Ret
  Delay e f <*> a = Delay e (f <*> a)
  Stuck <*> _ = Stuck
  f <*> Delay e a = Delay e (f <*> a)
  _ <*> Stuck = Stuck
  Ret f <*> Ret a = Ret (f a)

instance Monad Eventful where
  Stuck >>= _ = Stuck
  Delay e d >>= k = Delay e (d >>= k)
  Ret a >>= k = k a

instance MonadFix Eventful where
  mfix f = trc
    where
      (trc,v) = go (f v)
      go (Delay e t) = (Delay e t', v)
        where
          (t', v) = go t
      go (Ret v) = (Ret v, v)
      go Stuck = (Stuck, undefined)

instance MonadTrace Eventful where
  stuck = Stuck
  lookup _ = Delay Look
  update = Delay Upd
  app1 = Delay App1
  app2 = Delay App2
  bind = Delay Bind


evalByName :: Expr -> Eventful (Value (ByName Eventful))
evalByName = Template.evalByName

evalByNeed :: Expr -> Eventful (Value (ByNeed Eventful), Heap (ByNeed Eventful))
evalByNeed = Template.evalByNeed

evalByValue :: Expr -> Eventful (Value (ByValue Eventful))
evalByValue = Template.evalByValue
