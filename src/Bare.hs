module Bare where

import Prelude hiding (lookup)

import Expr
import Template
import Control.Monad.Fix

data Bare a = Delay (Bare a) | Ret !a | Stuck
  deriving Functor

instance Show a => Show (Bare a) where
  show (Delay trc) = 'L':show trc
  show Stuck = "🗲"
  show (Ret a) = '⟨':show a++"⟩"

instance Applicative Bare where
  pure = Ret
  Delay f <*> a = Delay (f <*> a)
  Stuck <*> _ = Stuck
  f <*> Delay a = Delay (f <*> a)
  _ <*> Stuck = Stuck
  Ret f <*> Ret a = Ret (f a)

instance Monad Bare where
  Stuck >>= _ = Stuck
  Delay d >>= k = Delay (d >>= k)
  Ret a >>= k = k a

instance MonadFix Bare where
  mfix f = trc
    where
      (trc,v) = go (f v)
      go (Delay t) = (Delay t', v)
        where
          (t', v) = go t
      go (Ret v) = (Ret v, v)
      go Stuck = (Stuck, undefined)

instance MonadTrace Bare where
  stuck = Stuck
  lookup _ = Delay
  update = Delay
  app1 = Delay
  app2 = Delay
  bind = Delay
  case1 = Delay
  case2 = Delay

instance MonadRecord Bare where
  recordIfJust (Ret Nothing) = Nothing
  recordIfJust (Ret (Just a)) = Just (Ret a)
  recordIfJust Stuck = Just Stuck
  recordIfJust (Delay t) = Delay <$> recordIfJust t


boundT :: Int -> Bare v -> Maybe (Bare v)
boundT 0 _ = Nothing
boundT n (Delay t) = Delay <$> boundT (n-1) t
boundT _ t = Just t

evalByName :: Expr -> Bare (Value (ByName Bare))
evalByName = Template.evalByName

evalByNeed :: Expr -> Bare (Value (ByNeed Bare), Heap (ByNeed Bare))
evalByNeed = Template.evalByNeed

evalByValue :: Expr -> Bare (Value (ByValue Bare))
evalByValue = Template.evalByValue

evalClairvoyant :: Expr -> Bare (Value (Clairvoyant Bare))
evalClairvoyant = Template.evalClairvoyant
