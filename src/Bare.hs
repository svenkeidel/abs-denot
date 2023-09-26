{-# LANGUAGE TypeFamilies #-}
module Bare where

import Prelude hiding (lookup)

import Expr
import Template
import Control.Monad.Fix
import Later
import Data.Functor.Identity

data Bare l a = Delay (l (Bare l a)) | Ret !a | Stuck
  deriving Functor
type LBare = Bare Later
type IBare = Bare Identity

instance Show a => Show (Bare Later a) where
  show (Delay trc) = 'L':show (trc unsafeTick)
  show Stuck = "🗲"
  show (Ret a) = '⟨':show a++"⟩"

instance Show a => Show (Bare Identity a) where
  show (Delay (Identity trc)) = 'L':show trc
  show Stuck = "🗲"
  show (Ret a) = '⟨':show a++"⟩"

instance Functor l => Applicative (Bare l) where
  pure = Ret
  Delay f <*> a = Delay (fmap (<*> a) f)
--  Delay f <*> a = Delay (\α -> (f α) <*> a)
  Stuck <*> _ = Stuck
  f <*> Delay a = Delay (fmap (f <*>) a)
--  f <*> Delay a = Delay (\α -> f <*> a α)
  _ <*> Stuck = Stuck
  Ret f <*> Ret a = Ret (f a)

instance Functor l => Monad (Bare l) where
  Stuck >>= _ = Stuck
  Delay d >>= k = Delay (fmap (>>= k) d)
  Ret a >>= k = k a

-- | This instance is the correct 'mfix' implementation for 'Bare',
-- yet it is not typeable in a Guarded Type Theory.
-- See the remarks in 'MonadAlloc Later CallByValue'.
instance MonadFix LBare where
  mfix f = trc
    where
      (trc,v) = go (f v)
      go (Delay t) = (Delay (pure t'), v)
        where
          -- Passing unsafeTick here bypasses the Later modality!
          -- Without it, we wouldn't be able to access v without a Later.
          (t', v) = go (t unsafeTick)
      go (Ret v) = (Ret v, v)
      go Stuck = (Stuck, undefined)

instance Applicative l => MonadTrace (Bare l) where
  type L (Bare l) = l
  stuck = Stuck
  lookup _ = Delay
  app1 = Delay . pure
  app2 = Delay . pure
  bind = Delay . pure
  case1 = Delay . pure
  case2 = Delay . pure
  update = Delay . pure
  let_ = Delay . pure

instance MonadRecord LBare where
  recordIfJust (Ret Nothing) = Nothing
  recordIfJust (Ret (Just a)) = Just (Ret a)
  recordIfJust Stuck = Just Stuck
  recordIfJust (Delay t) = Delay . pure <$> (recordIfJust (t unsafeTick)) -- wildly unproductive! This is the culprit of Clairvoyant CbV

-- | Primary way to turn a coinductive trace 'LBare' into an inductive trace
-- 'IBare'.
boundT :: Int -> LBare v -> Maybe (IBare v)
boundT 0 _ = Nothing
boundT n (Delay t) = Delay . Identity <$> boundT (n-1) (t unsafeTick)
boundT _ Stuck = Just Stuck
boundT _ (Ret v) = Just (Ret v)

evalByName :: Expr -> LBare (Value (ByName LBare))
evalByName = Template.evalByName

evalByNeed :: Expr -> LBare (Value (ByNeed LBare), Heap (ByNeed LBare))
evalByNeed = Template.evalByNeed

evalByValue :: Expr -> LBare (Value (ByValue LBare))
evalByValue = Template.evalByValue

evalClairvoyant :: Expr -> LBare (Value (Clairvoyant LBare))
evalClairvoyant = Template.evalClairvoyant
