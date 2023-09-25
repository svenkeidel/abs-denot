{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Later (Later, Tick, löb, unsafeTick) where

data Tick = Tick

type Later = (->) Tick
--  deriving (Functor,Applicative) via Identity
-- An embedding that is more faithful to the Agda encoding would be
-- `Reader () a` (where `()` is the erasure of all tick variable types, which
-- can't be properly type-checked in Haskell).
-- The difference is hardly worth the bother...

löb :: (Later a -> a) -> a
löb f = let x = f (pure x) in x

unsafeTick :: Tick
unsafeTick = Tick
