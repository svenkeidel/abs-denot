{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
module Usage where

import Prelude hiding (lookup)
import Expr
import Template
import Order
import qualified Data.Map.Strict as S
import Data.Coerce
import GHC.Show
import Control.Monad
import Data.Functor.Identity

data U = Zero | One | Omega -- 0 | 1 | ω
  deriving Eq

instance PreOrd U where
  -- Z ⊑ O ⊑ W
  Zero ⊑ _ = True
  _ ⊑ Omega = True
  One ⊑ One = True
  _ ⊑ _ = False

instance Complete U where
  Zero ⊔ u = u
  u ⊔ Zero = u
  One ⊔ One = One
  _ ⊔ _ = Omega

instance LowerBounded U where
  bottom = Zero

instance Show U where
  show Zero = "0"
  show One = "1"
  show Omega = "ω"

(+#) :: U -> U -> U
Zero  +# u     = u
u     +# Zero  = u
Omega +# _     = Omega
_     +# Omega = Omega
One   +# One   = Omega

-- | Usage information for multiple variables.
-- If a variable does not occur, it is a assumed to have a usage of `Zero`.
type Us = S.Map Name U

instance {-# OVERLAPPING #-} Show Us where
  show = ($ []) . showList__ (\(k,v) -> (k ++) . ('↦':) . shows v) . S.toList

-- | Combines usage information per variable point-wise with `+#`.
(.+.) :: Us -> Us -> Us
(.+.) = S.unionWith (+#)

-- | Multiplies usage information for all variables with the given usage.
(*#) :: U -> Us -> Us
Zero  *# _  = S.empty
One   *# us = us
Omega *# us = S.map (const Omega) us

-- | Increments usage for a given variable
increment :: Us -> Name -> Us
increment us x = S.alter (\e -> Just $ case e of Just u -> u +# One; Nothing -> One) x us

-----------------------
-- Usg
-----------------------

-- | Writer monad that accumulates usage information
data Usg a = Usg Us !a
  deriving (Eq,Functor)

instance Show a => Show (Usg a) where
  show (Usg us val) = show us ++ show val

instance Applicative Usg where
  pure a = Usg S.empty a
  (<*>) = ap

instance Monad Usg where
  Usg us1 a >>= k = case k a of
    Usg us2 b -> Usg (us1 .+. us2) b

instance MonadTrace Usg where
  type L Usg = Identity
  lookup x (Identity (Usg us a)) = Usg (increment us x) a
  app1 = id
  app2 = id
  bind = id
  case1 = id
  case2 = id
  update = id
  let_ = id

-- These won't work, because UTrace is an inductive trace type.
-- Use PrefixTrace instead!
--
-- evalByName :: Expr -> Usg (Value (ByName Usg))
-- evalByName = Template.evalByName
--
-- evalByNeed :: Expr -> Usg (Value (ByNeed Usg), Heap (ByNeed Usg))
-- evalByNeed = Template.evalByNeed
--
-- evalByValue :: Expr -> Usg (Value (ByValue Usg))
-- evalByValue = Template.evalByValue

---------------
-- AbsVal
---------------

data AbsVal = Nop
  deriving Eq

instance Show AbsVal where
  show Nop = ""

instance IsValue Usg AbsVal where
  stuck = return Nop
  injFun f = Usg (evalDeep (f zeroUsage)) Nop
  injCon _ ds = Usg (foldr (.+.) S.empty $ map evalDeep ds) Nop
  apply Nop d = Usg (evalDeep d) Nop
  select Nop fs = Usg (lub $ map (\(k,f) -> evalDeep (f (replicate (conArity k) zeroUsage))) fs) Nop

zeroUsage :: Usg AbsVal
zeroUsage = Usg S.empty Nop

-- | Multiplies all usage information by `Omega`
evalDeep :: Usg AbsVal -> Us
evalDeep (Usg us _) = Omega *# us

instance PreOrd (Usg AbsVal) where
  l ⊑ r = l ⊔ r == r

instance LowerBounded (Usg AbsVal) where
  bottom = Usg bottom Nop

instance Complete (Usg AbsVal) where
  Usg us1 Nop ⊔ Usg us2 Nop = Usg (us1 ⊔ us2) Nop

instance MonadAlloc Usg AbsVal where
  alloc f = pure $ Identity $ kleeneFix (f . Identity)

evalAbsUsg :: Expr -> Usg AbsVal
evalAbsUsg e = eval e S.empty
