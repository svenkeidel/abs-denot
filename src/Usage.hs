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

data U = Z | O | W -- 0 | 1 | ω
  deriving Eq

instance PreOrd U where
  l ⊑ r = l ⊔ r == r

instance Complete U where
  Z ⊔ u = u
  u ⊔ Z = u
  O ⊔ O = O
  _ ⊔ _ = W

instance LowerBounded U where
  bottom = Z

(+#) :: U -> U -> U
O  +# O  = W
u1 +# u2 = u1 ⊔ u2

type Us = S.Map Name U

(.+.) :: Us -> Us -> Us
(.+.) = S.unionWith (+#)

instance {-# OVERLAPPING #-} Show Us where
  show = ($ []) . showList__ (\(k,v) -> (k ++) . ('↦':) . shows v) . S.toList

instance Show U where
  show Z = "0"
  show O = "1"
  show W = "ω"

-----------------------
-- Usg
-----------------------

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

add :: Us -> Name -> Us
add us x = S.alter (\e -> Just $ case e of Just u -> u +# O; Nothing -> O) x us

instance MonadTrace Usg where
  type L Usg = Identity
  lookup x (Identity (Usg us a)) = Usg (add us x) a
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
  injFun f = Usg (evalDeep (f nopD)) Nop
  injCon _ ds = Usg (foldr (.+.) S.empty $ map evalDeep ds) Nop
  apply Nop d = Usg (evalDeep d) Nop
  select Nop fs = Usg (lub $ map (\(k,f) -> evalDeep (f (replicate (conArity k) nopD))) fs) Nop

nopD :: Usg AbsVal
nopD = Usg S.empty Nop

evalDeep :: Usg AbsVal -> Us
evalDeep (Usg us _) = W *# us

(*#) :: U -> Us -> Us
Z *# _  = S.empty
O *# us = us
W *# us = S.map (const W) us

instance PreOrd (Usg AbsVal) where
  l ⊑ r = l ⊔ r == r

instance LowerBounded (Usg AbsVal) where
  bottom = Usg bottom Nop

instance Complete (Usg AbsVal) where
  Usg us1 Nop ⊔ Usg us2 Nop = Usg (us1 ⊔ us2) Nop

instance MonadAlloc Usg AbsVal where
  alloc f = pure $ Identity $ kleeneFix (f . Identity)

kleeneFix :: (Complete l, LowerBounded l) => (l -> l) -> l
kleeneFix f = go (f bottom)
  where
  go l = let l' = f l in if l' ⊑ l then l' else go l'

evalAbsUsg :: Expr -> Usg AbsVal
evalAbsUsg e = eval e S.empty
