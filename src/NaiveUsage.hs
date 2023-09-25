{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
module NaiveUsage where

import Prelude hiding (lookup)
import Expr
import Template
import Order
import qualified Data.Map.Strict as S
import Data.Coerce
import GHC.Show
import Control.Monad
import Data.Functor.Identity

-- Challenges:
-- 1. How to communicate the address to lookup?
--    Perhaps pass whole "state"? What does that mean?
--    Perhaps pass entry in env? Yes, can reconstruct address from memo
--    Can probably key the map by denotation of form memo(a,_) and factor through Addr -> L!
--

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

data UVal a where
  Bot :: UVal a
  Nop :: UVal (Value UTrace)
  Ret :: !a -> UVal a

data UTrace a = UT Us (UVal a)
  deriving Functor

instance Show a => Show (UVal a) where
  show Bot = "🗲"
  show Nop = "T"
  show (Ret a) = '⟨':show a++"⟩"

instance Show a => Show (UTrace a) where
  show (UT us val) = show us ++ show val

nopD :: D UTrace
nopD = UT S.empty Nop

evalDeep :: D UTrace -> Us
evalDeep (UT us v) = go us v
  where
    go us Bot = us
    go us Nop = us
    go us (Ret (Fun f)) = case f nopD of
      UT us2 v -> go (us .+. us2) v
    go us (Ret (Con _ ds)) =
      foldr (.+.) us $ map evalDeep ds

manyfy :: Us -> Us
manyfy = S.map (const W)

nopFunVal :: Value UTrace
nopFunVal = Fun (\d -> UT (manyfy (evalDeep d)) Nop)

nopConVal :: ConTag -> Value UTrace
nopConVal k = Con k (replicate (conArity k) nopD)

nopVals :: [Value UTrace]
nopVals = nopFunVal : map nopConVal [minBound..maxBound]

instance Functor UVal where
  fmap _ Bot = Bot
  fmap f Nop = fmap f (Ret nopFunVal)
  fmap f (Ret a) = Ret (f a)

instance Applicative UTrace where
  pure a = UT S.empty (Ret a)
  (<*>) = ap

instance Monad UTrace where
  UT us1 Bot >>= _ = UT us1 Bot
  UT us1 Nop >>= k = UT us1 (Ret nopFunVal) >>= k
  UT us1 (Ret a) >>= k = case k a of
    UT us2 b -> UT (us1 .+. us2) b

add :: Us -> Name -> Us
add us x = S.alter (\e -> Just $ case e of Just u -> u +# O; Nothing -> O) x us

instance MonadTrace Identity UTrace where
  stuck = UT S.empty Bot
  lookup x (Identity (UT us a)) = UT (add us x) a
  app1 = id
  app2 = id
  bind = id
  case1 = id
  case2 = id
  update = id
  let_ = id

-- evalByName :: Expr -> UTrace (Value (ByName UTrace))
-- evalByName = Template.evalByName

-- evalByNeed :: Expr -> UTrace (Value (ByNeed UTrace), Heap (ByNeed UTrace))
-- evalByNeed = Template.evalByNeed

-- evalByValue :: Expr -> UTrace (Value (ByValue UTrace))
-- evalByValue = Template.evalByValue


-----------------------
-- UTrace
-----------------------

instance MonadAlloc Identity UTrace where
  alloc f = do
    let us = kleeneFix (\us -> evalDeep (f (Identity (UT us Nop))))
    pure (Identity (UT us Nop))

kleeneFix :: (Complete l, LowerBounded l) => (l -> l) -> l
kleeneFix f = go (f bottom)
  where
  go l = let l' = f l in if l' ⊑ l then l' else go l'

evalUTrace :: Expr -> UTrace (Value UTrace)
evalUTrace e = eval e S.empty
