{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
module NaiveUsage where

import Prelude hiding (lookup)
import Expr
import Template
import qualified Data.Map.Strict as S
import Data.Coerce

-- Challenges:
-- 1. How to communicate the address to lookup?
--    Perhaps pass whole "state"? What does that mean?
--    Perhaps pass entry in env? Yes, can reconstruct address from memo
--    Can probably key the map by denotation of form memo(a,_) and factor through Addr -> L!
--

data U = Z | O | W -- 0 | 1 | ω
  deriving Eq

(⊔) :: U -> U -> U
Z ⊔ u = u
u ⊔ Z = u
O ⊔ O = O
_ ⊔ _ = W

(+#) :: U -> U -> U
O  +# O  = W
u1 +# u2 = u1 ⊔ u2

type Us = S.Map Name U

(.⊔.) :: Us -> Us -> Us
(.⊔.) = S.unionWith (⊔)

(.+.) :: Us -> Us -> Us
(.+.) = S.unionWith (+#)

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

manyfy :: Us -> Us
manyfy = S.map (const W)

nopVal :: Value UTrace
nopVal = Fun (\d -> UT (manyfy (evalDeep d)) Nop)

instance Functor UVal where
  fmap _ Bot = Bot
  fmap f Nop = fmap f (Ret nopVal)
  fmap f (Ret a) = Ret (f a)

instance Applicative UTrace where
  pure a = UT S.empty (Ret a)
  UT us1 Bot <*> _ = UT us1 Bot
  UT us1 _ <*> UT us2 Bot = UT (us1 .+. us2) Bot
  ut <*> UT us2 Nop = ut <*> UT us2 (Ret nopVal)
  UT us1 (Ret f) <*> UT us2 (Ret a) = UT (us1 .+. us2) (Ret (f a))


instance Monad UTrace where
  UT us1 Bot >>= _ = UT us1 Bot
  UT us1 Nop >>= k = UT us1 (Ret nopVal) >>= k
  UT us1 (Ret a) >>= k = case k a of
    UT us2 b -> UT (us1 .+. us2) b

add :: Us -> Name -> Us
add us x = S.alter (\e -> Just $ case e of Just u -> u +# O; Nothing -> O) x us

instance MonadTrace UTrace where
  stuck = UT S.empty Bot
  lookup x (UT us a) = UT (add us x) a
  update = id
  app1 = id
  app2 = id
  bind = id

evalByName :: Expr -> UTrace (Value (ByName UTrace))
evalByName = Template.evalByName

evalByNeed :: Expr -> UTrace (Value (ByNeed UTrace), Heap (ByNeed UTrace))
evalByNeed = Template.evalByNeed

-- evalByValue :: Expr -> UTrace (Value (ByValue UTrace))
-- evalByValue = Template.evalByValue


-----------------------
-- UTrace
-----------------------

instance MonadAlloc UTrace where
  alloc f = do
    let us = fixIter (\us -> evalDeep (f (UT us Nop)))
    pure (UT us Nop)

(.<=.) :: Us -> Us -> Bool
us1 .<=. us2 = (us1 .⊔. us2) == us2

fixIter :: (Us -> Us) -> Us
fixIter f = go (f S.empty)
  where
  go us = let us' = f us in if us' .<=. us then us' else go us'

evalUTrace :: Expr -> UTrace (Value UTrace)
evalUTrace e = eval e S.empty
