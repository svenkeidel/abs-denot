{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
module Usage where

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

data UTrace a where
  Look :: Name -> UTrace a -> UTrace a
  Other :: UTrace a -> UTrace a
  Ret :: !a -> UTrace a
  Bot :: UTrace a
  Nop :: UTrace (Value UTrace)

instance Show a => Show (UTrace a) where
  show (Look x trc) = show x ++ show trc
  show (Other trc) = '.':show trc
  show Bot = "🗲"
  show Nop = "T"
  show (Ret a) = '⟨':show a++"⟩"

nopVal :: Value UTrace
nopVal = Fun (\d -> d >> d >> Nop)

instance Applicative UTrace where
  pure = Ret
  Look x f <*> a = Look x (f <*> a)
  Other f <*> a = Other (f <*> a)
  Bot <*> _ = Bot
  f <*> Other a = Other (f <*> a)
  f <*> Look x a = Look x (f <*> a)
  _ <*> Bot = Bot
  Nop <*> a = Ret nopVal <*> a
  Ret f <*> Ret a = Ret (f a)

instance Monad UTrace where
  Bot >>= _ = Bot
  Other d >>= k = Other (d >>= k)
  Look x d >>= k = Look x (d >>= k)
  Ret a >>= k = k a

instance MonadTrace UTrace where
  stuck = Bot
  lookup = Look
  update = Other
  app1 = Other
  app2 = Other
  bind = Other

evalByName :: Expr -> UTrace (Value (ByName UTrace))
evalByName = Template.evalByName

evalByNeed :: Expr -> UTrace (Value (ByNeed UTrace), Heap (ByNeed UTrace))
evalByNeed = Template.evalByNeed

-- evalByValue :: Expr -> UTrace (Value (ByValue UTrace))
-- evalByValue = Template.evalByValue


-----------------------
-- Naive
-----------------------

newtype Naive a = Naive { unNaive :: (UTrace a) }
  deriving newtype (Functor,Applicative,Monad)

instance MonadAlloc Naive where
  alloc f =
    pure (nopValN <$ fixIter (\d -> eval_deep (f (nopValN <$ d))))

nopValN :: Value Naive
nopValN = Fun (\d -> d >> d >> nopD)

nopD :: D Naive
nopD = Naive nopValN

eval_deep :: D Naive -> Naive ()
eval_deep (Naive d) = Naive (go d)
  where
    go (Look x d) = Look x (go d)
    go (Other d) = Other (go d)
    go Bot = Bot
    go (Ret (Fun f)) = go (unNaive (f nopD))

getD :: Naive () -> S.Map Name U
getD (Naive d) = go S.empty d
  where
    add us x = S.alter (\e -> Just $ case e of Just u -> u +# O; Nothing -> O) x us
    go us (Look x d) = go (add us x) d
    go us (Other d) = go us d
    go us (Ret _) = us
    go us Bot = us

(.<=.) :: Naive () -> Naive () -> Bool
d .<=. d' = (getD d .⊔. getD d') == getD d'

fixIter :: (Naive () -> Naive ()) -> Naive ()
fixIter f = go (f (Naive Bot))
  where
    go d = let d' = f d in if d' .<=. d then d' else go d'

thingNaive :: (forall v. UTrace v -> UTrace v) -> Naive v -> Naive v
thingNaive f (Naive m) = Naive (f m)

instance MonadTrace Naive where
  stuck = Naive stuck
  lookup x = thingNaive (lookup x)
  update = thingNaive update
  app1 = thingNaive app1
  app2 = thingNaive app2
  bind = thingNaive bind
instance Show (Naive a) where
  show _ = "_"

evalNaive :: Expr -> UTrace (Value Naive)
evalNaive e = unNaive $ eval e S.empty


