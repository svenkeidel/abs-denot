{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DerivingVia #-}
module Usage where

import Expr
import Template
import qualified Data.Map.Strict as S

-- Challenges:
-- 1. How to communicate the address to lookup?
--    Perhaps pass whole "state"? What does that mean?
--    Perhaps pass entry in env? Yes, can reconstruct address from memo
--    Can probably key the map by denotation of form memo(a,_) and factor through Addr -> L!
--

data U = Z | O | W -- 0 | 1 | ω

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

data UTrace a = Look Name (UTrace a) | Other (UTrace a) | Ret !a | Bot
  deriving Functor

instance Show a => Show (UTrace a) where
  show (Look x trc) = show x ++ show trc
  show (Other trc) = '.':show trc
  show Bot = "🗲"
  show (Ret a) = '⟨':show a++"⟩"

instance Applicative UTrace where
  pure = Ret
  Look x f <*> a = Look x (f <*> a)
  Other f <*> a = Other (f <*> a)
  Bot <*> _ = Bot
  f <*> Other a = Other (f <*> a)
  f <*> Look x a = Look x (f <*> a)
  _ <*> Bot = Bot
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
