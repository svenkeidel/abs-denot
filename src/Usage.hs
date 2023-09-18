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

data UsageTrace v = UT Us v
  deriving (Functor)

instance Applicative UsageTrace where
  pure v = UT S.empty v
  UT us1 f <*> UT us2 a = UT (us1 .+. us2) (f a)

instance Monad UsageTrace where
  UT us1 a >>= k = UT (us1 .+. us2) b
    where UT us2 b = k a

--botUsageTrace = UT S.empty

instance MonadTrace UsageTrace where
  stuck = UT S.empty _
  lookup = _
  update = _
  app1 = _
  app2 = _
  bind = _

