{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE GADTs #-}

module NonDet where

import Control.Monad
import Expr
import NaiveUsage (U(..), Us, (.+.), (+#))
import Order
import Template
import qualified Data.Map.Strict as S

data NonDet t a where
  Many :: ![a] -> NonDet t a
  Symbol :: !(t a) -> NonDet t a

class Symbolic t where
  conc :: t a -> [a]

runNonDet :: Symbolic t => NonDet t a -> [a]
runNonDet (Symbol s) = conc s
runNonDet (Many as) = as

instance Symbolic t => Functor (NonDet t) where
  fmap f n = Many (map f (runNonDet n))

instance Symbolic t => Applicative (NonDet t) where
  pure = Many . pure
  (<*>) = ap

instance Symbolic t => Monad (NonDet t) where
  n >>= k = Many [b  | a <- runNonDet n, b <- runNonDet (k a)]

instance (Show a, forall b. Show (t b)) => Show (NonDet t a) where
  show (Symbol s) = show s
  show (Many as) = '⟨' : showSep (showString ",") (map shows as) "⟩"


--------------------
-- How to use it

data USym a where
  Bot :: USym a
  Nop :: USym (Value UTrace)

instance Symbolic USym where
  conc Bot = []
  conc Nop = nopVals

data UTrace a = UT Us (NonDet USym a)
  deriving Functor

instance Show a => Show (USym a) where
  show Bot = "🗲"
  show Nop = "T"

instance Show a => Show (UTrace a) where
  show (UT us val) = show us ++ show val

nopD :: D UTrace
nopD = UT S.empty (Symbol Nop)

evalDeep :: D UTrace -> Us
evalDeep (UT us (Symbol Bot)) = us
evalDeep (UT us (Symbol Nop)) = us
evalDeep (UT us (Many vs)) = us .+. lub (map one vs)
  where
    one (Fun f) = evalDeep (f nopD)
    one (Con _ ds) = foldr ((.+.) . evalDeep) S.empty ds

manyfy :: Us -> Us
manyfy = S.map (const W)

nopFunVal :: Value UTrace
nopFunVal = Fun (\d -> UT (manyfy (evalDeep d)) (Symbol Nop))

nopConVal :: ConTag -> Value UTrace
nopConVal k = Con k (replicate (conArity k) nopD)

nopVals :: [Value UTrace]
nopVals = nopFunVal : map nopConVal [minBound..maxBound]

instance Applicative UTrace where
  pure a = UT S.empty (pure a)
  (<*>) = ap

instance Monad UTrace where
  UT us1 v >>= k = case lub $ runNonDet $ fmap k v of -- Need lub on Value UTrace
    UT us2 b -> UT (us1 .+. us2) b

add :: Us -> Name -> Us
add us x = S.alter (\e -> Just $ case e of Just u -> u +# O; Nothing -> O) x us

instance MonadTrace UTrace where
  stuck = UT S.empty (Symbol Bot)
  lookup x (UT us a) = UT (add us x) a
  update = id
  app1 = id
  app2 = id
  bind = id
  case1 = id
  case2 = id

