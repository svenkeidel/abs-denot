{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedRecordDot #-}

module PCF where

import Prelude hiding (lookup, succ, pred)
import Data.Kind
import Numeric.Natural
import qualified Data.Map.Strict as Map
import qualified Data.Map.Lazy as LMap
import Later
import Bare
import Data.Functor.Identity
import Control.Monad.Trans.State
import GHC.Read
import qualified Text.Read as Read
import Data.Char
import qualified Text.ParserCombinators.ReadP as ReadP
import Control.Monad
import Text.Read.Lex
import qualified Data.Set as Set
import Order
import Data.List (foldl')
import Control.Monad.Trans.Class
import Debug.Trace

type Name = String
type Label = Int

data ExprF r
  = Var Name
  | Lam Name r
  | App r r
  | Y Name r
  | Zero
  | Succ r
  | Pred r
  | IfZero r r r
  deriving (Show, Functor)

newtype Expr = Expr (ExprF Expr)

appPrec, lamPrec :: Read.Prec
lamPrec = Read.minPrec
appPrec = lamPrec+1

-- | Example output: @F (λa. G) (H I) (λb. J b)@
instance Show Expr where
  showsPrec _ (Expr (Var v))      = showString v
  showsPrec p (Expr (App f arg))  = showParen (p > appPrec) $
    showsPrec appPrec f . showString " " . showsPrec appPrec arg
  showsPrec p (Expr (Lam b body)) = showParen (p > lamPrec) $
    showString "λ" . showString b . showString ". " . showsPrec lamPrec body
  showsPrec p (Expr (Y x e)) = showParen (p > lamPrec) $
    showString "rec " . showString x
    . showString ". " . showsPrec lamPrec e
  showsPrec _ (Expr Zero) = showString "0"
  showsPrec _ (Expr (Succ e)) = showString "succ(" . showsPrec lamPrec e . showString ")"
  showsPrec _ (Expr (Pred e)) = showString "pred(" . showsPrec lamPrec e . showString ")"
  showsPrec p (Expr (IfZero c t e)) = showParen (p > lamPrec) $
    showString "if0(" .
    showsPrec lamPrec c . showString "; " .
    showsPrec lamPrec t . showString "; " .
    showsPrec lamPrec e . showString ")"

-- | The default 'ReadP.many1' function leads to ambiguity. What a terrible API.
greedyMany, greedyMany1 :: ReadP.ReadP a -> ReadP.ReadP [a]
greedyMany p  = greedyMany1 p ReadP.<++ pure []
greedyMany1 p = (:) <$> p <*> greedyMany p

-- | This monster parses Exprs in the REPL etc. It parses names that start
-- with an upper-case letter as literals and lower-case names as variables.
--
-- Accepts syntax like
-- @let x = λa. g z in (λb. j b) x@
--
-- >>> read "g z" :: Expr
-- g z
--
-- >>> read "λx.x" :: Expr
-- λx. x
--
-- >>> read "λ x . rec y . x y" :: Expr
-- λx. rec y. x y
--
-- >>> read "f (if0 ( 0 ; succ( 0 ); pred( 0 ) ))" :: Expr
-- f (if0(0; succ(0); pred(0)))
--
-- >>> read "(if0 ( 0 ; succ( 0 ); pred( 0 ) )) a" :: Expr
-- (if0(0; succ(0); pred(0))) a
instance Read Expr where
  readPrec = Read.parens $ Read.choice
    [ Expr . Var <$> readName
    , Read.prec appPrec $ do
        -- Urgh. Just ignore the code here as long as it works
        let spaces1 = greedyMany1 (ReadP.satisfy isSpace)
        (f:args) <- Read.readP_to_Prec $ \prec ->
          ReadP.sepBy1 (Read.readPrec_to_P Read.readPrec (prec+1)) spaces1
        guard $ not $ null args
        pure (foldl' (\l r -> Expr (App l r)) f args)
    , Read.prec lamPrec $ do
        c <- Read.get
        guard (c `elem` "λΛ@#%\\") -- multiple short-hands for Lam
        Expr (Var v) <- Read.readPrec
        Read.Symbol "." <- Read.lexP
        Expr . Lam v <$> Read.readPrec
    , Read.prec lamPrec $ do
        Read.Ident "rec" <- Read.lexP
        x <- readName
        Read.Symbol "." <- Read.lexP
        e <- Read.readPrec
        pure (Expr (Y x e))
    , do
        Read.Number n <- Read.lexP
        Just m <- pure (numberToInteger n)
        guard $ m >= 0
        pure (iterate (Expr . Succ) (Expr Zero) !! fromIntegral m)
    , Read.prec appPrec $ do
        Read.Ident "succ" <- Read.lexP
        Read.Punc "(" <- Read.lexP
        e <- Read.readPrec
        Read.Punc ")" <- Read.lexP
        pure (Expr (Succ e))
    , Read.prec appPrec $ do
        Read.Ident "pred" <- Read.lexP
        Read.Punc "(" <- Read.lexP
        e <- Read.readPrec
        Read.Punc ")" <- Read.lexP
        pure (Expr (Pred e))
    , Read.prec appPrec $ do
        Read.Ident "if0" <- Read.lexP
        Read.Punc "(" <- Read.lexP
        c <- Read.readPrec
        Read.Punc ";" <- Read.lexP
        t <- Read.readPrec
        Read.Punc ";" <- Read.lexP
        e <- Read.readPrec
        Read.Punc ")" <- Read.lexP
        pure (Expr (IfZero c t e))
    ]
    where
      readName = do
        Read.Ident v <- Read.lexP
        guard (not $ v `elem` ["let","in", "succ", "pred", "if0", "rec"])
        guard (all isAlphaNum v)
        pure v

data LExpr = LExpr { lbl :: Label, expr :: ExprF LExpr }

showLbl :: Label -> ShowS
showLbl lbl = shows lbl . showString "@"
instance Show LExpr where
  showsPrec _ (LExpr l (Var v))      = showLbl l . showString v
  showsPrec _ (LExpr l (App f arg))  =
    showLbl l . showParen True (showsPrec appPrec f . showString " " . showsPrec appPrec arg)
  showsPrec _ (LExpr l (Lam b body)) =
    showLbl l . showParen True (showString "λ" . showString b . showString ". " . showsPrec lamPrec body)
  showsPrec _ (LExpr l (Y x e)) =
    showLbl l . showParen True (showString "rec " . showString x . showString ". " . showsPrec lamPrec e)
  showsPrec _ (LExpr _ Zero) = showString "0"
  showsPrec _ (LExpr _ (Succ e)) = showString "succ(" . showsPrec lamPrec e . showString ")"
  showsPrec _ (LExpr _ (Pred e)) = showString "pred(" . showsPrec lamPrec e . showString ")"
  showsPrec p (LExpr _ (IfZero c t e)) = showParen (p > lamPrec) $
    showString "if0(" .
    showsPrec lamPrec c . showString "; " .
    showsPrec lamPrec t . showString "; " .
    showsPrec lamPrec e . showString ")"

label :: Expr -> LExpr
label e = evalState (lab e) 1
  where
    next :: State Label Label
    next = state (\(!l) -> (l, l + 1))
    lab :: Expr -> State Label LExpr
    lab (Expr e) = do
      lbl <- next
      le <- case e of
        Var n -> pure (Var n)
        Lam n e -> Lam n <$> lab e
        App f a ->
          App <$> lab f <*> lab a
        Y n e -> Y n <$> lab e
        Zero -> pure Zero
        Succ e -> Succ <$> lab e
        Pred e -> Pred <$> lab e
        IfZero c t e -> IfZero <$> lab c <*> lab t <*> lab e
      pure LExpr {lbl = lbl, expr = le}

unlabel :: LExpr -> Expr
unlabel (LExpr _ e) = Expr (fmap unlabel e)

type Env = Map.Map Name

class (Functor (L m), Monad m) => MonadTrace m where
  type L m :: Type -> Type
  unroll :: L m (m v) -> m v
  lookup :: Label -> m v -> m v
  app1 :: m v -> m v
  app2 :: m v -> m v
  app3 :: m v -> m v

class Monad m => IsValue m v where
  stuck :: m v
  zero :: m v
  succ :: v -> m v
  pred :: v -> m v
  ifZero :: v -> m v -> m v -> m v
  injFun :: Label -> (m v -> m v) -> m v
  apply :: Label -> v -> m v -> m v

class (MonadTrace m) => MonadAlloc m v where
  alloc :: (L m (m v) -> m v) -> m (L m (m v))

-- | The type of coinductive traces, in the sense that @MonadCoindTrace m => m@
-- denotes a potentially infinite program trace.
type MonadCoindTrace m = (MonadTrace m, L m ~ Later)
-- | The type of inductive traces, in the sense that @MonadIndTrace m => m@
-- denotes a finite program trace.
type MonadIndTrace m = (MonadTrace m, L m ~ Identity)

eval :: forall m v. (MonadTrace m, IsValue m v, MonadAlloc m v) => LExpr -> Env (m v) -> m v
eval e env = case e.expr of
  Var x -> lookup e.lbl (Map.findWithDefault stuck x env)
  App f a -> do
    vf <- app1 (eval f env)
    va <- app2 (eval a env) -- TODO: transitions??
--    d <- lookup <$> alloc (\_ld -> return va)
    apply e.lbl vf (return va)
  Lam x body -> injFun e.lbl (\d -> app3 (eval body (Map.insert x d env)))
  Y x f -> do
    ld <- alloc (\ld -> eval f (Map.insert x (unroll ld) env))
    unroll ld
  Zero -> zero
  Succ e -> eval e env >>= succ
  Pred e -> eval e env >>= pred
  IfZero c t e -> eval c env >>= \v -> ifZero v (eval t env) (eval e env)

type D m = m (Value m)
data Value m = Stuck | Lit Natural | Fun (D m -> D m)

instance Show (Value m) where
  show (Fun _) = "λ"
  show (Lit n) = show n
  show Stuck = "🗲"

instance MonadTrace m => IsValue m (Value m) where
  stuck = return Stuck
  zero = return (Lit 0)
  succ (Lit n) = return (Lit (n+1))
  succ _       = stuck
  pred (Lit 0) = return (Lit 0)
  pred (Lit n) = return (Lit (n-1))
  pred _       = stuck
  ifZero (Lit 0) t _ = t
  ifZero (Lit _) _ e = e
  ifZero _       _ _ = stuck
  injFun _ = return . Fun
  apply _ (Fun f) d = f d
  apply _ _       _ = stuck

------------------------
-- Bare adjustments
------------------------
instance Applicative l => MonadTrace (Bare l) where
  type L (Bare l) = l
  unroll = Delay
  lookup _ = Delay . pure
  app1 = Delay . pure
  app2 = Delay . pure
  app3 = Delay . pure

-----------------------
-- Concrete semantics
-----------------------
newtype Concrete m a = Concrete { unConcrete :: (m a) }
  deriving newtype (Functor,Applicative,Monad)

liftConc :: (forall a. m a -> m a) -> Concrete m a -> Concrete m a
liftConc f (Concrete m) = Concrete (f m)

liftConcL :: Functor l => (l (m v) -> m v) -> l (Concrete m v) -> Concrete m v
liftConcL f = Concrete . f . fmap unConcrete

instance MonadCoindTrace m => MonadTrace (Concrete m) where
  type L (Concrete m) = Later
  unroll = liftConcL unroll
  lookup l = liftConc (lookup l)
  app1 = liftConc app1
  app2 = liftConc app2
  app3 = liftConc app3

instance (MonadCoindTrace m) => MonadAlloc (Concrete m) (Value (Concrete m)) where
  alloc f = pure (\_α -> löb f)

instance Show (Concrete m a) where
  show _ = "_"

evalConc :: MonadCoindTrace m => LExpr -> m (Value (Concrete m))
evalConc e = unConcrete $ eval e Map.empty

--------------------
-- 0CFA
--------------------
newtype AllEqual a = AE a
  deriving Show
instance Eq (AllEqual a) where _ == _ = True
instance Ord (AllEqual a) where compare _ _ = EQ

type AbsD = CFA (Pow SynVal)
data SynVal = SomeLit | SomeLam Label (AllEqual (AbsD -> AbsD))
  deriving (Eq, Ord)
instance Show SynVal where
  show SomeLit = "N"
  show (SomeLam l _) = show l

newtype Pow a = Pow { unPow :: Set.Set a }
  deriving (Eq, Ord)
showSep :: ShowS -> [ShowS] -> ShowS
showSep _   [] = id
showSep _   [s] = s
showSep sep (s:ss) = s . sep . showString " " . showSep sep ss
instance Show a => Show (Pow a) where
  showsPrec _ (Pow s) =
    showString "{" . showSep (showString ", ") (map shows (Set.toList s)) . showString "}"
instance Ord a => PreOrd (Pow a) where
  l ⊑ r = l ⊔ r == r
instance Ord a => LowerBounded (Pow a) where
  bottom = Pow Set.empty
instance Ord a => Complete (Pow a) where
  Pow l ⊔ Pow r = Pow (Set.union l r)

type Calls = Map.Map Label (Pow SynVal) -- Application site label :-> Potential labels of lambdas applied

data CFA a = CFA Calls a
  deriving (Eq, Ord, Functor)
instance Show a => Show (CFA a) where
  show (CFA calls a) = show calls ++ show a
instance PreOrd a => PreOrd (CFA a) where
  CFA l1 l2 ⊑ CFA r1 r2 = l1 ⊑ r1 && l2 ⊑ r2
instance LowerBounded a => LowerBounded (CFA a) where
  bottom = CFA bottom bottom
instance Complete a => Complete (CFA a) where
  CFA l1 l2 ⊔ CFA r1 r2 = CFA (l1 ⊔ r1) (l2 ⊔ r2)

instance Applicative CFA where
  pure = CFA Map.empty
  (<*>) = ap
instance Monad CFA where
  CFA c1 a >>= k = case k a of
    CFA c2 b -> CFA (c1 ⊔ c2) b
instance MonadTrace CFA where
  type L CFA = Identity
  unroll (Identity m) = m
  lookup _ = id
  app1 = id
  app2 = id
  app3 = id

addCall :: Label -> Pow SynVal -> CFA ()
addCall app_lbl head_lams =
  CFA (Map.singleton app_lbl head_lams) ()

instance IsValue CFA (Pow SynVal) where
  stuck = return $ Pow Set.empty
  zero = return $ Pow (Set.singleton SomeLit)
  succ _ = return $ Pow (Set.singleton SomeLit)
  pred _ = return $ Pow (Set.singleton SomeLit)
  ifZero _ t e = (⊔) <$> t <*> e
  injFun l f = do
    return (Pow (Set.singleton (SomeLam l (AE f))))
  apply l head_lams arg = do
    addCall l head_lams
    let do_one SomeLit = stuck
        do_one (SomeLam _l (AE f)) = f arg
    vs <- traverse do_one (Set.toList (unPow head_lams))
    return (lub vs)

----------------------
-- Caching
----------------------

data FunCache a b = FC (LMap.Map a b) (FunCache a b -> a -> b)
instance (Eq a, Eq b) => Eq (FunCache a b) where
  FC l _ == FC r _ = l == r
instance (Ord a, Ord b) => Ord (FunCache a b) where
  compare (FC l _) (FC r _) = compare l r
instance (Ord a, PreOrd b) => PreOrd (FunCache a b) where
  FC l _ ⊑ FC r _ = l ⊑ r
instance (Ord a, LowerBounded b) => LowerBounded (FunCache a b) where
  bottom = FC LMap.empty (const bottom)
instance (Ord a, Complete b) => Complete (FunCache a b) where
  FC l1 l2 ⊔ FC r1 r2 =
    -- naive recaching: recompute all cached points with new_fun
    -- Thanks to laziness, this isn't too naive, actually
    let new_fun   = l2 ⊔ r2
        old_cache = l1 ⊔ r1
        old_fc    = FC old_cache new_fun -- might be out of date
        new_cache = LMap.mapWithKey (\a _ -> new_fun old_fc a) old_cache
    in FC new_cache new_fun

applyFunCache :: Ord a => FunCache a b -> a -> (FunCache a b, b)
applyFunCache fc@(FC cache fun) a = case LMap.lookup a cache of
  Just b  -> (fc, b)
  Nothing ->
    let b = fun fc a
        fc' = FC (LMap.insert a b cache) fun
    in (fc', b)

type Lams = Map.Map Label (FunCache AbsD AbsD) -- Lam label :-> join of all activations of the lambda (memoised and comparable)
newtype CachedCFA a = CCFA { unCached :: StateT Lams CFA a }
  deriving (Functor, Applicative, Monad)

instance MonadAlloc CFA (Pow SynVal) where
  alloc f = pure $ Identity $ kleeneFix (f . Identity)

addFun :: Label -> (CachedCFA (Pow SynVal) -> CachedCFA (Pow SynVal)) -> CachedCFA ()
addFun l f = CCFA $ do
  lams <- get
  let
    f' :: FunCache AbsD AbsD -> AbsD -> AbsD
    f' fc a = evalStateT (unCached (f (CCFA (lift a)))) (Map.insert l fc lams)
  modify (Map.insertWith (⊔) l (FC bottom f'))

instance MonadTrace CachedCFA where
  type L CachedCFA = Identity
  unroll (Identity m) = m
  lookup _ = id
  app1 = id
  app2 = id
  app3 = id

callWithCache :: Label -> CachedCFA (Pow SynVal) -> CachedCFA (Pow SynVal)
callWithCache l (CCFA d) = CCFA $ StateT $ \lams ->
  let cache = Map.findWithDefault bottom l lams in
  case applyFunCache cache (evalStateT d lams) of
    (cache', res) -> do
      v <- res
      return (v, Map.insert l cache' lams)

liftCached :: CFA a -> CachedCFA a
liftCached = CCFA . lift

instance IsValue CachedCFA (Pow SynVal) where
  stuck = liftCached stuck
  zero = liftCached zero
  succ = liftCached . succ
  pred = liftCached . pred
  ifZero _ t e = (⊔) <$> t <*> e -- same impl, but more caching
  injFun l f = do
    addFun l f
    liftCached $ injFun l (runCached . f . liftCached)
  apply l head_lams arg = do
    liftCached $ addCall l head_lams
    let do_one SomeLit = stuck
        do_one (SomeLam l _f) = callWithCache l arg
    vs <- traverse do_one (Set.toList (unPow head_lams))
    return (lub vs)

instance MonadAlloc CachedCFA (Pow SynVal) where
  alloc f = CCFA $ do
    let wrap = Identity . CCFA
    pure $ wrap $ kleeneFix $ \(lams :: Lams, d :: CFA (Pow SynVal)) ->
      let CFA calls (lams',d') = runStateT (unCached (f (wrap (lift d)))) lams in
      traceM ("iter " ++ show d ++ "  " ++ show d')
      (lams',CFA )

runCached :: CachedCFA a -> CFA a
runCached (CCFA s) = evalStateT s Map.empty

execCFA :: CFA (Pow SynVal) -> Calls
execCFA (CFA m _) = m

evalCFA :: CFA (Pow SynVal) -> Pow SynVal
evalCFA (CFA _ a) = a

execCCFA :: CachedCFA (Pow SynVal) -> Calls
execCCFA = execCFA . runCached

evalCCFA :: CachedCFA (Pow SynVal) -> Pow SynVal
evalCCFA = evalCFA . runCached

exec0CFA :: LExpr -> Calls
exec0CFA e = execCFA $ eval e Map.empty

eval0CFA :: LExpr -> Pow SynVal
eval0CFA e = evalCFA $ eval e Map.empty

exec0CachedCFA :: LExpr -> Calls
exec0CachedCFA e = execCCFA $ eval e Map.empty

eval0CachedCFA :: LExpr -> Pow SynVal
eval0CachedCFA e = evalCCFA $ eval e Map.empty
