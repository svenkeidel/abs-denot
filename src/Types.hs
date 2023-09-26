{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
module Types where

import Prelude hiding (lookup)
import Expr
import Template
import Order
import qualified Data.Map.Strict as S
import Data.Functor.Identity
import Control.Monad.Trans.RWS
import Debug.Trace
import Control.Monad
import qualified Data.List as List

data TyCon = BoolTyCon | OptionTyCon | PairTyCon
  deriving Eq

instance Show TyCon where
  show BoolTyCon = "bool"
  show OptionTyCon = "option"
  show PairTyCon = "×"

type PolyType = ([Name], Type) -- ρ ::= ∀xs. τ

data Type -- τ ::= x | T | τ -> τ   + Top element
  = FunTy Type Type
  | TyConAppTy TyCon [Type]
  | TyVarTy Name
  | Wrong
  deriving Eq

instance Show Type where
  showsPrec _ (TyConAppTy k tys) = showsPrec 0 k . foldr (\t s -> showString " " . showsPrec 1 t . s) id tys
  showsPrec _ (TyVarTy x) = showString x
  showsPrec _ Wrong       = showString "Wrong"
  showsPrec p (FunTy l r) =
    showParen (p > 0) $ showsPrec 1 l . showString "->" . showsPrec 0 r

pattern (:->:) :: Type -> Type -> Type
pattern l :->: r = FunTy l r
infixr 7 :->:

conTagTy :: ConTag -> PolyType
conTagTy T = ([], TyConAppTy BoolTyCon [])
conTagTy F = ([], TyConAppTy BoolTyCon [])
conTagTy None = (["a_none"], TyConAppTy OptionTyCon [TyVarTy "a_none"])
conTagTy Some = (["a_some"], TyVarTy "a_some" :->: TyConAppTy OptionTyCon [TyVarTy "a_some"])
conTagTy Pair = (["a_pair", "b_pair"],
  TyVarTy "a_pair" :->: TyVarTy "b_pair" :->: TyConAppTy PairTyCon [TyVarTy "a_pair", TyVarTy "b_pair"])

tyConTags :: TyCon -> [ConTag]
tyConTags tc =
  [ k | k <- [minBound..maxBound]
      , TyConAppTy tc' _ <- pure $ snd $ splitFunTys $ snd (conTagTy k)
      , tc == tc' ]

substTy :: Name -> Type -> Type -> Type
substTy x t ty@(TyVarTy y)
  | x == y    = t
  | otherwise = ty
substTy x t (FunTy a r) =
  FunTy (substTy x t a) (substTy x t r)
substTy x t (TyConAppTy k tys) =
  TyConAppTy k (map (substTy x t) tys)
substTy _ _ ty = ty

-----------------------
-- Cts
-----------------------

type Ct = (Type, Type)

type Subst = S.Map Name Type

applySubst :: Subst -> Type -> Type
applySubst subst ty = foldr (uncurry substTy) ty (S.assocs subst)

applySubstCts :: Subst -> [Ct] -> [Ct]
applySubstCts subst = map (\(l,r) -> (applySubst subst l, applySubst subst r))

unify :: [Ct] -> Maybe Subst
unify = go S.empty
  where
    occurs x ty = substTy x ty ty /= ty -- quick and dirty
    go subst [] = Just subst
    go subst ((l,r):cts) = case (l,r) of
      (TyVarTy x, ty)
        | not (occurs x ty)
        , let subst' = S.insert x ty subst
        -> go subst' (applySubstCts subst' cts)
      (_, TyVarTy _) -> go subst ((r,l):cts)
      (FunTy a1 r1, FunTy a2 r2) -> go subst ((a1,a2):(r1,r2):cts)
      (Wrong, Wrong) -> go subst cts
      (TyConAppTy k1 tys1, TyConAppTy k2 tys2) | k1 == k2 -> go subst (zip tys1 tys2 ++ cts)
      _ -> Nothing

newtype Cts a = Cts { unCts :: RWS () [Ct] [Name] a }
  deriving newtype (Functor,Applicative,Monad)

fresh :: Cts Name
fresh = Cts $ state $ \ns ->
  let n = "α" ++ show (length ns)
  in (n,n:ns)

runCts :: Cts Type -> Type
runCts (Cts rws) = case runRWS rws () [] of
  (ty,_names,cts)
    | Just subst <- unify cts
    -> applySubst subst ty
  _ -> Wrong

instance Show a => Show (Cts a) where
  show (Cts rws) = case runRWS rws () [] of
    (a,_names,cts) -> show cts ++ "=>" ++ show a

instance MonadTrace Cts where
  type L Cts = Identity
  lookup x (Identity cts) = cts
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
-- evalByName :: Expr -> Cts (Value (ByName Cts))
-- evalByName = Template.evalByName
--
-- evalByNeed :: Expr -> Cts (Value (ByNeed Cts), Heap (ByNeed Cts))
-- evalByNeed = Template.evalByNeed
--
-- evalByValue :: Expr -> Cts (Value (ByValue Cts))
-- evalByValue = Template.evalByValue

---------------
-- Type
---------------

emit :: Ct -> Cts ()
emit ct = Cts (tell [ct])

freshTyVarTy :: Cts Type
freshTyVarTy = TyVarTy <$> fresh

freshenVars :: [Name] -> Cts [(Name,Type)]
freshenVars = traverse $ \alpha -> do
  beta <- freshTyVarTy
  pure (alpha, beta)

instantiateCon :: ConTag -> Cts Type
instantiateCon k = do
  let (alphas, ty) = conTagTy k
  subst <- freshenVars alphas
  return (foldr (uncurry substTy) ty subst)

splitFunTys :: Type -> ([Type], Type)
splitFunTys ty = go [] ty
  where
    go as (FunTy a r) = go (a:as) r
    go as ty = (reverse as, ty)

enumerateCons :: TyCon -> [Type] -> Cts [(ConTag,[Cts Type])]
enumerateCons tc tc_arg_tys = forM (tyConTags tc) $ \k -> do
  ty <- instantiateCon k
  let (field_tys,res_ty) = splitFunTys ty
  emit (TyConAppTy tc tc_arg_tys, res_ty)
  return (k, map pure field_tys)

instance IsValue Cts Type where
  stuck = return Wrong
  injFun f = do
    arg <- freshTyVarTy
    res <- f (return arg)
    return (FunTy arg res)
  injCon k ds = do
    con_app_ty <- instantiateCon k
    arg_tys <- sequence ds
    res_ty <- freshTyVarTy
    emit (con_app_ty, foldr FunTy res_ty arg_tys)
    return res_ty
  apply ty d = do
    arg_ty <- d
    res_ty <- freshTyVarTy
    emit (ty, FunTy arg_ty res_ty)
    return res_ty
  select _  [] = stuck
  select ty fs@((k,_):_) = do
    res_ty <- snd . splitFunTys <$> instantiateCon k
    let TyConAppTy tc tc_args = res_ty
    emit (ty, res_ty)
    ks_tys <- enumerateCons tc tc_args
    tys <- forM ks_tys $ \(k,tys) ->
      case List.find (\(k',_) -> k' == k) fs of
        Just (_,f) -> f tys
        _          -> stuck
    let ty:tys' = tys
    traverse (\ty' -> emit (ty,ty')) tys' >> return ty

instance MonadAlloc Cts Type where
  alloc f = do
    f_ty <- freshTyVarTy
    f_ty' <- f (Identity (return f_ty))
    emit (f_ty,f_ty')
    pure $ Identity $ return f_ty

inferType :: Expr -> Type
inferType e = runCts $ eval e S.empty
