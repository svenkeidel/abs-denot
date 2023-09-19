module Play where

import Control.Applicative
import Control.Monad
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Ord
import Data.Set (Set)
import qualified Data.Set as Set
import Debug.Trace
import Expr
import Bare
import Eventful
import NaiveUsage
import System.IO

x, y, z, a, b, c, d, e, f, i, t :: Expr
x : y : z : a : b : c : d : e : f : i : t : _ = map (Var . (: [])) "xyzabcdefit"

e_1 :: Expr
e_1 = Lam "y" y

e_2 :: Expr
e_2 = Let "x" (Lam "y" y) (App x "x")

e_3 :: Expr
e_3 = Let "x" (Lam "y" y) (App (App x "x") "x")

e_bool :: Expr
e_bool = Let "t" (Lam "a" (Lam "b" a)) $
                 Let "f" (Lam "c" (Lam "d" d)) $
                 App (App (App t "f") "t") "t"

e_fresh :: Expr
-- The point here is that each call to id allocates
-- and has to give fresh heap entries for y
e_fresh = read " let id = (λa. let y = a in y) in \
                       \ let z = λc.c in \
                       \ let d = id id in \
                       \ let e = id z in \
                       \ d e d"

e_abs :: Expr
e_abs = read "let id = λx.x in let const = λy.λz.y in const const id"

e_stuck :: Expr
e_stuck = x

e_stuck_app :: Expr
e_stuck_app = read "a a"

e_stuck_let :: Expr
e_stuck_let = read "let a = b in a"

e_w :: Expr
e_w = Let "x" x x

e_w2 :: Expr
e_w2 = Let "x" (App x "x") x

e_W :: Expr
e_W = Let "y" (Lam "x" (App x "x")) (App y "y")

e_usg :: Expr
e_usg = read "let f = λx. let i = λy.y in i x x in f f"

e_usg2 :: Expr
e_usg2 = read "let i = λx.x in let j = λy.y in i j"

e_usg3 :: Expr
e_usg3 = read "let f = λx.f f in f"



--e_bug1 :: Expr
--e_bug1 = uniqify $ read "let a = (λb.let c = a in (let d = λe.a b in let f = let g = a in a in λh.let i = a in d) a) a in (let j = a in a) a"

e_bug2 :: Expr
e_bug2 = read "let a = a in let b = let c = a in a in b"

-- | This is an example where there is no clairvoyant CbV trace of minimal length.
-- It's still theoretically possible to prefer yielding from the trace that drops `i`,
-- but we can never fully commit and thus never have a productive definition.
e_clairvoyant_loop :: Expr
e_clairvoyant_loop = read "let i = λx.x in let ω = λy.y y in ω ω"

main :: IO ()
main = forM_ [e_2, e_3, e_fresh, e_usg, e_usg2, e_usg3, e_clairvoyant_loop] $ \e -> do
  putStrLn ""
  putStrLn "------------------------------"
  print e
--  putStrLn "----------------"
--  putStrLn "     Bare"
--  putStrLn "----------------"
--  print $ Bare.boundT 40 $ Bare.evalByName e
--  print $ Bare.boundT 40 $ Bare.evalByNeed e
--  print $ Bare.boundT 40 $ Bare.evalByValue e
--  print $ Bare.boundT 40 $ Bare.evalClairvoyant e
  putStrLn "----------------"
  putStrLn "     Eventful"
  putStrLn "----------------"
  print $ Eventful.boundT 40 $ Eventful.evalByName e
  print $ Eventful.boundT 40 $ Eventful.evalByNeed e
  print $ Eventful.boundT 40 $ Eventful.evalByValue e
  print $ Eventful.boundT 40 $ Eventful.evalClairvoyant e
--  putStrLn "----------------"
--  putStrLn "    UTrace"
--  putStrLn "----------------"
--  print $ Usage.evalByName e
--  print $ Usage.evalByNeed e
  putStrLn "----------------"
  putStrLn "    Naive"
  putStrLn "----------------"
  print $ NaiveUsage.evalUTrace e
  return ()
