{-# LANGUAGE TypeApplications #-}

module PlayPCF where

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
import PCF
import Bare
import System.Timeout

e_1 :: LExpr
e_1 = label $ read "λx.x"

e_2 :: LExpr
e_2 = label $ read "(λx.x) (λy.y)"

e_3 :: LExpr
e_3 = label $ read "(λx. x x) (λy.y)"

e_id :: LExpr
e_id = label $ read "(rec id. λx. if0(x;x;succ (id (pred(x))))) 3"

e_w :: LExpr
e_w = label $ read "(λx.x x) (λy.y y)"

e_w2 :: LExpr
e_w2 = label $ read "rec x. x"

e_loop :: LExpr
e_loop = label $ read "(rec f. λx. f x) 0"

-- e_loop :: LExpr
-- e_loop = label $ read "(rec f. λx. f x) 0"

timeout' :: Int -> IO () -> IO ()
timeout' time m = do
  res <- timeout time m
  case res of
    Nothing -> putStrLn "<timeout>"
    _ -> return ()

main :: IO ()
main = forM_ [e_1, e_2, e_3, e_w, e_w2, e_loop, e_id] $ \e -> do
  putStrLn ""
  putStrLn "------------------------------"
  print e
  print $ Bare.boundT 40 $ PCF.evalConc e
  -- putStrLn "----------------"
  -- putStrLn "     PrefixTrace"
  -- putStrLn "----------------"
  -- print $ PrefixTrace.evalLog PrefixTrace.evalByName 40 e
  -- print $ PrefixTrace.evalLog PrefixTrace.evalByNeed 40 e
  -- print $ PrefixTrace.evalLog PrefixTrace.evalByValue 40 e
  -- print $ PrefixTrace.evalLog PrefixTrace.evalClairvoyant 40 e
  timeout' 10000 $ print $ PCF.eval0CFA e
  timeout' 10000 $ print $ PCF.exec0CFA e
  print $ PCF.eval0CachedCFA e
  print $ PCF.exec0CachedCFA e
  return ()
