module Main where

import qualified PlaySestoft
import qualified PlayPCF

main :: IO ()
main = do
  PlaySestoft.main
  PlayPCF.main
