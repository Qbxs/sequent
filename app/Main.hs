module Main where

import Prop
import Parser
import SequentCalculus

import System.Environment
import Control.Monad.Trans.Writer.CPS (runWriter)

main :: IO ()
main = do
  (p:_) <- getArgs
  case parseExpr p of
    (Left err) -> print err
    (Right e) -> case runWriter $ tauto e of
      (pr,True) -> putStrLn (render e <> " is valid.") >> putStrLn (render pr)
      (pr,False) -> putStrLn (render e <> " is invalid.") >> putStrLn (render pr)
