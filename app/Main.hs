module Main where

import Prop
import Parser
import SequentCalculus

import System.Environment

main :: IO ()
main = do
  (p:_) <- getArgs
  case parseExpr p of
    (Left err) -> print err
    (Right e) -> case tauto e of
      Nothing -> putStrLn $ "Proof search failed.\n" <> render e <> " is not valid."
      (Just d) -> putStrLn $ render d
