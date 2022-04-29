module Main where

import Prop
import Parser
import SequentCalculus
import SAT

import System.Environment
import Control.Monad.Trans.Writer.CPS (runWriter)

main :: IO ()
main = do
  args <- getArgs
  mapM_ run args

run :: String -> IO ()
run p = case parseClause p of
  (Left err) -> case parseExpr p of
    (Left err) -> print err
    (Right e) -> let (pr,i) = runWriter (tauto e)
                 in printR i >> printR pr
  (Right c) -> case satisfiable c of
                Nothing -> putStrLn "The clause set is unsatisfiable."
                (Just i) -> putStrLn "The clause set is satisfiable by I with" >> printR i
