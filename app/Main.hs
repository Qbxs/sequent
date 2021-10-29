module Main where

import Prop
import Parser
import SequentCalculus

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
  (Right c) -> let (pr,i) = runWriter (satisfiable c)
               in printR c >> if unsatisfiable i
                  then putStrLn "The clause set is unsatisfiable."
                  else putStrLn "The clause set is satisfiable by I with" >> printR i >> printR pr
  -- case parseExpr p of
  --   (Left err) -> print err
  --   (Right e) -> case runWriter $ tauto e of
  --     (pr,True) -> putStrLn (render e <> " is valid.") >> putStrLn (render pr)
  --     (pr,False) -> putStrLn (render e <> " is invalid.") >> putStrLn (render pr)
