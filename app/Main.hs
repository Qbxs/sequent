module Main where

import Prop
import SequentCalculus

main :: IO ()
main = do
  putStrLn $ render example
  print $ valid example
  case proof example of
    Nothing -> return ()
    (Just p) -> putStrLn $ render p
