import Prop
import SAT

import Data.List ((!!))
import System.CPUTime

-- | Benchmarks for up to 15 variables (2^15 clauses)
-- up to ~12 is feasible, more clauses lead to runtime of several seconds
main :: IO ()
main = mapM_ go [1..15]
  where go n = do
                putStrLn $! "n=" <> show n
                let c = (\(Clause cl) -> Clause $! tail cl) $! generate n
                t <- getCPUTime
                case satisfiable c of
                  Nothing -> do
                    t' <- getCPUTime
                    putStrLn $! "unsatisfiable"
                    putStrLn $! "time used: " <> show ((fromInteger t'- fromInteger t)/1000000000000)
                  (Just i) -> do
                    t' <- getCPUTime
                    printR i
                    putStrLn $! "time used: " <> show ((fromInteger t'- fromInteger t)/1000000000000)

generate :: Int -> Clause
generate n' = Clause $! go n'
  where go 1 = [[Lit 'a'],[Negated 'a']]
        go n = let c = ['a'..] !! (n-1) in
               [\x -> [Lit c] <> x, \x -> [Negated c] <> x] <*> go (n-1)
