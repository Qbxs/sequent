{-# LANGUAGE TypeOperators #-}

module SAT
        ( satisfiable
        , unsatisfiable
        ) where

import Prop

import Data.Maybe (isJust)
import Data.List (intercalate, intersect)
import qualified Data.Set as S

satisfiable :: Clause -> Maybe Interpretation
satisfiable = sat . (:=>) S.empty . map (fold Disj Falsum . (toExpr <$>)) . getClauses --unitPropagation

-- | we use single sided sequents here
-- | separate literal and non-literal expressions
data Sequent = (:=>) (S.Set Literal) [Expr]
 deriving (Show, Eq)

instance Render Sequent where
  render ((:=>) s g) = gamma <> " ⊢ "
                  where gamma = intercalate "," $ (render <$> S.toList s) <> (render <$> g)

-- falsifying Interpretation to extract
data Interpretation
  = Interpretation
     { false :: S.Set Literal
     , true :: S.Set Literal
     }

instance Semigroup Interpretation where
  (<>) l r = Interpretation (false l `S.union` false r) (true l `S.union` true r)
instance Monoid Interpretation where
  mempty = Interpretation S.empty S.empty
instance Render Interpretation where
  render i = intercalate ", " $! map (\(Lit x) -> "I(" <> pure x <> ")=t") (S.toList $ true i)
                              <> map (\(Negated x) -> "I(" <> pure x <> ")=f") (S.toList $ false i)

unsatisfiable :: Interpretation -> Bool
unsatisfiable i = null (true i) && null (false i)

-- LK rules with a few assumptions:
-- disjunctions contain either only literals or a literal and another disjunction
-- negations only contain atoms
-- implications do not occur
-- conjunction do not occur
sat :: Sequent -> Maybe Interpretation
-- constants (from simplification)
sat ((:=>) s (Falsum:g)) = Nothing
sat ((:=>) s (Verum:g)) = sat ((:=>) s g)
-- remove literals
sat ((:=>) s ((Atom p):g)) = sat ((:=>) (S.insert (Lit p) s)
                                        (map (simplification p Verum) g))
sat ((:=>) s ((Neg (Atom p)):g)) = sat ((:=>) (S.insert (Negated p) s)
                                              (map (simplification p Falsum) g))
-- double negation elim
sat ((:=>) s ((Neg (Neg p)):g)) = sat ((:=>) s (p:g))
-- disjunction left: implemented as atomic cut
-- like this the tree is explored as a dfs from left to right
sat ((:=>) s ((Disj p q):g)) = let
  p' = sat ((:=>) s (p:q:g))
  q' = sat ((:=>) s (Neg p:q:g))
  in if isJust p' then p' else q'
-- conjunction left
sat ((:=>) s ((Conj p q):g)) = error "conjunction should not occur"
-- implication left
sat ((:=>) s ((Impl p q):g)) = error "unexpected implication"
-- done: only literals remain
sat ((:=>) s []) = let (t,f) = S.partition isPositive s in
                             if S.empty == S.intersection t f
                             then return $! Interpretation
                                             { true = t
                                             , false = f }
                             else Nothing

-- | substitute and simplify after
simplification :: Char -> Expr -> Expr -> Expr
simplification s t = simplify . substitute s t

-- | substitute an expr for an atom (char) in an expression
substitute :: Char -> Expr -> Expr -> Expr
substitute s t (Disj p q) = Disj (substitute s t p) (substitute s t q)
substitute s t (Conj p q) = Conj (substitute s t p) (substitute s t q)
substitute s t (Impl p q) = Impl (substitute s t p) (substitute s t q)
substitute s t (Neg p) = Neg (substitute s t p)
substitute s t (Atom p) = if s == p then t else Atom p
substitute s t Verum = Verum
substitute s t Falsum = Falsum

-- | simplify as much as possible & remove constants
simplify :: Expr -> Expr
-- computation
simplify (Disj p Verum) = Verum
simplify (Disj Verum p) = Verum
simplify (Disj p Falsum) = simplify p
simplify (Disj Falsum p) = simplify p
simplify (Conj p Verum) = simplify p
simplify (Conj Verum p) = simplify p
simplify (Conj p Falsum) = Falsum
simplify (Conj Falsum p) = Falsum
simplify (Impl p Verum) = Verum
simplify (Impl Verum p) = simplify p
simplify (Impl p Falsum) = simplify (Neg p)
simplify (Impl Falsum p) = Verum
simplify (Neg Verum) = Falsum
simplify (Neg Falsum) = Verum
-- confluence (idea here is to simplify again, if the recursive step was productive)
simplify e@(Disj p q) = let simpl = Disj (simplify p) (simplify q) in
                        if e /= simpl then simplify simpl else e
simplify e@(Conj p q) = let simpl = Conj (simplify p) (simplify q) in
                        if e /= simpl then simplify simpl else e
simplify e@(Impl p q) = let simpl = Impl (simplify p) (simplify q) in
                        if e /= simpl then simplify simpl else e
simplify e@(Neg p) = let simpl = Neg (simplify p) in
                     if e /= simpl then simplify simpl else e
simplify (Atom p) = Atom p
simplify Verum = Verum
simplify Falsum = Falsum

-- | convert Literal (from a clause) to be used in a formula
toExpr :: Literal -> Expr
toExpr (Lit p) = Atom p
toExpr (Negated p) = Neg (Atom p)

-- | more 'specific' list fold
fold :: (a -> a -> a) -> a -> [a] -> a
fold alg z [] = z
fold alg _ [x] = x
fold alg z (x:xs) = x `alg` fold alg z xs

-- | for all atomic clauses simplify the clause set
unitPropagation :: Clause -> [[Expr]]
unitPropagation (Clause cs) = (((toExpr <$>) <$> atoms) <>) $!
                              ((simpl . head <$> atoms) <*>) <$> ((toExpr <$>) <$> rest) -- sry for this mess
  where (atoms,rest) = span ((1 ==) . length) cs
        simpl (Lit p) = simplification p Verum
        simpl (Negated p) = simplification p Falsum
