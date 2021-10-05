{-# Language TypeOperators #-}

module SequentCalculus (tauto, valid, proof, Proof(..)) where

import Prop

import Data.List (intercalate, intersect)
import qualified Data.Set as S
import Text.PrettyPrint.Boxes hiding (render, (<>))
import qualified Text.PrettyPrint.Boxes as Pretty
import Control.Monad.Trans.Writer.CPS

instance Semigroup Bool where
  (<>) = (&&)
instance Monoid Bool where
  mempty = True

-- used to separate atomic and non atomic Expressions
data Bucket a = Bucket (S.Set a) [a]
 deriving (Show, Eq)

data Sequent = (:=>) (Bucket Expr) (Bucket Expr)
 deriving (Show, Eq)

push :: Expr -> Bucket Expr -> Bucket Expr
push a@(Atom p) (Bucket s l) = Bucket (S.insert a s) l
push p (Bucket s l) = Bucket s (p:l)

instance Render Sequent where
  render ((Bucket s g) :=> (Bucket t d)) = gamma <> " ⊢ " <> delta
                  where gamma = intercalate "," $ render <$> (g <> S.toList s)
                        delta = intercalate "," $ render <$> (d <> S.toList t)

data Proof
  = PeirceL Sequent Proof
  | PeirceR Sequent Proof Proof
  | ConjL Sequent Proof
  | ConjR Sequent Proof Proof
  | DisjL Sequent Proof Proof
  | DisjR Sequent Proof
  | ImplL Sequent Proof Proof
  | ImplR Sequent Proof
  | NegL Sequent Proof
  | NegR Sequent Proof
  | Axiom Sequent
  | Assumption Sequent
 deriving (Show, Eq)

-- helpers
rule :: String -> Box -> Box -> Box
rule str x y = vcat center2 [x, text bar <+> text str, y]
  where bar = replicate (if cols x == 0 then 0 else max 6 (cols x-3)) '—'
renderS :: Sequent -> Box
renderS = text . render

pretty :: Proof -> Box
pretty (PeirceL s pr) = rule "↓l" (pretty pr) (renderS s)
pretty (PeirceR s pr1 pr2) = rule "↓r" (hsep 2 bottom [pretty pr1, pretty pr2]) (renderS s)
pretty (ConjL s pr) = rule "∧l" (pretty pr) (renderS s)
pretty (ConjR s pr1 pr2) = rule "∧r" (hsep 2 bottom [pretty pr1, pretty pr2]) (renderS s)
pretty (DisjL s pr1 pr2) = rule "∨l" (hsep 2 bottom [pretty pr1, pretty pr2]) (renderS s)
pretty (DisjR s pr) = rule "∨r" (pretty pr) (renderS s)
pretty (ImplL s pr1 pr2) = rule "→l" (hsep 2 bottom [pretty pr1, pretty pr2]) (renderS s)
pretty (ImplR s pr) = rule "→r" (pretty pr) (renderS s)
pretty (NegL s pr) = rule "¬l" (pretty pr) (renderS s)
pretty (NegR s pr) = rule "¬r" (pretty pr) (renderS s)
pretty (Axiom s) = rule "" (text "axiom") (renderS s)
pretty (Assumption s) = rule "INVALID" nullBox (renderS s)

instance Render Proof where
  render = Pretty.render . pretty

tauto :: Expr -> Writer Bool Proof
tauto p = proof (Bucket S.empty [] :=> Bucket S.empty [p])

valid :: Sequent -> Bool
-- remove atoms
valid ((Bucket s ((Atom p):g)) :=> d) = valid (Bucket (S.insert (Atom p) s) g :=> d)
valid (g :=> (Bucket s ((Atom p):d))) = valid (g :=> Bucket (S.insert (Atom p) s) d)
-- negation right
valid (g :=> (Bucket s ((Neg p):d))) = valid (push p g :=> Bucket s d)
-- negation left
valid ((Bucket s ((Neg p):g)) :=> d) = valid (Bucket s g :=> push p d)
-- implication right
valid (g :=> (Bucket s ((Impl p q):d))) = valid (push p g :=> push q (Bucket s d))
-- implication left
valid ((Bucket s ((Impl p q):g)) :=> d) = valid (Bucket s g :=> push p d)
                                       && valid (push q (Bucket s g) :=> d)
-- disjunction right
valid (g :=> (Bucket s ((Disj p q):d))) = valid (g :=> push p (push q (Bucket s d)))
-- disjunction left
valid ((Bucket s ((Disj p q):g)) :=> d) = valid (push p (Bucket s g) :=> d)
                                       && valid (push q (Bucket s g) :=> d)
-- conjunction right
valid (g :=> (Bucket s ((Conj p q):d))) = valid (g :=> push p (Bucket s d))
                                       && valid (g :=> push q (Bucket s d))
-- conjunction left
valid ((Bucket s ((Conj p q):g)) :=> d) = valid (push p (push q (Bucket s g)) :=> d)
-- done
valid ((Bucket s []) :=> (Bucket t [])) = not $ S.null $ S.intersection s t


proof :: Sequent -> Writer Bool Proof
proof ((Bucket s ((Atom p):g)) :=> d) = proof (Bucket (S.insert (Atom p) s) g :=> d)
proof (g :=> (Bucket s ((Atom p):d))) = proof (g :=> Bucket (S.insert (Atom p) s) d)
proof e@(g :=> (Bucket s ((Neg p):d))) = do
  pr <- proof (push p g :=> Bucket s d)
  return $ NegR e pr
proof e@((Bucket s ((Neg p):g)) :=> d) = do
  pr <- proof (Bucket s g :=> push p d)
  return $ NegL e pr
proof e@(g :=> (Bucket s ((Impl p q):d))) = do
  pr <- proof (push p g :=> push q (Bucket s d))
  return $ ImplR e pr
proof e@(g :=> (Bucket s ((Disj p q):d))) = do
  pr <- proof (g :=> push p (push q (Bucket s d)))
  return $ DisjR e pr
proof e@((Bucket s ((Conj p q):g)) :=> d) = do
  pr <- proof (push p (push q (Bucket s g)) :=> d)
  return $ ConjL e pr
proof e@((Bucket s (Peirce p q:g)) :=> d) = do
  pr <- proof (Bucket s g :=> push p (push q d))
  return $ PeirceL e pr
proof e@(g :=> (Bucket s (Peirce p q:d))) = do
  pr1 <- proof (push p g :=> Bucket s d)
  pr2 <- proof (push q g :=> Bucket s d)
  return $ PeirceR e pr1 pr2
proof e@((Bucket s ((Disj p q):g)) :=> d) = do
  pr1 <- proof (push p (Bucket s g) :=> d)
  pr2 <- proof (push q (Bucket s g) :=> d)
  return $ DisjL e pr1 pr2
proof e@(g :=> (Bucket s (Conj p q:d))) = do
  pr1 <- proof (g :=> push p (Bucket s d))
  pr2 <- proof (g :=> push q (Bucket s d))
  return $ ConjR e pr1 pr2
proof e@((Bucket s ((Impl p q):g)) :=> d) = do
  pr1 <- proof (Bucket s g :=> push p d)
  pr2 <- proof (push q (Bucket s g) :=> d)
  return $ ImplL e pr1 pr2
proof e@((Bucket s []) :=> (Bucket t [])) = if S.null $ S.intersection s t
                                            then tell False >> return (Assumption e)
                                            else return $ Axiom e

example :: Sequent
example = Bucket S.empty [] :=> Bucket S.empty [Impl (Impl (Conj (Atom 'p') (Atom 'q')) (Atom 'r'))
                                               (Impl (Atom 'p') (Impl (Atom 'q') (Atom 'r')))]
