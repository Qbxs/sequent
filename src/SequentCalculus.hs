{-# Language TypeOperators #-}

module SequentCalculus where

import Prop

import Data.List (intercalate, intersect)
import Text.PrettyPrint hiding (render, (<>))
import qualified Text.PrettyPrint as P (render)


data Sequent = (:=>) [Expr] [Expr]
 deriving (Show, Eq)

instance Render Sequent where
  render (g :=> d) = gamma <> " ⊢ " <> delta
                  where gamma = intercalate "," $ render <$> g
                        delta = intercalate "," $ render <$> d

data Proof
  = ConjL Sequent Proof
  | ConjR Sequent Proof Proof
  | DisjL Sequent Proof Proof
  | DisjR Sequent Proof
  | ImplL Sequent Proof Proof
  | ImplR Sequent Proof
  | NegL Sequent Proof
  | NegR Sequent Proof
  | Axiom Sequent
 deriving (Show, Eq)

-- helpers
rule :: String -> Doc -> Doc -> Doc
rule str x y = x $$ (text "——————————" <+> text str) $$ y
renderS :: Sequent -> Doc
renderS = text . render

prettyProof :: Proof -> Doc
prettyProof (ConjL s pr) = rule "∧l" (prettyProof pr) (renderS s)
prettyProof (ConjR s pr1 pr2) = rule "∧r" (prettyProof pr1 <+> prettyProof pr2) (renderS s)
prettyProof (DisjL s pr1 pr2) = rule "∨l" (prettyProof pr1 <+> prettyProof pr2) (renderS s)
prettyProof (DisjR s pr) = rule "∨r" (prettyProof pr) (renderS s)
prettyProof (ImplL s pr1 pr2) = rule "→l" (prettyProof pr1 <+> prettyProof pr2) (renderS s)
prettyProof (ImplR s pr) = rule "→r" (prettyProof pr) (renderS s)
prettyProof (NegL s pr) = rule "¬l" (prettyProof pr) (renderS s)
prettyProof (NegR s pr) = rule "¬r" (prettyProof pr) (renderS s)
prettyProof (Axiom s) = rule "" (text "axiom") (renderS s)

instance Render Proof where
  render = renderStyle s . prettyProof
    where s = Style PageMode 100 1.0

tauto :: Expr -> Bool
tauto p = valid ([] :=> pure p)

valid :: Sequent -> Bool
-- negation right
valid (g :=> ((Neg p):d)) = valid ((p:g) :=> d)
-- negation left
valid (((Neg p):g) :=> d) = valid (g :=> (p:d))
-- implication right
valid (g :=> ((Impl p q):d)) = valid ((p:g) :=> (q:d))
-- implication left
valid (((Impl p q):g) :=> d) = valid (g :=> (p:d)) && valid ((q:g) :=> d)
-- disjunction right
valid (g :=> ((Disj p q):d)) = valid (g :=> (p:(q:d)))
-- disjunction left
valid (((Disj p q):g) :=> d) = valid ((p:g) :=> d) && valid ((q:g) :=> d)
-- conjunction right
valid (g :=> ((Conj p q):d)) = valid (g :=> (p:d)) && valid (g :=> (q:d))
-- conjunction left
valid (((Conj p q):g) :=> d) = valid ((p:(q:g)) :=> d)
-- axiom/confluence
valid (g :=> []) = False
valid ([] :=> ((Atom p):d)) = all isAtom d || valid ([] :=> (d<>[Atom p]))
valid ((p:g) :=> (q:d)) | all isAtom g && all isAtom d = not $ null $ intersect (p:g) (q:d)
                        | all isAtom g = valid ((p:g) :=> (d<>[q]))
                        | otherwise = valid ((g<>[p]) :=> (q:d))


proof :: Sequent -> Maybe Proof
-- negation right
proof (g :=> ((Neg p):d)) = do
  pr <- proof ((p:g) :=> d)
  return $ NegR (g :=> (Neg p:d)) pr
-- negation left
proof (((Neg p):g) :=> d) = do
  pr <- proof (g :=> (p:d))
  return $ NegL ((Neg p:g) :=> d) pr
-- implication right
proof (g :=> ((Impl p q):d)) = do
  pr <- proof ((p:g) :=> (q:d))
  return $ ImplR (g :=> (Impl p q:d)) pr
-- implication left
proof (((Impl p q):g) :=> d) = do
  pr1 <- proof (g :=> (p:d))
  pr2 <- proof ((q:g) :=> d)
  return $ ImplL ((Impl p q:g) :=> d) pr1 pr2
-- disjunction right
proof (g :=> ((Disj p q):d)) = do
  pr <- proof (g :=> (p:(q:d)))
  return $ DisjR (g :=> (Disj p q:d)) pr
-- disjunction left
proof (((Disj p q):g) :=> d) = do
  pr1 <- proof ((p:g) :=> d)
  pr2 <- proof ((q:g) :=> d)
  return $ DisjL ((Disj p q:g) :=> d) pr1 pr2
-- conjunction right
proof (g :=> (Conj p q:d)) = do
  pr1 <- proof (g :=> (p:d))
  pr2 <- proof (g :=> (q:d))
  return $ ConjR (g :=> (Conj p q:d)) pr1 pr2
-- conjunction left
proof (((Conj p q):g) :=> d) = do
  pr <- proof ((p:(q:g)) :=> d)
  return $ ConjL ((Conj p q:g) :=> d) pr
-- axiom/confluence
proof (g :=> []) = Nothing
proof ([] :=> ((Atom p):d)) = if all isAtom d
                              then return $ Axiom ([] :=> (Atom p:d))
                              else proof ([] :=> (d<>[Atom p]))
proof ((p:g) :=> (q:d)) | all isAtom g && all isAtom d && not (null $ intersect (p:g) (q:d))
                            = return $ Axiom ((p:g) :=> (q:d))
                        | all isAtom g = proof ((p:g) :=> (d<>[q]))
                        | otherwise = proof ((g<>[p]) :=> (q:d))

example :: Sequent
example = [] :=> [Impl (Impl (Conj (Atom 'p') (Atom 'q')) (Atom 'r'))
                       (Impl (Atom 'p') (Impl (Atom 'q') (Atom 'r')))]
