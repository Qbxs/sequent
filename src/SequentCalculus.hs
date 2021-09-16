{-# Language TypeOperators #-}

module SequentCalculus where

import Prop

import Data.List (intercalate, intersect)
import Text.PrettyPrint.Boxes hiding (render, (<>))
import qualified Text.PrettyPrint.Boxes as Pretty

-- mysterious
-- block = renderStyle (Style PageMode 100 1.0) $ (int 1 $$ int 2) <+> (nest (-1) $ int 3 $$ int 4)


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
rule :: String -> Box -> Box -> Box
rule str x y = vcat center2 [x, text (replicate (cols x) '—') <+> text str, y]
renderS :: Sequent -> Box
renderS = text . render

pretty :: Proof -> Box
pretty (ConjL s pr) = rule "∧l" (pretty pr) (renderS s)
pretty (ConjR s pr1 pr2) = rule "∧r" (hcat bottom [pretty pr1, pretty pr2]) (renderS s)
pretty (DisjL s pr1 pr2) = rule "∨l" (hcat bottom [pretty pr1, pretty pr2]) (renderS s)
pretty (DisjR s pr) = rule "∨r" (pretty pr) (renderS s)
pretty (ImplL s pr1 pr2) = rule "→l" (hcat bottom [pretty pr1, pretty pr2]) (renderS s)
pretty (ImplR s pr) = rule "→r" (pretty pr) (renderS s)
pretty (NegL s pr) = rule "¬l" (pretty pr) (renderS s)
pretty (NegR s pr) = rule "¬r" (pretty pr) (renderS s)
pretty (Axiom s) = rule "" (text "axiom") (renderS s)

instance Render Proof where
  render = Pretty.render . pretty

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
valid ([] :=> d) = False
valid ((p:g) :=> (q:d)) | all isAtom g && all isAtom d
                             = not $ null $ intersect (p:g) (q:d)
                        | all isAtom g = valid ((p:g) :=> (d<>[q]))
                        | otherwise = valid ((g<>[p]) :=> (q:d))


proof :: Sequent -> Maybe Proof
proof (g :=> ((Neg p):d)) = do
  pr <- proof ((p:g) :=> d)
  return $ NegR (g :=> (Neg p:d)) pr
proof (((Neg p):g) :=> d) = do
  pr <- proof (g :=> (p:d))
  return $ NegL ((Neg p:g) :=> d) pr
proof (g :=> ((Impl p q):d)) = do
  pr <- proof ((p:g) :=> (q:d))
  return $ ImplR (g :=> (Impl p q:d)) pr
proof (((Impl p q):g) :=> d) = do
  pr1 <- proof (g :=> (p:d))
  pr2 <- proof ((q:g) :=> d)
  return $ ImplL ((Impl p q:g) :=> d) pr1 pr2
proof (g :=> ((Disj p q):d)) = do
  pr <- proof (g :=> (p:(q:d)))
  return $ DisjR (g :=> (Disj p q:d)) pr
proof (((Disj p q):g) :=> d) = do
  pr1 <- proof ((p:g) :=> d)
  pr2 <- proof ((q:g) :=> d)
  return $ DisjL ((Disj p q:g) :=> d) pr1 pr2
proof (g :=> (Conj p q:d)) = do
  pr1 <- proof (g :=> (p:d))
  pr2 <- proof (g :=> (q:d))
  return $ ConjR (g :=> (Conj p q:d)) pr1 pr2
proof (((Conj p q):g) :=> d) = do
  pr <- proof ((p:(q:g)) :=> d)
  return $ ConjL ((Conj p q:g) :=> d) pr
proof (g :=> []) = Nothing
proof ([] :=> (q:d)) = if all isAtom d then Nothing else proof ([] :=> (d<>[q]))
proof ((p:g) :=> (q:d)) | all isAtom g && all isAtom d
                            = if null $ intersect (p:g) (q:d)
                              then Nothing
                              else return $ Axiom ((p:g) :=> (q:d))
                        | all isAtom g = proof ((p:g) :=> (d<>[q]))
                        | otherwise = proof ((g<>[p]) :=> (q:d))

example :: Sequent
example = [] :=> [Impl (Impl (Conj (Atom 'p') (Atom 'q')) (Atom 'r'))
                       (Impl (Atom 'p') (Impl (Atom 'q') (Atom 'r')))]
