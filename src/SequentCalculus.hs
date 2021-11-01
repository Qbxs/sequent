{-# LANGUAGE TypeOperators #-}

module SequentCalculus
        ( Proof(..)
        , tauto
        , contra
        , valid
        , proof
        ) where

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
data Bucket a b = Bucket (S.Set a) [b]
 deriving (Show, Eq)

data Sequent = (:=>) (Bucket Char Expr) (Bucket Char Expr)
 deriving (Show, Eq)

push :: Expr -> Bucket Char Expr -> Bucket Char Expr
push (Atom p) (Bucket s l) = Bucket (S.insert p s) l
push p (Bucket s l) = Bucket s (p:l)

instance Render Sequent where
  render ((Bucket s g) :=> (Bucket t d)) = gamma <> " ⊢ " <> delta
                  where gamma = intercalate "," $ (pure <$> S.toList s) <> (render <$> g)
                        delta = intercalate "," $ (pure <$> S.toList t) <> (render <$> d)

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
  | Assumption Sequent
 deriving (Show, Eq)

-- falsifying Interpretation to extract
data Interpretation
  = Interpretation
     { false :: S.Set Char
     , true :: S.Set Char
     }

instance Semigroup Interpretation where
  (<>) l r = Interpretation (false l `S.union` false r) (true l `S.union` true r)
instance Monoid Interpretation where
  mempty = Interpretation S.empty S.empty
instance Render Interpretation where
  render i = intercalate ", " $! map (\x -> "I(" <> pure x <> ")=t") (S.toList $ true i)
                              <> map (\x -> "I(" <> pure x <> ")=f") (S.toList $ false i)

-- helpers
rule :: String -> Box -> Box -> Box
rule str x y = vcat center2 [x, text bar <+> text str, y]
  where bar = replicate (if cols x == 0 then 0 else max 6 (cols x-3)) '—'
renderS :: Sequent -> Box
renderS = text . render

pretty :: Proof -> Box
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

tauto :: Expr -> Writer Interpretation Proof
tauto p = proof (Bucket S.empty [] :=> Bucket S.empty [p])

contra :: Expr -> Writer Interpretation Proof
contra p = proof (Bucket S.empty [p] :=> Bucket S.empty [])

valid :: Sequent -> Bool
-- remove atoms
valid ((Bucket s ((Atom p):g)) :=> d) = valid (Bucket (S.insert p s) g :=> d)
valid (g :=> (Bucket s ((Atom p):d))) = valid (g :=> Bucket (S.insert p s) d)
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

-- | Build a proof tree in LK and memorize (write) falsifying interpretations
--   as of right now explores the whole tree rather than stopping on an unsatisfiable leaf
--   alpha rules will match first, however only if they appear first on one side
proof :: Sequent -> Writer Interpretation Proof
proof ((Bucket s ((Atom p):g)) :=> d) = proof (Bucket (S.insert p s) g :=> d)
proof (g :=> (Bucket s ((Atom p):d))) = proof (g :=> Bucket (S.insert p s) d)
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
proof (Bucket s (Verum:g) :=> d) = proof (Bucket s g :=> d)
proof e@(g :=> Bucket s (Verum:d)) = return (Axiom e)
proof e@(Bucket s (Falsum:g) :=> d) = return (Assumption e)
proof (g :=> Bucket s (Falsum:d)) = proof (g :=> Bucket s d)
proof e@((Bucket s []) :=> (Bucket t [])) = if S.null $ S.intersection s t
                                            then do
                                              tell $ Interpretation {true=s,false=t}
                                              return (Assumption e)
                                            else return $ Axiom e

example :: Sequent
example = Bucket S.empty [] :=> Bucket S.empty [Impl (Impl (Conj (Atom 'p') (Atom 'q')) (Atom 'r'))
                                                     (Impl (Atom 'p') (Impl (Atom 'q') (Atom 'r')))]
