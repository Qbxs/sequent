module Prop where


data Expr
  = Atom Char
  | Neg Expr
  | Conj Expr Expr
  | Disj Expr Expr
  | Impl Expr Expr
  | Forall Char Expr
  | Exists Char Expr
 deriving (Eq, Ord)

instance Show Expr where
  showsPrec _  (Atom x)   = showChar x
  showsPrec pr (Neg p)    = showParen (pr > 5) $ showChar '¬' . showsPrec 5 p
  showsPrec pr (Conj p q) = showParen (pr > 4) $ showsPrec 5 p . showChar '∧' . showsPrec 4 q
  showsPrec pr (Disj p q) = showParen (pr > 3) $ showsPrec 4 p . showChar '∨' . showsPrec 3 q
  showsPrec pr (Impl p q) = showParen (pr > 2) $ showsPrec 3 p . showChar '→' . showsPrec 2 q
  showsPrec pr (Forall x p) = showChar '∀' . showChar x . showChar '.' . showParen (pr > 1) (showsPrec 1 p)
  showsPrec pr (Exists x p) = showChar '∃' . showChar x . showChar '.' . showParen (pr > 0) (shows p)

class Render a where
  render :: a -> String

instance Render Expr where
  render = show

isAtom :: Expr -> Bool
isAtom (Atom _) = True
isAtom _ = False
