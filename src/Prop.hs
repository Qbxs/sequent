module Prop where


data Expr
  = Atom Char
  | Neg Expr
  | Conj Expr Expr
  | Disj Expr Expr
  | Impl Expr Expr
 deriving (Eq, Ord)

instance Show Expr where
  showsPrec _  (Atom p)   = showChar p
  showsPrec pr (Neg p)    = showParen (pr > 3) $ showChar '¬' . showsPrec 3 p
  showsPrec pr (Conj p q) = showParen (pr > 2) $ showsPrec 3 p . showChar '∧' . showsPrec 2 q
  showsPrec pr (Disj p q) = showParen (pr > 1) $ showsPrec 2 p . showChar '∨' . showsPrec 1 q
  showsPrec pr (Impl p q) = showParen (pr > 0) $ showsPrec 1 p . showChar '→' . shows q

class Render a where
  render :: a -> String

instance Render Expr where
  render = show

isAtom :: Expr -> Bool
isAtom (Atom _) = True
isAtom _ = False
