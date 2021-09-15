module Prop where


data Expr
  = Atom Char
  | Neg Expr
  | Conj Expr Expr
  | Disj Expr Expr
  | Impl Expr Expr
 deriving (Show, Eq, Ord)

class Render a where
  render :: a -> String

instance Render Expr where
  render (Atom c) = pure c
  render (Neg p) = '¬':render p
  render (Conj p q) = "(" <> render p <> "∧" <> render q <> ")"
  render (Disj p q) = "(" <> render p <> "∨" <> render q <> ")"
  render (Impl p q) = "(" <> render p <> "→" <> render q <> ")"

isAtom :: Expr -> Bool
isAtom (Atom _) = True
isAtom _ = False
