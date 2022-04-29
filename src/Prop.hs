module Prop where

data Expr
  = Verum
  | Falsum
  | Atom Char
  | Neg Expr
  | Conj Expr Expr
  | Disj Expr Expr
  | Impl Expr Expr
 deriving (Eq, Ord)

instance Show Expr where
  showsPrec _  Verum      = showChar 'T'
  showsPrec _  Falsum     = showChar 'F'
  showsPrec _  (Atom p)   = showChar p
  showsPrec pr (Neg p)    = showParen (pr > 3) $ showChar '¬' . showsPrec 3 p
  showsPrec pr (Conj p q) = showParen (pr > 2) $ showsPrec 3 p . showChar '∧' . showsPrec 2 q
  showsPrec pr (Disj p q) = showParen (pr > 1) $ showsPrec 2 p . showChar '∨' . showsPrec 1 q
  showsPrec pr (Impl p q) = showParen (pr > 0) $ showsPrec 1 p . showChar '→' . shows q

data Literal = Lit Char | Negated Char
 deriving (Show, Eq, Ord)

newtype Clause = Clause { getClauses :: [[Literal]] }


class Render a where
  render :: a -> String
  printR :: a -> IO ()
  printR = putStrLn . render

instance Render Literal where
  render (Lit p) = pure p
  render (Negated p) = '¬':pure p

instance (Render a) => Render [a] where
  render = ('{':) . go
   where go [] = "}"
         go [x] = render x <> "}"
         go (x:xs) = render x <> "," <> go xs

instance Render Clause where
  render = render . getClauses

instance Render Expr where
  render = show

isAtom :: Expr -> Bool
isAtom (Atom _) = True
isAtom _ = False

isPositive :: Literal -> Bool
isPositive (Lit _) = True
isPositive _ = False

toChar :: Expr -> Char
toChar (Atom p) = p
toChar _ = undefined
