module Parser (parseExpr) where

import Prop

import Text.ParserCombinators.Parsec

parseExpr :: String -> Either ParseError Expr
parseExpr = parse expr "ParseError:"

expr :: Parser Expr
expr = choice [ neg, try conj, try disj, try impl, atom ]

atom :: Parser Expr
atom = Atom <$> alphaNum

neg :: Parser Expr
neg = (char '¬' <|> char '~') >> Neg <$> expr

conj :: Parser Expr
conj = do
  char '('
  e1 <- expr
  spaces
  char '&' <|> char '∧'
  spaces
  e2 <- expr
  char ')'
  return $ Conj e1 e2

disj :: Parser Expr
disj = do
  char '('
  e1 <- expr
  spaces
  char '|' <|> char '∨'
  spaces
  e2 <- expr
  char ')'
  return $ Disj e1 e2

impl :: Parser Expr
impl = do
  char '('
  e1 <- expr
  spaces
  char '>' <|> char '→'
  spaces
  e2 <- expr
  char ')'
  return $ Impl e1 e2
