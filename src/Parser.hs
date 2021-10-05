{-# LANGUAGE FlexibleContexts #-}

module Parser (parseExpr) where

import Prop

import Text.ParserCombinators.Parsec
import Text.Parsec.Char
import Text.Parsec.Expr

parseExpr :: String -> Either ParseError Expr
parseExpr = parse expr "ParseError:"

term :: Parser Expr
term = (char '(' >> expr >>= \e -> char ')' >> return e)
   <|> (Atom <$> lower) <?> "simple expression"

expr :: Parser Expr
expr = buildExpressionParser table term <?> "expression"

table = [ [prefix "¬" Neg, prefix "~" Neg ]
        , [binary "&" Conj AssocLeft, binary "∧" Conj AssocLeft ]
        , [binary "↓" Peirce AssocLeft, binary ";" Peirce AssocLeft ]
        , [binary "|" Disj AssocLeft, binary "∨" Disj AssocLeft ]
        , [binary "->" Impl AssocRight, binary ">" Impl AssocRight, binary "→" Impl AssocRight ]
        ]

binary name fun = Infix $ string name >> return fun
prefix name fun = Prefix $ spaces >> string name >> spaces >> return fun
