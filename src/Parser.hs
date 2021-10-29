{-# LANGUAGE FlexibleContexts #-}

module Parser (parseExpr, parseClause) where

import Prop

import Text.ParserCombinators.Parsec
import Text.Parsec.Char
import Text.Parsec.Expr

parseExpr :: String -> Either ParseError Expr
parseExpr = parse expr "Error while parsing expression"

parseClause :: String -> Either ParseError Clause
parseClause = parse clauses "Error while parsing clause"

clauses :: Parser Clause
clauses = Clause <$> (char '{' *> many (clause <* sep) <* char '}') <?> "clause form"

clause :: Parser [Literal]
clause = char '{' *> many (literal <* sep) <* char '}' <?> "clause"

literal :: Parser Literal
literal = ((char '~' <|> char '¬') *> (Negated <$> lower))
       <|> (Lit <$> lower) <?> "literal"

sep :: Parser ()
sep = spaces <* optional (char ',') *> spaces

term :: Parser Expr
term = (char '(' *> expr <* char ')')
    <|> (Atom <$> lower) <?> "simple expression" -- add logical constants?

expr :: Parser Expr
expr = buildExpressionParser table term <?> "expression"

table :: (Monad m) => OperatorTable String u m Expr
table = [ [prefix "¬" Neg, prefix "~" Neg ]
        , [binary "&" Conj AssocLeft, binary "∧" Conj AssocLeft ]
        , [binary "|" Disj AssocLeft, binary "∨" Disj AssocLeft ]
        , [binary "->" Impl AssocRight, binary ">" Impl AssocRight, binary "→" Impl AssocRight ]
        ] where
            binary name fun = Infix $ string name >> return fun
            prefix name fun = Prefix $ spaces >> string name >> spaces >> return fun
