module Parser where

import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import Ast

languageDef =
   emptyDef { Token.commentStart    = "/*"
            , Token.commentEnd      = "*/"
            , Token.commentLine     = "//"
            , Token.identStart      = letter
            , Token.identLetter     = alphaNum
            , Token.reservedNames   = [ "recover" ]
            , Token.reservedOpNames = [ "=", ".", ";" ]
            }

lexer = Token.makeTokenParser languageDef
identifier = Token.identifier lexer
reserved = Token.reserved lexer
reservedOp = Token.reservedOp lexer
parens = Token.parens lexer
whiteSpace = Token.whiteSpace lexer

op_seq = reservedOp ";" >> return Coq_expr_seq

op_field = do
  reservedOp "."
  ident <- identifier
  notFollowedBy (reservedOp "=")

  return (\e -> Coq_expr_field e ident)

op_assign_field = do
  reservedOp "."
  ident <- identifier
  reservedOp "="

  return (\e1 e2 -> Coq_expr_assign_field e1 ident e2)

op_assign_local = do
  ident <- identifier
  reservedOp "="
  return (Coq_expr_assign_local ident)

operators = [ [ Postfix (try op_field) ]
            , [ Infix (try op_assign_field) AssocRight ]
            , [ Prefix (try op_assign_local) ]
            , [ Infix (try op_seq) AssocLeft ] ]

term :: Parser Coq_expr
term = parens expr <|> Coq_expr_local <$> identifier

expr :: Parser Coq_expr
expr = buildExpressionParser operators term
