module Parser where

import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import Extracted (Expr(..))

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

op_seq = reservedOp ";" >> return Expr_seq

op_field = do
  reservedOp "."
  ident <- identifier
  notFollowedBy (reservedOp "=")

  return (\e -> Expr_field e ident)

op_call = do
  reservedOp "."
  ident <- identifier
  parens (return ())
  return (\e -> Expr_call e ident)

op_assign_field = do
  reservedOp "."
  ident <- identifier
  reservedOp "="

  return (\e1 e2 -> Expr_assign_field e1 ident e2)

op_assign_local = do
  ident <- identifier
  reservedOp "="
  return (Expr_assign_local ident)

operators = [ [ Postfix (try op_call) ]
            , [ Postfix (try op_field) ]
            , [ Infix (try op_assign_field) AssocRight ]
            , [ Prefix (try op_assign_local) ]
            , [ Infix (try op_seq) AssocLeft ] ]

term :: Parser Expr
term = parens expr <|> Expr_local <$> identifier

expr :: Parser Expr
expr = buildExpressionParser operators term
