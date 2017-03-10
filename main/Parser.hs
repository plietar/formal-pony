module Parser where

import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import Extracted (Expr(..), Ty(..), Cap(..), Program(..), Def(..), Item(..), list_expr_coerce)

languageDef =
   emptyDef { Token.commentStart    = "/*"
            , Token.commentEnd      = "*/"
            , Token.commentLine     = "//"
            , Token.identStart      = lower
            , Token.identLetter     = alphaNum
            , Token.reservedNames   = [ "recover", "class", "fun", "new", "var", "iso", "ref" ]
            , Token.reservedOpNames = [ "=", ".", ";", "=>" ]
            }

lexer = Token.makeTokenParser languageDef
identifier = Token.identifier lexer
reserved = Token.reserved lexer
reservedOp = Token.reservedOp lexer
parens = Token.parens lexer
whiteSpace = Token.whiteSpace lexer
commaSep = Token.commaSep lexer
colon = Token.colon lexer

tyname = Token.identifier $ Token.makeTokenParser $ languageDef { Token.identStart = upper }

op_seq = reservedOp ";" >> return Expr_seq

op_field = do
  reservedOp "."
  ident <- identifier
  notFollowedBy (reservedOp "=")

  return (\e -> Expr_field e ident)

op_call = do
  reservedOp "."
  ident <- identifier
  e_args <- parens (commaSep expr)
  return (\e -> Expr_call e ident (list_expr_coerce e_args))

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

cap :: Parser Cap
cap = Cap_iso <$ reserved "iso" <|>
      Cap_ref <$ reserved "ref" <|>
      Cap_tag <$ reserved "tag" <?> "capability"

ty :: Parser Ty
ty = Ty_name <$> tyname <*> cap <?> "type"

term :: Parser Expr
term = parens expr <|>
    Expr_local <$> identifier <|>
    Expr_ctor <$> tyname <* reservedOp "." <*> identifier <*> parens (list_expr_coerce <$> commaSep expr)

expr :: Parser Expr
expr = buildExpressionParser operators term <?> "expression"

item_var :: Parser Item
item_var = reserved "var" >> Item_field <$> identifier <* colon <*> ty

item_fun :: Parser Item
item_fun = reserved "fun" >> Item_func <$> cap
                                       <*> identifier
                                       <*> parens (commaSep ((,) <$> identifier <* colon <*> ty))
                                       <* colon
                                       <*> ty
                                       <* reservedOp "=>"
                                       <*> expr

item_new :: Parser Item
item_new = reserved "new" >> Item_ctor <$> identifier
                                       <*> parens (commaSep ((,) <$> identifier <* colon <*> ty))
                                       <* reservedOp "=>"
                                       <*> expr
item :: Parser Item
item = item_var <|> item_fun <|> item_new

def :: Parser Def
def = reserved "class" >> Def_class <$> tyname <*> many item

prog :: Parser Program
prog = many def

foo :: String -> Parser a -> Either ParseError a
foo t p = parse p "" t

type P = Parser
