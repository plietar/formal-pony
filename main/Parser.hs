module Parser where

import Data.Either
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import Extracted (Expr(..), Ty(..), Cap(..), Ecap(..), Program(..), list_expr_coerce)
import Extracted (Field, Func, Behv, Ctor, Class)

languageDef =
   emptyDef { Token.commentStart    = "/*"
            , Token.commentEnd      = "*/"
            , Token.commentLine     = "//"
            , Token.identStart      = lower
            , Token.identLetter     = alphaNum
            , Token.reservedNames   = [ "recover", "consume", "class", "fun", "new", "var", "iso", "ref", "null" ]
            , Token.reservedOpNames = [ "=", ".", ";", "=>", "^" ]
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

ecap :: Parser Ecap
ecap = do
  c <- cap
  mod <- optionMaybe (reservedOp "^")
  case (c, mod) of
    (Cap_iso, Just ()) -> return Cap_iso_eph
    (c, Just ()) -> return (Ecap_cap c)
    (_ , Nothing) -> return (Ecap_cap c)

ty :: Parser Ty
ty = Ty_name <$> tyname <*> ecap <?> "type"

term :: Parser Expr
term = parens expr <|>
    Expr_null <$ reserved "null" <|>
    Expr_local <$> identifier <|>
    Expr_ctor <$> tyname <* reservedOp "." <*> identifier <*> parens (list_expr_coerce <$> commaSep expr) <|>
    (\x -> Expr_assign_local x Expr_null) <$ reserved "consume" <*> identifier

expr :: Parser Expr
expr = buildExpressionParser operators term <?> "expression"

many_ooo2 :: Parser a -> Parser b -> Parser ([a], [b])
many_ooo2 pa pb = partitionEithers <$> many (Left <$> pa <|> Right <$> pb)

many_ooo3 :: Parser a -> Parser b -> Parser c -> Parser (([a], [b]), [c])
many_ooo3 pa pb pc = do
  abcs <- many pabc
  return (foldr f (([], []), []) abcs) 
  where
    pabc = (Left <$> pab <|> Right <$> pc)
    pab = (Left <$> pa <|> Right <$> pb)

    f (Left (Left a)) ((as, bs), cs) = ((a:as, bs), cs)
    f (Left (Right b)) ((as, bs), cs) = ((as, b:bs), cs)
    f (Right c) ((as, bs), cs) = ((as, bs), c:cs)

item_field :: Parser Field
item_field = reserved "var" >> (,) <$> identifier <* colon <*> ty

item_func :: Parser Func
item_func = do
  reserved "fun"
  receiver <- cap
  m <- identifier
  args <- parens (commaSep ((,) <$> identifier <* colon <*> ty))
  colon
  retty <- ty
  reservedOp "=>"
  body <- expr
  return (m, (((receiver, args), retty), body))

item_ctor :: Parser Ctor
item_ctor = do
  reserved "new"
  m <- identifier
  args <- parens (commaSep ((,) <$> identifier <* colon <*> ty))
  reservedOp "=>"
  body <- expr
  return (m, (args, body))

def_class :: Parser Class
def_class = do
  reserved "class"
  c <- tyname
  items <- many_ooo3 item_field item_ctor item_func
  return (c, items)

prog :: Parser Program
prog = do
  cs <- many def_class
  return ((([], []), cs), [])

foo :: String -> Parser a -> Either ParseError a
foo t p = parse p "" t

type P = Parser
