module Parser where

import Data.Either
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token

import Extracted (Expr(..), Ty(..), Cap(..), Ecap(..), Program(..), List_expr(..), list_expr_coerce)
import Extracted (Field, Func, Func_stub, Behv, Behv_stub, Ctor, Ctor_stub, Class, Iface, Trait)

languageDef =
   emptyDef { Token.commentStart    = "/*"
            , Token.commentEnd      = "*/"
            , Token.commentLine     = "//"
            , Token.identStart      = lower
            , Token.identLetter     = alphaNum
            , Token.reservedNames   = [ "recover", "consume", "null"
                                      , "class", "actor", "interface", "trait"
                                      , "fun", "new", "var", "is"
                                      , "iso", "ref" ]
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

expr_ctor :: Parser Expr
expr_ctor = do
  kt <- tyname
  (k, es) <- option ("create", List_expr_nil) ((,) <$ reservedOp "." <*> identifier <*> parens (list_expr_coerce <$> commaSep expr))
  return (Expr_ctor kt k es)

term :: Parser Expr
term = parens expr <|>
    Expr_null <$ reserved "null" <|>
    Expr_local <$> identifier <|>
    expr_ctor <|>
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

item_body :: Parser (String, a) -> Parser (String, (a, Expr))
item_body p = do
  (m, info) <- p
  reservedOp "=>"
  body <- expr
  return (m, (info, body))

item_func_stub :: Parser Func_stub
item_func_stub = do
  reserved "fun"
  receiver <- option Cap_box cap
  m <- identifier
  args <- parens (commaSep ((,) <$> identifier <* colon <*> ty))
  colon
  retty <- ty
  return (m, ((receiver, args), retty))

item_ctor_stub :: Parser Ctor_stub
item_ctor_stub = do
  reserved "new"
  m <- identifier
  args <- parens (commaSep ((,) <$> identifier <* colon <*> ty))
  return (m, args)

item_behv_stub :: Parser Behv_stub
item_behv_stub = do
  reserved "be"
  m <- identifier
  args <- parens (commaSep ((,) <$> identifier <* colon <*> ty))
  return (m, args)

item_func :: Parser Func
item_func = item_body item_func_stub

item_ctor :: Parser Ctor
item_ctor = item_body item_ctor_stub

item_behv :: Parser Behv
item_behv = item_body item_behv_stub

def_abstract :: String -> Parser (String, ((([Ctor_stub], [Func_stub]), [Behv_stub]), [String]))
def_abstract kw = do
  reserved kw
  {- optional cap -}
  c <- tyname
  parents <- option [] (reserved "is" >> (commaSep tyname))
  items <- many_ooo3 item_ctor_stub item_func_stub item_behv_stub
  return (c, (items, parents))


def_iface :: Parser Iface
def_iface = def_abstract "interface"

def_trait :: Parser Trait
def_trait = def_abstract "trait"

def_class :: Parser Class
def_class = do
  reserved "class"
  {- optional cap -}
  c <- tyname
  parents <- option [] (reserved "is" >> (commaSep tyname))
  items <- many_ooo3 item_field item_ctor item_func
  return (c, (items, parents))

prog :: Parser Program
prog = do
  cs <- many def_class
  defs <- many_ooo3 def_trait def_iface def_class
  return (defs, [])

foo :: String -> Parser a -> Either ParseError a
foo t p = parse p "" t

type P = Parser
