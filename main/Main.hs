{-# LANGUAGE StandaloneDeriving #-}

import System.IO
import Control.Monad
import Text.ParserCombinators.Parsec hiding (State)
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import qualified Text.ParserCombinators.Parsec.Token as Token
import Control.Monad.State.Lazy

import Ast
import Semantics (Coq_heap, Coq_frame, Coq_local_id(..), Coq_value(..))
import Eval
import Extract (init)

deriving instance Show Coq_value
deriving instance Show Coq_local_id
deriving instance Show Coq_expr

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

operators = [ [Infix (reservedOp ";" >> return Coq_expr_seq) AssocLeft ] ]

term :: Parser Coq_expr
term = parens expr
       <|> Coq_expr_assign_local <$> try (identifier <* (reservedOp "=")) <*> expr
       <|> Coq_expr_local <$> identifier

expr :: Parser Coq_expr
expr = buildExpressionParser operators term

type Ctx = State (Coq_heap, Coq_frame)

replOne :: String -> (Coq_heap, Coq_frame) -> ([String], (Coq_heap, Coq_frame))
replOne contents (heap, frame) = ([show temp, show frame], (heap', frame'))
  where
    Right e = parse (whiteSpace >> expr <* eof ) "" contents
    ((heap', frame'), temp) = eval heap frame e
    
repl :: [String] -> [String]
repl contents = concat $ evalState (mapM (state . replOne) contents) Extract.init

main :: IO ()
main = interact (unlines . repl . lines)
