{-# LANGUAGE StandaloneDeriving #-}

import Control.Monad.State.Lazy
import Control.Monad.Except
import Data.Char
import System.IO
import Text.Parsec (parse)
import Text.Parsec.Combinator (eof)

import qualified Parser
import Extracted (Expr(..), Expr_hole, Heap, Value(..), Local_id(..), Frame)
import qualified Extracted

deriving instance Show Value
deriving instance Show Local_id
deriving instance Show Expr
deriving instance Show Expr_hole
deriving instance Show (Extracted.Object)
deriving instance Show (Extracted.N)
deriving instance Show (Extracted.Positive)
deriving instance (Show a) => Show (Extracted.Pmap_raw a)
deriving instance (Show a) => Show (Extracted.Nmap a)

type ST = Heap
type Repl = StateT ST (ExceptT String IO)

(init_heap, init_stack) = Extracted.init

parser :: String -> Repl Expr
parser line =
  case parse (Parser.expr <* eof) "<interactive>" line of
    Right e -> return e
    Left err -> throwError (show err)

evaluate' :: Expr -> [Frame] -> Repl Value
evaluate' expr@(Expr_temp temp) [frame] = do
  let Just x = Extracted.lookup (Extracted.frame_lookup Extracted.localmap_lookup_temp) temp frame in return x

evaluate' expr stack = do
  heap <- get

  case Extracted.eval heap stack expr of
    Just ((heap', stack'), expr') -> put heap' >> evaluate' expr' stack'
    Nothing -> throwError "eval error"

evaluate :: Expr -> Repl Value
evaluate expr = evaluate' expr init_stack

command :: String -> String -> Repl ()
command "heap"  _ = get >>= liftIO . print
command "reset" _ = put init_heap
command "parse" line = parser line >>= liftIO . print

repl :: String -> Repl ()
repl "" = return ()
repl (':':line) =
  let (c, rest) = break isSpace line in
  command c (dropWhile isSpace rest)

repl line = do
  e <- parser line
  value <- evaluate e
  heap <- get

  case value of
    V_null -> liftIO (putStrLn "null")
    V_addr addr ->
      let (Just object) = Extracted.lookup Extracted.nlookup addr heap
      in liftIO (print object)

replMany :: Repl ()
replMany = forever $ do
  liftIO (putStr "> " >> hFlush stdout)
  line <- liftIO getLine
  catchError (repl line) (\err -> liftIO (putStrLn err))

main :: IO ()
main = do
  result <- runExceptT (evalStateT replMany init_heap)
  case result of
    Left err -> putStrLn ("Fatal error:" ++ err)
    Right () -> return ()
