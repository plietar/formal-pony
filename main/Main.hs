{-# LANGUAGE StandaloneDeriving #-}

import Control.Monad.State.Lazy
import Control.Monad.Except
import Data.Char
import System.IO
import Text.Parsec (parse)
import Text.Parsec.Combinator (eof)

import Ast
import Entities (Coq_heap, Coq_frame, Coq_local_id(..), Coq_value(..))
import Eval
import Extract (init)
import Parser (expr)

deriving instance Show Coq_value
deriving instance Show Coq_local_id
deriving instance Eq Coq_local_id
deriving instance Show Coq_expr

type ST = (Coq_heap, Coq_frame)
type Repl = StateT ST (ExceptT String IO)

gc :: Repl ()
gc = modify gc'
  where
    gc' (heap, frame) = (heap, filter (isSourceId . fst) frame)
    isSourceId (SourceId _) = True
    isSourceId (TempId _) = False

parser :: String -> Repl Coq_expr
parser line = case parse (expr <* eof) "<interactive>" line of
  Right e -> return e
  Left err -> throwError (show err)

command :: String -> String -> Repl ()
command "heap"  _ = gets fst >>= liftIO . print
command "frame" _ = gets snd >>= liftIO . print
command "clear" _ = put Extract.init
command "gc" _ = gc
command "parse" line = parser line >>= liftIO . print

repl :: String -> Repl ()
repl (':':line) =
  let (c, rest) = break isSpace line in
  command c (dropWhile isSpace rest)

repl line = do
  e <- parser line
  (heap, frame) <- get
  let ((heap', frame'), temp) = eval heap frame e
  case lookup (TempId temp) frame' of
    Just Coq_v_null -> liftIO (putStrLn "null")
    Just (Coq_v_addr addr) ->
      let (Just object) = lookup addr heap'
      in liftIO (print object)

  put (heap', frame')

  gc

replMany :: Repl ()
replMany = forever $ do
  liftIO (putStr "> " >> hFlush stdout)
  line <- liftIO getLine
  catchError (repl line) (\err -> liftIO (putStrLn err))

main :: IO ()
main = do
  result <- runExceptT (evalStateT replMany Extract.init)
  case result of
    Left err -> putStrLn ("Fatal error:" ++ err)
    Right () -> return ()
