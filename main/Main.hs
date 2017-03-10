{-# LANGUAGE StandaloneDeriving #-}

import Control.Monad.State.Lazy
import Control.Monad.Except
import Data.Char
import Data.List
import System.IO
import Text.Parsec (parse)
import Text.Parsec.Combinator (eof)
import System.Environment (getArgs)

import qualified Parser
import Extracted (Program, List_expr, Expr(..), Expr_hole(..), Heap, Value(..), Local_id(..), Frame)
import Extracted (Nmap, Pmap, Stringmap, list_expr_uncoerce)
import qualified Extracted

deriving instance Show Local_id
deriving instance Show Extracted.Def
deriving instance Show Extracted.Item
deriving instance Show Extracted.Item_stub
deriving instance Show List_expr
deriving instance Show Frame

instance Show Expr_hole where
  show Expr_hole_id = "\x00B7"
  show (Expr_hole_seq e1 e2) = show e1 ++ "; " ++ show e2
  show (Expr_hole_recover e) = "recover " ++ show e
  show (Expr_hole_assign_local n e) = n ++ " = " ++ show e
  show (Expr_hole_field e n) = show e ++ "." ++ n
  show (Expr_hole_assign_field1 e1 n e2) = show e1 ++ "." ++ n ++ " = " ++ show e2
  show (Expr_hole_assign_field2 e1 n t) = show e1 ++ "." ++ n ++ " = " ++ show t
  show (Expr_hole_call1 e0 n ts e es) = show e0 ++ "." ++ n ++ "(" ++ (concat . intersperse ", " $ (map show ts ++ [show e] ++ map show (list_expr_uncoerce es))) ++ ")"
  show (Expr_hole_call2 e0 n ts) = show e0 ++ "." ++ n ++ "(" ++ (concat . intersperse ", " . map show $ ts) ++ ")"
  show (Expr_hole_ctor n m ts e es) = n ++ "." ++ m ++ "(" ++ (concat . intersperse ", " $ (map show ts ++ [show e] ++ map show (list_expr_uncoerce es))) ++ ")"

instance Show Expr where
  show (Expr_temp t) = show t
  show (Expr_seq e1 e2) = show e1 ++ "; " ++ show e2
  show (Expr_recover e) = "recover " ++ show e
  show (Expr_local n) = n
  show (Expr_assign_local n e) = n ++ " = " ++ show e
  show (Expr_field e n) = show e ++ "." ++ n
  show (Expr_assign_field e1 n e2) = show e1 ++ "." ++ n ++ " = " ++ show e2
  show (Expr_call e1 n es) = show e1 ++ "." ++ n ++ "(" ++ (concat . intersperse ", " . map show . list_expr_uncoerce $ es) ++ ")"
  show (Expr_ctor n m es) = n ++ "." ++ m ++ "(" ++ (concat . intersperse ", " . map show . list_expr_uncoerce $ es) ++ ")"
  
instance Show Value where
  show V_null = "null"
  show (V_addr addr) = "#" ++ show (Extracted.n_to_nat addr)

instance Show Extracted.Object where
  show (Extracted.Build_object name fields) =
    name ++ " { " ++ concat (intersperse ", " (map (\(k,v) -> k ++ ": " ++ show v ) (Extracted.fields_to_list fields))) ++ " }"

instance Show (Extracted.N) where
  show = show . Extracted.n_to_nat

instance Show (Extracted.Positive) where
  show = show . Extracted.p_to_nat

instance (Show a) => Show (Stringmap a) where
  show = show . Extracted.map_to_list Extracted.stringmap_to_list 

instance (Show a) => Show (Nmap a) where
  show = show . Extracted.map_to_list Extracted.nto_list 

instance (Show a) => Show (Pmap a) where
  show = show . Extracted.map_to_list Extracted.pto_list 


data ST = ST { stProg :: Program, stHeap :: Heap, stStack :: [Frame] }
type Repl = StateT ST (ExceptT String IO)

(init_heap, init_stack) = Extracted.init

multiline :: Repl String
multiline = liftIO (multiline' [])
  where
    multiline' acc = do
      putStr "| " >> hFlush stdout
      line <- getLine

      if null line then return (unlines (reverse acc))
      else multiline' (line : acc)

load :: String -> Repl ()
load contents = do
  prog <- parser Parser.prog contents
  liftIO (print prog)
  put (ST prog init_heap init_stack)

loadFile :: FilePath -> Repl ()
loadFile path = liftIO (readFile path) >>= load

parser :: Parser.P a -> String -> Repl a
parser p line =
  case parse (Parser.whiteSpace >> p <* Parser.whiteSpace <* eof) "<interactive>" line of
    Right e -> return e
    Left err -> throwError (show err)

evaluate :: Expr -> Repl Value
evaluate expr = do
  (ST prog heap stack) <- get
  -- liftIO . putStr . unlines  $ map (("- "++) . show) stack ++ ["  " ++ show expr]

  case (expr, stack) of
    (Expr_temp temp, [frame]) ->
      let Just x = Extracted.lookup (Extracted.frame_lookup Extracted.localmap_lookup_temp) temp frame in return x
    _ -> case Extracted.eval prog heap stack expr of
      Just ((heap', stack'), expr') -> put (ST prog heap' stack') >> evaluate expr'
      Nothing -> throwError "eval error"

command :: String -> String -> Repl ()
command "heap"  _ = do
  heap <- Extracted.heap_to_list <$> gets stHeap
  liftIO (mapM_ (\(x, o) -> putStrLn ("#" ++ show x ++ ": " ++ show o)) heap)

{-command "stack"  _ = do-}
  {-stack <- Extracted.heap_to_list <$> gets stStack-}


command "reset" _ = do
    modify (\s -> s { stHeap = init_heap, stStack = init_stack })

command "parse" line = parser Parser.expr line >>= liftIO . print

command "parse_def" line = parser Parser.def line >>= liftIO . print
command "parse_item" line = parser Parser.item line >>= liftIO . print

command "load" "" = multiline >>= load
command "load" path = loadFile path

repl :: String -> Repl ()
repl "" = return ()
repl (':':line) =
  let (c, rest) = break isSpace line in
  command c (dropWhile isSpace rest)

repl line = do
  e <- parser Parser.expr line
  value <- evaluate e
  heap <- gets stHeap

  case value of
    V_null -> liftIO (putStrLn "null")
    V_addr addr ->
      let (Just object) = Extracted.lookup Extracted.nlookup addr heap
      in liftIO (print object)

main :: IO ()
main = do
  args <- getArgs
  result <- runExceptT . flip evalStateT (ST [] init_heap init_stack) $ do
    prog <- case args of
      [] -> return ()
      (path : _) -> loadFile path

    forever $ do
      liftIO (putStr "> " >> hFlush stdout)
      line <- liftIO getLine
      catchError (repl line) (\err -> liftIO (putStrLn err))

  case result of
    Left err -> putStrLn ("Fatal error:" ++ err)
    Right () -> return ()
