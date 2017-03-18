import Control.Monad.State.Lazy
import Control.Monad.Except
import Data.Char
import Data.List
import System.IO
import Text.Parsec (parse)
import Text.Parsec.Combinator (eof)
import System.Environment (getArgs)
import qualified Text.ParserCombinators.Parsec as Parsec

import qualified Parser
import Extracted (Program, Expr(..), Expr_hole(..), Heap, Value(..), Local_id(..), Frame, Ty(..), Cap(..), Ty_ctx)
import Extracted (Nmap, Pmap, Stringmap, list_expr_uncoerce)
import qualified Extracted

data ST = ST { stProg :: Program, stHeap :: Heap, stStack :: [Frame], stCtx :: Ty_ctx }
type Repl = StateT ST (ExceptT String IO)

tyctx_insert :: String -> Ty -> Ty_ctx -> Ty_ctx
tyctx_insert = Extracted.insert (Extracted.map_insert Extracted.stringmap_partial_alter)

((init_heap, init_stack), init_tyctx) = Extracted.init

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
  liftIO (print (Extracted.wf_program prog))
  liftIO (print prog)
  put (ST prog init_heap init_stack init_tyctx)

loadFile :: FilePath -> Repl ()
loadFile path = liftIO (readFile path) >>= load

parser :: Parser.P a -> String -> Repl a
parser p line =
  case parse (Parser.whiteSpace >> p <* Parser.whiteSpace <* eof) "<interactive>" line of
    Right e -> return e
    Left err -> throwError (show err)

ck_expr :: Expr -> Repl Ty
ck_expr expr = do
  (ST prog _ _ ctx) <- get

  case Extracted.ck_expr prog ctx expr of
    Just ty -> return ty
    Nothing -> throwError "typecheck error"

evaluate' :: Expr -> Repl Value
evaluate' expr = do
  (ST prog heap stack ctx) <- get
  liftIO . putStrLn $ show (length stack - 1) ++ ": " ++ show expr

  case (expr, stack) of
    (Expr_temp temp, [frame]) ->
      let Just x = Extracted.lookup (Extracted.frame_lookup Extracted.localmap_lookup_temp) temp frame in return x

    _ -> case Extracted.eval prog heap stack expr of
      Just ((heap', stack'), expr') -> put (ST prog heap' stack' ctx) >> evaluate' expr'
      Nothing -> throwError "eval error"

evaluate :: Expr -> Repl (Ty, Value)
evaluate expr = do
  ty <- ck_expr expr
  val <- evaluate' expr
  return (ty, val)

command :: String -> String -> Repl ()
command "heap" _ = do
  heap <- Extracted.heap_to_list <$> gets stHeap
  liftIO (mapM_ (\(x, o) -> putStrLn ("#" ++ show x ++ ": " ++ show o)) heap)

command "stack" _ = do
  stack <- gets stStack
  liftIO . print $ stack

command "ctx" _ = do
  ctx <- gets stCtx
  liftIO (print ctx)

command "reset" _ = do
    modify (\s -> s { stHeap = init_heap, stStack = init_stack })

command "parse" line = parser Parser.expr line >>= liftIO . print

command "load" "" = multiline >>= load
command "load" path = loadFile path

repl :: String -> Repl ()
repl "" = return ()
repl (':':line) =
  let (c, rest) = break isSpace line in
  command c (dropWhile isSpace rest)

repl ('l':'e':'t':' ':line) = do
  (x, ty, expr) <- parser parseLet line
  ty <- case (ty, expr) of
    (Just ty, _) -> return ty
    (Nothing, Just expr) -> ck_expr expr

  modify (\s -> s { stCtx = tyctx_insert x ty (stCtx s) })
  case expr of
    Just expr -> evaluate (Expr_assign_local x expr) >> return ()
    Nothing -> return ()

  where
    parseLet = do
      x <- Parser.identifier
      ty <- Parsec.optionMaybe (Parser.colon >> Parser.ty)
      expr <- Parsec.optionMaybe (Parser.reservedOp "=" >> Parser.expr)
      return (x, ty, expr)

repl line = do
  e <- parser Parser.expr line
  (ty, value) <- evaluate e
  heap <- gets stHeap

  let desc =
       case value of
        V_null -> "null"
        V_addr addr ->
          let (Just object) = Extracted.lookup Extracted.nlookup addr heap
          in show object

  liftIO $ putStrLn (desc ++ " : " ++ show ty)

main :: IO ()
main = do
  args <- getArgs
  result <- runExceptT . flip evalStateT (ST ((([],[]),[]),[]) init_heap init_stack init_tyctx) $ do
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
