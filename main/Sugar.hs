module Sugar where

import Extracted (Expr(..), Ty(..), Cap(..), Ecap(..), Program(..), list_expr_coerce, list_expr_uncoerce)
import Extracted (Field, Func, Func_stub, Behv, Behv_stub, Ctor, Ctor_stub, Class, Iface, Trait)

default_ctor :: Program -> Program
default_ctor = modify_class (modify_ctor_list (\ks -> if null ks then default_ks else ks))
  where
    default_ks :: [Ctor]
    default_ks = [("create", ([], Expr_local "this"))]

implicit_this :: Program -> Program
implicit_this = modify_class mod_class
  where
    mod_class :: Class -> Class
    mod_class (c, (((fs, ks), ms), is)) =
      (c, (((fs, map (mod_ctor (map fst fs)) ks), map (mod_func (map fst fs)) ms), is))

    mod_ctor :: [String] -> Ctor -> Ctor
    mod_ctor fs (k, (args, expr)) = (k, (args, modify_expr (mod_expr fs (map fst args)) expr))

    mod_func :: [String] -> Func -> Func
    mod_func fs (k, (((reccap, args), retty), expr)) = (k, (((reccap, args), retty), modify_expr (mod_expr fs (map fst args)) expr))

    mod_expr fs args (Expr_local x) = if elem x fs && not (elem x args) then Expr_field (Expr_local "this") x else (Expr_local x)
    mod_expr fs args (Expr_assign_local x e) = if elem x fs && not (elem x args) then Expr_assign_field (Expr_local "this") x e else (Expr_assign_local x e)
    mod_expr fs args e = e

ctor_trailing_this :: Program -> Program
ctor_trailing_this = modify_class (modify_ctor_list (map (\(k, (args, expr)) -> (k, (args, mod_body expr)))))
  where
    mod_body (Expr_seq e1 e2) = (Expr_seq e1 (mod_body e2))
    mod_body (Expr_local "this") = (Expr_local "this") 
    mod_body e = (Expr_seq e (Expr_local "this"))

desugar :: Program -> Program
desugar = default_ctor . ctor_trailing_this . implicit_this

modify_class :: (Class -> Class) -> Program -> Program
modify_class f (((nts, sts), cts), ats) = (((nts, sts), map f cts), ats)

modify_ctor_list :: ([Ctor] -> [Ctor]) -> Class -> Class
modify_ctor_list f (c, (((fs, ks), ms), is)) = (c, (((fs, f ks), ms), is))

modify_expr :: (Expr -> Expr) -> Expr -> Expr
modify_expr f e = case f e of
  Expr_temp t -> Expr_temp t
  Expr_null -> Expr_null
  Expr_seq e1 e2 -> Expr_seq (modify_expr f e1) (modify_expr f e2)
  Expr_recover e -> Expr_recover (modify_expr f e)
  Expr_local x -> Expr_local x
  Expr_assign_local x e -> Expr_assign_local x (modify_expr f e)
  Expr_field e fld -> Expr_field (modify_expr f e) fld
  Expr_assign_field e0 fld e1 -> Expr_assign_field (modify_expr f e0) fld (modify_expr f e1)
  Expr_call e0 n es -> Expr_call (modify_expr f e0) n (list_expr_coerce . map (modify_expr f) . list_expr_uncoerce $ es)
  Expr_ctor kt k es -> Expr_ctor kt k (list_expr_coerce . map (modify_expr f) . list_expr_uncoerce $ es)

