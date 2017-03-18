{-# OPTIONS_GHC -cpp -XMagicHash #-}
{-# LANGUAGE StandaloneDeriving #-}

{- For Hugs, use the option -F"cpp -P -traditional" -}

module Extracted where
import qualified Prelude

import qualified GHC.Base
import qualified GHC.Prim
import qualified Data.Bits
import qualified Data.Char
import qualified Debug.Trace

import Prelude (Show, (.), ($), show, (++), concat)
import Data.List (intersperse)

deriving instance Show Local_id
deriving instance Show Frame

instance Show Expr_hole where
  show Expr_hole_id = "\x00B7"
  show (Expr_hole_seq e1 e2) = show e1 ++ "; " ++ show e2
  show (Expr_hole_recover e) = "recover " ++ show e
  show (Expr_hole_assign_local n e) = n ++ " = " ++ show e
  show (Expr_hole_field e n) = show e ++ "." ++ n
  show (Expr_hole_assign_field1 e1 n e2) = show e1 ++ "." ++ n ++ " = " ++ show e2
  show (Expr_hole_assign_field2 e1 n t) = show e1 ++ "." ++ n ++ " = $" ++ show t
  show (Expr_hole_call1 e0 n ts e es) = show e0 ++ "." ++ n ++ "(" ++ (concat . intersperse ", " $ (Prelude.map (\t -> "$"++show t) ts ++ [show e] ++ Prelude.map show (list_expr_uncoerce es))) ++ ")"
  show (Expr_hole_call2 e0 n ts) = show e0 ++ "." ++ n ++ "(" ++ (concat . intersperse ", " . Prelude.map (\t -> "$"++show t) $ ts) ++ ")"
  show (Expr_hole_ctor n m ts e es) = n ++ "." ++ m ++ "(" ++ (concat . intersperse ", " $ (Prelude.map (\t -> "$"++show t) ts ++ [show e] ++ Prelude.map show (list_expr_uncoerce es))) ++ ")"

instance Show Expr where
  show (Expr_temp t) = "$" ++ show t
  show (Expr_null) = "null"
  show (Expr_seq e1 e2) = show e1 ++ "; " ++ show e2
  show (Expr_recover e) = "recover " ++ show e
  show (Expr_local n) = n
  show (Expr_assign_local n e) = n ++ " = " ++ show e
  show (Expr_field e n) = show e ++ "." ++ n
  show (Expr_assign_field e1 n e2) = show e1 ++ "." ++ n ++ " = " ++ show e2
  show (Expr_call e1 n es) = show e1 ++ "." ++ n ++ "(" ++ (concat . intersperse ", " . Prelude.map show . list_expr_uncoerce $ es) ++ ")"
  show (Expr_ctor n m es) = n ++ "." ++ m ++ "(" ++ (concat . intersperse ", " . Prelude.map show . list_expr_uncoerce $ es) ++ ")"
  
instance Show Value where
  show V_null = "null"
  show (V_addr addr) = "#" ++ show (Extracted.n_to_nat addr)

instance Show Extracted.Cap where
  show Extracted.Cap_iso = "iso"
  show Extracted.Cap_tag = "tag"
  show Extracted.Cap_ref = "ref"

instance Show Extracted.Ecap where
  show Extracted.Cap_iso_eph = "iso^"
  show (Extracted.Ecap_cap c) = show c

instance Show Extracted.Ty where
  show (Extracted.Ty_name name cap) = name ++ " " ++ show cap
  show (Extracted.Ty_null) = "null"

instance Show Extracted.Object where
  show (Extracted.Build_object name fields) =
    name ++ " { " ++ concat (intersperse ", " (Prelude.map (\(k,v) -> k ++ ": " ++ show v ) (Extracted.fields_to_list fields))) ++ " }"

instance Show Extracted.N where
  show = show . Extracted.n_to_nat

instance Show Extracted.Positive where
  show = show . Extracted.p_to_nat

instance (Show a) => Show (Stringmap a) where
  show = show . Extracted.map_to_list Extracted.stringmap_to_list 

instance (Show a) => Show (Nmap a) where
  show = show . Extracted.map_to_list Extracted.nto_list 

instance (Show a) => Show (Pmap a) where
  show = show . Extracted.map_to_list Extracted.pto_list 

