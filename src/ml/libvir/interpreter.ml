open Handlers.Mem
open Handlers.Local
open Handlers.Stack
open Handlers.Global
open Handlers.LLVMEvents

open Format
open ITreeDefinition
let pp_addr : Format.formatter -> Memory.Addr.addr -> unit
  = fun ppf _ -> fprintf ppf "UVALUE_Addr(?)"
let string_of_float_full f =
  let s = sprintf "%.350f" f in
  let open Str in
  Str.global_replace (Str.regexp "0+$") "" s

let rec pp_uvalue : Format.formatter -> DV.uvalue -> unit =
  let open Camlcoq in
  let pp_comma_space ppf () = pp_print_string ppf ", " in
  fun ppf ->
  function
  | UVALUE_Addr   x -> pp_addr ppf x
  | UVALUE_I1     x -> fprintf ppf "UVALUE_I1(%d)"  (Camlcoq.Z.to_int (DynamicValues.Int1.unsigned x))
  | UVALUE_I8     x -> fprintf ppf "UVALUE_I8(%d)"  (Camlcoq.Z.to_int (DynamicValues.Int8.unsigned x))
  | UVALUE_I32    x -> fprintf ppf "UVALUE_I32(%d)" (Camlcoq.Z.to_int (DynamicValues.Int32.unsigned x))
  | UVALUE_I64    x -> fprintf ppf "UVALUE_I64(%s)" (Int64.to_string (Z.to_int64 (DynamicValues.Int64.unsigned x)))
  | UVALUE_Double x -> fprintf ppf "UVALUE_Double(%s)" (string_of_float_full (camlfloat_of_coqfloat x))
  | UVALUE_Float  x -> fprintf ppf "UVALUE_Float(%s)"  (string_of_float_full (camlfloat_of_coqfloat32 x))
  | UVALUE_Poison   -> fprintf ppf "UVALUE_Poison"
  | UVALUE_None     -> fprintf ppf "UVALUE_None"
  | UVALUE_Undef _  -> fprintf ppf "UVALUE_Undef"
  | UVALUE_Struct        l -> fprintf ppf "UVALUE_Struct(%a)"        (pp_print_list ~pp_sep:pp_comma_space pp_uvalue) l
  | UVALUE_Packed_struct l -> fprintf ppf "UVALUE_Packet_struct(%a)" (pp_print_list ~pp_sep:pp_comma_space pp_uvalue) l
  | UVALUE_Array         l -> fprintf ppf "UVALUE_Array(%a)"         (pp_print_list ~pp_sep:pp_comma_space pp_uvalue) l
  | UVALUE_Vector        l -> fprintf ppf "UVALUE_Vector(%a)"        (pp_print_list ~pp_sep:pp_comma_space pp_uvalue) l
  | _ -> fprintf ppf "todo"

let debug_flag = ref false 
let debug (msg:string) =
  if !debug_flag then
    Printf.printf "DEBUG: %s\n%!" msg

let rec step (m : ('a coq_L5, memory_stack * ((local_env * lstack) * (global_env * DV.uvalue))) itree) : (DV.uvalue, string) result =
  let open ITreeDefinition in
  match observe m with
  | TauF x -> step x
  | RetF (_,(_,(_,v))) -> Ok v
  | VisF (Sum.Coq_inl1 (ExternalCall(_, _, _)), _) ->
     Error "Uninterpreted Call"
  | VisF (Sum.Coq_inr1 (Sum.Coq_inl1 msg), k) ->
        (debug (Camlcoq.camlstring_of_coqstring msg);
         step (k (Obj.magic DV.UVALUE_None)))
  | VisF (Sum.Coq_inr1 (Sum.Coq_inr1 f), _) ->
     Error (Camlcoq.camlstring_of_coqstring f)


let interpret (prog:(LLVMAst.typ, (LLVMAst.typ LLVMAst.block * (LLVMAst.typ LLVMAst.block) list)) LLVMAst.toplevel_entity list) : (DV.uvalue, string) result =
  step (TopLevel.interpreter prog)
