open Handlers.Mem
open Handlers.Local
open Handlers.Stack
open Handlers.Global
open Handlers.LLVMEvents
open ITreeDefinition

val pp_addr : Format.formatter -> Memory.Addr.addr -> unit

val pp_uvalue : Format.formatter -> DV.uvalue -> unit

val interpret: ((LLVMAst.typ, LLVMAst.typ LLVMAst.block * (LLVMAst.typ LLVMAst.block) list) LLVMAst.toplevel_entity) list -> (DV.uvalue, string) result

val step : ('a coq_L5, memory_stack * ((local_env * lstack) * (global_env * DV.uvalue))) itree -> (DV.uvalue, string) result

val debug_flag: bool ref
