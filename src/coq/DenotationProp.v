(* -------------------------------------------------------------------------- *
 *                     Vir - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith List String Omega.
Require Import ExtLib.Structures.Monads.

Require Import Vir.Util.
Require Import Vir.LLVMAst Vir.AstLib Vir.CFG Vir.CFGProp.
Require Import Vir.LLVMEvents Vir.Denotation.

Import MonadNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Module DenotationProp(A:MemoryAddress.ADDRESS)(LLVMIO:LLVM_INTERACTIONS(A)).
  Module SS := Denotation(A)(LLVMIO).
  Import SS.
  Import LLVMIO.DV.

  Section Properties.
  Definition is_Op {T} (i:instr T) : Prop :=
    match i with
    | INSTR_Op _ => True
    | _ => False
    end.

  Definition is_Eff {T} (i:instr T) : Prop :=
    match i with 
    | INSTR_Alloca t nb a => True
    | INSTR_Load v t p a => True
    | INSTR_Store v val p a => True
    | _ => False
    end.
  
  Definition is_Call {T} (i:instr T) : Prop :=
    match i with
    | INSTR_Call _ _ => True
    | _ => False
    end.
  End Properties.

End DenotationProp.  

