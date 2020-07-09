(* -------------------------------------------------------------------------- *
 *                     Vir - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

From Coq Require Import
     ZArith
     List
     String
     Setoid
     Morphisms
     Omega
     Classes.RelationClasses.

From ExtLib Require Import
     Core.RelDec
     Programming.Eqv
     Structures.Monads.

From ITree Require Import
     ITree
     Events.Exception.

From Vir Require Import
     Util
     LLVMAst
     MemoryAddress
     DynamicTypes
     DynamicValues
     Error.

(****************************** LLVM Events *******************************)
(**
   Vir's semantics relies on _Interaction Trees_, a generic data-structure allowing to model
   effectful computations.
   This file defined the interface provided to the interaction trees, that is the set of
   events that a LLVM program can trigger.
   These events are then concretely interpreted as a succession of handler, as defined in the
   _Handlers_ folder.
   The possible events are:
   * Function calls [CallE]
   * Calls to intrinsics whose implementation _do not_ depends on the memory [IntrinsicE]
   * Interactions with the global environment [GlobalE]
   * Interactions with the local environment [LocalE]
   * Manipulation of the frame stack for local environments [StackE]
   * Interactions with the memory [MemoryE]
   * Concretization of a under-defined value [PickE]
   * Undefined behaviour [UBE]
   * Failure [FailureE]
   * Debugging messages [DebugE]
*)

Set Implicit Arguments.
Set Contextual Implicit.
  Variant GlobalE (k v:Type) : Type -> Type :=
  | GlobalWrite (id: k) (dv: v): GlobalE k v unit
  | GlobalRead  (id: k): GlobalE k v v.
  Variant LocalE (k v:Type) : Type -> Type :=
  | LocalWrite (id: k) (dv: v): LocalE k v unit
  | LocalRead  (id: k): LocalE k v v.

  Variant StackE (k v:Type) : Type -> Type :=
  | StackPush (args: list (k * v)) : StackE k v unit
  | StackPop : StackE k v unit.
  Variant UBE : Type -> Type :=
  | ThrowUB : string -> UBE void.
  Definition raiseUB {E : Type -> Type} `{UBE -< E} {X}
             (e : string)
    : itree E X
    := vis (ThrowUB e) (fun v : void => match v with end).
  Variant DebugE : Type -> Type :=
  | Debug : string -> DebugE unit.
  Definition debug {E} `{DebugE -< E} (msg : string) : itree E unit :=
    trigger (Debug msg).

  Definition FailureE := exceptE string.

  Definition raise {E} {A} `{FailureE -< E} (msg : string) : itree E A :=
    throw msg.

  Definition lift_err {A B} {E} `{FailureE -< E} (f : A -> itree E B) (m:err A) : itree E B :=
    match m with
    | inl x => throw x
    | inr x => f x
    end.

  Definition lift_pure_err {A} {E} `{FailureE -< E} (m:err A) : itree E A :=
    lift_err ret m.

  Definition lift_undef_or_err {A B} {E} `{FailureE -< E} `{UBE -< E} (f : A -> itree E B) (m:undef_or_err A) : itree E B :=
    match m with
    | mkEitherT m =>
      match m with
      | inl x => raiseUB x
      | inr (inl x) => throw x
      | inr (inr x) => f x
      end
    end.
Module Type LLVM_INTERACTIONS (ADDR : MemoryAddress.ADDRESS).

  Global Instance eq_dec_addr : RelDec (@eq ADDR.addr) := RelDec_from_dec _ ADDR.eq_dec.
  Global Instance Eqv_addr : Eqv ADDR.addr := (@eq ADDR.addr).

  Module DV := DynamicValues.DVALUE(ADDR).
  Export DV.
  Variant CallE : Type -> Type :=
  | Call        : forall (t:dtyp) (f:uvalue) (args:list uvalue), CallE uvalue.

  Variant ExternalCallE : Type -> Type :=
  | ExternalCall        : forall (t:dtyp) (f:uvalue) (args:list dvalue), ExternalCallE dvalue.
  Variant IntrinsicE : Type -> Type :=
  | Intrinsic : forall (t:dtyp) (f:string) (args:list dvalue), IntrinsicE dvalue.
  Variant MemoryE : Type -> Type :=
  | MemPush : MemoryE unit
  | MemPop  : MemoryE unit
  | Alloca  : forall (t:dtyp),                               (MemoryE dvalue)
  | Load    : forall (t:dtyp)   (a:dvalue),                  (MemoryE uvalue)
  | Store   : forall (a:dvalue) (v:dvalue),                  (MemoryE unit)
  | GEP     : forall (t:dtyp)   (v:dvalue) (vs:list dvalue), (MemoryE dvalue)
  | ItoP    : forall (i:dvalue),                             (MemoryE dvalue)
  | PtoI    : forall (t:dtyp) (a:dvalue),                    (MemoryE dvalue)
  .
  Variant PickE : Type -> Type :=
  | pick (u:uvalue) (P : Prop) : PickE dvalue.

  Definition unique_prop (uv : uvalue) : Prop
    := exists x, forall dv, concretize uv dv -> dv = x.

  Definition pickAll (p : uvalue -> PickE dvalue) := map_monad (fun uv => trigger (p uv)).
  Definition LLVMGEnvE := (GlobalE raw_id dvalue).
  Definition LLVMEnvE := (LocalE raw_id uvalue).
  Definition LLVMStackE := (StackE raw_id uvalue).

  Definition conv_E := MemoryE +' PickE +' UBE +' DebugE +' FailureE.
  Definition lookup_E := LLVMGEnvE +' LLVMEnvE.
  Definition exp_E := LLVMGEnvE +' LLVMEnvE +' MemoryE +' PickE +' UBE +' DebugE +' FailureE.

  Definition lookup_E_to_exp_E : lookup_E ~> exp_E :=
    fun T e =>
      match e with
      | inl1 e => inl1 e
      | inr1 e => inr1 (inl1 e)
      end.

  Definition conv_E_to_exp_E : conv_E ~> exp_E :=
    fun T e => inr1 (inr1 e).

  Definition instr_E := CallE +' IntrinsicE +' exp_E.
  Definition exp_E_to_instr_E : exp_E ~> instr_E:=
    fun T e => inr1 (inr1 e).
  Definition L0' := CallE +' ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickE +' UBE +' DebugE +' FailureE.

  Definition instr_E_to_L0' : instr_E ~> L0' :=
    fun T e =>
      match e with
      | inl1 e => inl1 e
      | inr1 (inl1 e) => inr1 (inr1 (inl1 e))
      | inr1 (inr1 (inl1 e)) => inr1 (inr1 (inr1 (inl1 e)))
      | inr1 (inr1 (inr1 (inl1 e))) => inr1 (inr1 (inr1 (inr1 (inl1 (inl1 e)))))
      | inr1 (inr1 (inr1 (inr1 e))) => inr1 (inr1 (inr1 (inr1 (inr1 e))))
      end.

  Definition _exp_E_to_L0' : exp_E ~> L0' :=
    fun T e => instr_E_to_L0' (exp_E_to_instr_E e).

  Definition _failure_UB_to_ExpE : (FailureE +' UBE) ~> exp_E :=
    fun T e =>
      match e with
      | inl1 x => inr1 (inr1 (inr1 (inr1 (inr1 (inr1 x)))))
      | inr1 x => inr1 (inr1 (inr1 (inr1 (inl1 x))))
      end.

  Definition L0 := ExternalCallE +' IntrinsicE +' LLVMGEnvE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickE +' UBE +' DebugE +' FailureE.

  Definition _exp_E_to_L0 : exp_E ~> L0 :=
    fun T e =>
      match e with
      | inl1 e => inr1 (inr1 (inl1 e))
      | inr1 (inl1 e) => inr1 (inr1 (inr1 (inl1 (inl1 e))))
      | inr1 (inr1 e) => inr1 (inr1 (inr1 (inr1 e)))
      end.
  Definition L1 := ExternalCallE +' IntrinsicE +' (LLVMEnvE +' LLVMStackE) +' MemoryE +' PickE +' UBE +' DebugE +' FailureE.
  Definition L2 := ExternalCallE +' IntrinsicE +' MemoryE +' PickE +' UBE +' DebugE +' FailureE.
  Definition L3 := ExternalCallE +' PickE +' UBE +' DebugE +' FailureE.
  Definition L4 := ExternalCallE +' UBE +' DebugE +' FailureE.

  Definition L5 := ExternalCallE +' DebugE +' FailureE.

  Hint Unfold L0 L0' L1 L2 L3 L4 L5 : core.

  Definition _failure_UB_to_L4 : (FailureE +' UBE) ~> L4:=
    fun T e =>
      match e with
      | inl1 x => inr1 (inr1 (inr1 x))
      | inr1 x => inr1 (inl1 x)
      end.

End LLVM_INTERACTIONS.

Module Make(ADDR : MemoryAddress.ADDRESS) <: LLVM_INTERACTIONS(ADDR).
Include LLVM_INTERACTIONS(ADDR).
End Make.
