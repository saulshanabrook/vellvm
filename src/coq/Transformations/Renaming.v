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
     ZArith Ascii Strings.String Setoid Morphisms List.

From ITree Require Import
     ITree
     Eq.Eq
     Interp.Interp
     Interp.InterpFacts
     Interp.TranslateFacts
     Basics.MonadState
     Events.StateFacts.

From Vir Require Import
     Error
     Util
     LLVMAst
     AstLib
     CFG
     DynamicTypes
     DynamicValues
     Denotation
     Handlers.Handlers
     LLVMEvents
     Transformations.Transformation
     Traversal
     TopLevelRefinements.

From ExtLib Require Import
     Programming.Eqv
     Structures.Monads.

Import EqvNotation.

Open Scope Z_scope.
Open Scope string_scope.

From Vir Require Import
     AstLib.
Import ListNotations.

Import DV.
Import R.

Import MonadNotation.

Section Swap.

  (* Class Swap (A:Type) := swap : raw_id -> raw_id -> A -> A. *)

  Variable id1 id2: raw_id.

  Definition swap_raw_id (id:raw_id) : raw_id :=
    if id ~=? id1 then id2 else
      if id ~=? id2 then id1 else
        id.

  Instance swap_endo_raw_id : Endo raw_id := swap_raw_id.

  Definition swap_mcfg: transformation := endo.
  Definition swap_dmcfg: Endo (mcfg dtyp) := endo.

  (*
    For now we forget about normalization of types, we reason after it happened.
    I'll see how to plug it back in the story later.
  Lemma normalize_types_swap: forall p,
      normalize_types (swap_mcfg p) = swap_dmcfg (normalize_types p).
  Proof.
  Admitted.
   *)
  Ltac split_bind := apply eutt_clo_bind with (UU := Logic.eq); [| intros ? (? & ? & ?) ->].

  (** Logical relation for the [list] type. *)
  Inductive list_rel {A1 A2 : Type}
            (RA : A1 -> A2 -> Prop) : (list A1) -> (list A2) -> Prop :=
  | list_rel_nil: list_rel RA [] []
  | list_rel_cons: forall a1 a2 tl1 tl2, RA a1 a2 -> list_rel RA tl1 tl2 -> list_rel RA (a1 :: tl1) (a2 :: tl2)
  .
  Hint Constructors list_rel : core.

  (* In top-level, [address_one_function] is mapped to return notably a mapping from function addresses to itrees.
     We hence want to get extensional eutt over the returned type.
   *)
  Definition function_rel {X}:
    relation (FMapAList.alist raw_id uvalue * @Stack.stack X * (FMapAList.alist raw_id dvalue * list (uvalue * (list uvalue -> itree L0 uvalue)))) := (Logic.eq × (Logic.eq × list_rel (refine_uvalue × (fun d1 d2 => forall x, eutt refine_uvalue (d1 x) (d2 x))))).
  Hint Unfold function_rel : core.

  Global Instance list_rel_refl {R: Type} {RR: relation R} `{Reflexive _ RR} : Reflexive (list_rel RR).
  Proof.
    intros l; induction l as [| hd tl IH]; auto.
  Qed.

  Global Instance function_rel_refl {X}: Reflexive (@function_rel X).
  Proof.
    repeat apply prod_rel_refl; auto.
    eapply list_rel_refl.
    Unshelve.
    apply prod_rel_refl; auto. apply refine_uvalue_Reflexive.
    intros ? ?.
    reflexivity.
  Qed.

  (*
  (* Calvin broke this somehow by changing uvalue to not include
     CallE. Yannick promises not to be mad later when fixing this. :) *)
  Lemma interp_to_L2_map_monad: forall {X} (f: X -> itree _ (uvalue * D.function_denotation)) (g: endo X) (l: list X) s1 s2,
      (forall x s1 s2, In x l -> eutt (Logic.eq × (Logic.eq × (refine_uvalue × (fun d1 d2 => forall x, eutt refine_uvalue (d1 x) (d2 x))))) (interp_to_L2 nil (f x) s1 s2) (interp_to_L2 nil (f (g x)) s1 s2)) ->
      eutt function_rel (interp_to_L2 nil (map_monad f l) s1 s2) (interp_to_L2 nil (map_monad f (map g l)) s1 s2).
  Proof.
    induction l as [| x l IH]; simpl; intros; [reflexivity |].
    rewrite 2 interp_to_L2_bind.
    eapply eutt_clo_bind; eauto.
    intros (? & ? & ? & ?) (? & ? & ? & ?) EQ.
    repeat match goal with | h: prod_rel _ _ _ _ |- _ => inv h end.
    rewrite 2 interp_to_L2_bind.
    eapply eutt_clo_bind; eauto.
    intros (? & ? & ?) (? & ? & ?) EQ.
    inv EQ.
    repeat match goal with | h: prod_rel _ _ _ _ |- _ => inv h end.
    rewrite 2 interp_to_L2_ret.
    apply eqit_Ret.
    constructor; auto.
  Qed.
  *)

  Lemma swap_correct_L2:
    forall dt entry args intrinsics p, refine_mcfg_L2 dt entry args intrinsics p (swap_mcfg p).
  Proof.
    intros p.
    unfold refine_mcfg_L2.
    unfold model_to_L2.

    (* unfold denote_vir. *)
    (* unfold denote_vir_init. *)

    {
      admit.
    }
  Admitted.

  Theorem swap_cfg_correct: transformation_correct swap_mcfg.
  Proof.
    unfold transformation_correct.
    intros dt entry args intrinsics m. 
    apply refine_mcfg_L2_correct, swap_correct_L2.
  Qed.

End Swap.
