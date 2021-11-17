(* begin hide *)
Require Import String.

From ITree Require Import
     ITree
     Basics
     Basics.HeterogeneousRelations
     Eq.Eq.

From Vellvm Require Import
     Utilities
     Syntax
     Semantics
     Semantics.MemoryAddress
     Semantics.GepM
     Semantics.Memory.Sizeof
     Semantics.Memory.MemBytes
     Semantics.LLVMParams
     Semantics.Lang
     Handlers.OOM.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad
     Structures.Functor.


From Coq Require Import Relations RelationClasses.
(* end hide *)

Module Make (LP : LLVMParams) (LLVM : Lang LP).
  Import LP.
  Import LLVM.
  Import LLVM.MEM.

  Import DV.
  Import LLVM.SP.SER.

  (* Refinement relation for uvalues *)
  (* Definition 5.6 UValue refinement *)
  Variant refine_uvalue: uvalue -> uvalue -> Prop :=
    | UndefPoison: forall dt uv uv1, concretize uv1 (DVALUE_Poison dt) -> uvalue_has_dtyp uv dt -> refine_uvalue uv1 uv
    | RefineConcrete: forall uv1 uv2, (forall (dv:dvalue), concretize uv2 dv -> concretize uv1 dv) -> refine_uvalue uv1 uv2
  .
  #[export] Hint Constructors refine_uvalue : core.

  Definition uvalue_eq (uv1 uv2 : uvalue) : Prop
    := refine_uvalue uv1 uv2 /\ refine_uvalue uv2 uv1.

  Global Instance refine_uvalue_Reflexive : Reflexive refine_uvalue.
  Proof.
    repeat intro.
    destruct x; (apply RefineConcrete; solve [auto]).
  Qed.

  Global Instance uvalue_eq_Reflexive : Reflexive uvalue_eq.
  Proof.
    repeat intro.
    split; reflexivity.
  Qed.

  Lemma refine_uvalue_dtyp :
    forall uv1 uv2 dt,
      uvalue_has_dtyp uv1 dt ->
      refine_uvalue uv1 uv2 ->
      uvalue_has_dtyp uv2 dt.
  Proof.
    intros uv1 uv2 dt DTYP REF.
    induction DTYP.
    - inversion REF; subst.
  Admitted.

  Global Instance refine_uvalue_Transitive : Transitive refine_uvalue.
  Proof.
    repeat intro.
    inversion H; subst.
    - (* x concretizes to poison *)
      eapply UndefPoison; eauto.
      eapply refine_uvalue_dtyp; eauto.
    - (* x may not be poison  *)
      inversion H0; subst.
      + (* y is poison *)
        pose proof (H1 (DVALUE_Poison dt)) as POISON.
        forward POISON.
        auto.

        (* x refines to poison... *)
        eapply UndefPoison; eauto.
      + constructor.
        auto.
  Qed.

  Global Instance uvalue_eq_Transitive : Transitive uvalue_eq.
  Proof.
    intros x y z [Rxy Ryx] [Ryz Rzy].
    split; etransitivity; eauto.
  Qed.

  Global Instance uvalue_eq_Symmetric : Symmetric uvalue_eq.
  Proof.
    intros x y [Rxy Ryx].
    split; auto.
  Qed.

  Global Instance uvalue_eq_Equivalence : Equivalence uvalue_eq.
  Proof.
    split.
    - apply uvalue_eq_Reflexive.
    - apply uvalue_eq_Symmetric.
    - apply uvalue_eq_Transitive.
  Qed.

  Infix"×" := prod_rel (at level 90, left associativity).

  Definition TT {A} : relation A := fun _ _ => True.

  Global Instance TT_Reflexive {A} : Reflexive (@TT A).
  Proof.
    intro.
    reflexivity.
  Qed.

  (* Lemma 5.7 - uses this definition of refinement 
   note that refine_uvalue is the basic Uvalue refinement given by Definition 5.6 *)
  (* Refinement of uninterpreted mcfg *)
  Definition refine_L0: relation (itree L0 uvalue) := eutt refine_uvalue.

  (* Refinement of mcfg after globals *)
  Definition refine_res1 : relation (global_env * uvalue)
    := TT × refine_uvalue.

  Definition refine_L1 : relation (itree L1 (global_env * uvalue))
    := eutt refine_res1.

  (* Refinement of mcfg after locals *)
  Definition refine_res2 : relation (local_env * lstack * (global_env * uvalue))
    := TT × refine_res1.

  Definition refine_L2 : relation (itree L2 (local_env * stack * (global_env * uvalue)))
    := eutt refine_res2.

  (* For multiple CFG, after interpreting [LocalE] and [MemoryE] and [IntrinsicE] that are memory intrinsics *)
  Definition refine_res3 : relation (MemState * (local_env * stack * (global_env * uvalue)))
    := TT × refine_res2.

  Definition refine_L3 : relation (itree L3 (MemState * (local_env * stack * (global_env * uvalue))))
    := eutt refine_res3.

  (* Refinement for after interpreting pick. *)
  Definition refine_L4 : relation ((itree L4 (MemState * (local_env * stack * (global_env * uvalue)))) -> Prop)
    := fun ts ts' => forall t', ts' t' -> exists t, ts t /\ eutt refine_res3 t t'.

  Inductive contains_UB {R} : itree L4 R -> Prop :=
  | CrawlTau  : forall t, contains_UB t -> contains_UB (Tau t)
  | CrawlVis1 : forall Y (e : ExternalCallE Y) x k, contains_UB (k x) -> contains_UB (vis e k)
  | CrawlVis2 : forall Y (e : (DebugE +' FailureE) Y) x k, contains_UB (k x) -> contains_UB (vis e k)
  | FindUB    : forall s, contains_UB (raiseUB s).

  Definition refine_L5 : relation ((itree L4 (MemState * (local_env * stack * (global_env * uvalue)))) -> Prop)
    := fun ts ts' =>
         (* For any tree in the target set *)
         forall t', ts' t' ->
               (* There is a tree in the source set that either
                  exhibits UB, or is eutt our target tree *)
               exists t, ts t /\ (contains_UB t \/ eutt refine_res3 t t').

  Definition refine_L6 : relation ((itree L4 (MemState * (local_env * stack * (global_env * uvalue)))) -> Prop)
    := fun ts ts' =>
         forall t', ts' t' ->
               exists t, ts t /\ (contains_UB t \/ refine_OOM_h refine_res3 t t').

End Make.
