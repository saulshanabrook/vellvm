From ITree Require Import
     ITree
     Basics
     Eq.Eq.

From Vir Require Import
     Util
     UndefinedBehaviour
     DynamicValues
     MemoryAddress
     LLVMEvents
     LLVMAst
     Handlers.Handlers.

From ExtLib Require Import
     Structures.Monads
     Data.Monads.EitherMonad
     Structures.Functor.


From Coq Require Import Relations RelationClasses.

Module Make (A:MemoryAddress.ADDRESS)(LLVMEvents: LLVM_INTERACTIONS(A)).

Import LLVMEvents.
Import DV.
Variant refine_uvalue: uvalue -> uvalue -> Prop :=
| UndefPoison: forall uv, refine_uvalue UVALUE_Poison uv
| RefineConcrete: forall uv1 uv2, uv2 <> UVALUE_Poison -> (forall (dv:dvalue), concretize uv2 dv -> concretize uv1  dv) -> refine_uvalue uv1 uv2
.
Hint Constructors refine_uvalue : core.

Instance refine_uvalue_Reflexive : Reflexive refine_uvalue.
Proof.
  repeat intro.
  destruct x; try (apply RefineConcrete;[intro; inversion H|auto];fail).
  apply UndefPoison.
Qed.

Lemma refine_poison : forall uv, refine_uvalue uv UVALUE_Poison -> uv = UVALUE_Poison.
Proof.
  intros.
  inv H.
  - reflexivity.
  - contradiction H0.
    reflexivity.
Qed.

Instance refine_uvalue_Transitive : Transitive refine_uvalue.
Proof.
  repeat intro.
  inversion H; subst.
  - inversion H0; subst.
    econstructor.
    econstructor.
  - inversion H0; subst.
    apply refine_poison in H. subst. econstructor.
    apply RefineConcrete. intros. assumption. auto. 
Qed.

Infix"×" := prod_rel (at level 90, left associativity).

Definition TT {A} : relation A := fun _ _ => True.
Definition refine_L0: relation (itree L0 uvalue) := eutt refine_uvalue.
Definition refine_res1 : relation (global_env * uvalue)
  := TT × refine_uvalue.

Definition refine_L1 : relation (itree L1 (global_env * uvalue))
  := eutt refine_res1.
Definition refine_res2 : relation (local_env * lstack * (global_env * uvalue))
  := TT × refine_res1.

Definition refine_L2 : relation (itree L2 (local_env * stack * (global_env * uvalue)))
  := eutt refine_res2.
Definition refine_res3 : relation (memory_stack * (local_env * stack * (global_env * uvalue)))
  := TT × refine_res2.

Definition refine_L3 : relation (itree L3 (memory_stack * (local_env * stack * (global_env * uvalue))))
  := eutt refine_res3.
Definition refine_L4 : relation ((itree L4 (memory_stack * (local_env * stack * (global_env * uvalue)))) -> Prop)
  := fun ts ts' => forall t', ts' t' -> exists t, ts t /\ eutt refine_res3 t t'.

Definition refine_L5 : relation ((itree L5 (memory_stack * (local_env * stack * (global_env * uvalue)))) -> Prop)
  := fun ts ts' => forall t', ts' t' -> exists t, ts t /\ eutt refine_res3 t t'.

End Make.
