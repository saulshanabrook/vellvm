From Coq Require Import
     ZArith List String Morphisms.

From ExtLib Require Import
     Structures.Monads
     Programming.Eqv
     Data.String.

From Vir Require Import
     Util
     LLVMAst
     LLVMEvents
     Error
     IntrinsicsDefinitions.

From ITree Require Import
     ITree
     InterpFacts
     Eq.Eq.

Import MonadNotation.
Import EqvNotation.
Import ListNotations.


Set Implicit Arguments.
Set Contextual Implicit.
Definition intrinsic_ident (id:ident) : option string :=
  match id with
  | ID_Global (Name s) =>
    if String.prefix "llvm." s then Some s else None
  | _ => None
  end.

Definition intrinsic_exp {T} (e:exp T) : option string :=
  match e with
  | EXP_Ident id => intrinsic_ident id
  | _ => None
  end.
Module Make(A:MemoryAddress.ADDRESS)(LLVMIO: LLVM_INTERACTIONS(A)).

  Module IS := IntrinsicsDefinitions.Make(A)(LLVMIO).
  Include IS.
  Import LLVMIO.
  Import DV.

  Definition defs_assoc (user_intrinsics: intrinsic_definitions) := List.map (fun '(a,b) =>
                                  match dc_name a with
                                  | Name s => (s,b)
                                  | _ => ("",b)
                                  end
                               ) (user_intrinsics ++ defined_intrinsics).

  Definition handle_intrinsics {E} `{FailureE -< E} `{IntrinsicE -< E}
             (user_intrinsics: intrinsic_definitions) : IntrinsicE ~> itree E :=
    fun X (e : IntrinsicE X) =>
      match e in IntrinsicE Y return X = Y -> itree E Y with
      | (Intrinsic _ fname args) =>
          match assoc fname (defs_assoc user_intrinsics) with
          | Some f => fun pf =>
                       match f args with
                       | inl msg => raise msg
                       | inr result => Ret result
                       end
          | None => fun pf => (eq_rect X (fun a => itree E a) (trigger e)) dvalue pf
          end
      end eq_refl.

  Section PARAMS.
    Variable (E F : Type -> Type).
    Context `{FailureE -< F}.
    Notation Eff := (E +' IntrinsicE +' F).

    Definition E_trigger : Handler E Eff := fun _ e => trigger e.
    Definition F_trigger : Handler F Eff := fun _ e => trigger e.

    Definition interp_intrinsics_h (user_intrinsics: intrinsic_definitions) :=
      (case_ E_trigger (case_ (handle_intrinsics user_intrinsics) F_trigger)).

    Definition interp_intrinsics (user_intrinsics: intrinsic_definitions):
      forall R, itree Eff R -> itree Eff R :=
      interp (interp_intrinsics_h user_intrinsics).


    Section Structural_Lemmas.

      Lemma interp_intrinsics_bind :
        forall (R S : Type) l (t : itree Eff R) (k : R -> itree _ S),
          interp_intrinsics l (ITree.bind t k) ≅ ITree.bind (interp_intrinsics l t) (fun r : R => interp_intrinsics l (k r)).
      Proof.
        intros; apply interp_bind.
      Qed.

      Lemma interp_intrinsics_ret :
        forall (R : Type) l (x: R),
          interp_intrinsics l (Ret x: itree Eff _) ≅ Ret x.
      Proof.
        intros; apply interp_ret.
      Qed.

      Lemma interp_intrinsics_vis_eqit:
        forall {X R} (e : Eff X)
          (kk : X -> itree Eff R) defs,
          interp_intrinsics defs (Vis e kk) ≅
          ITree.bind (interp_intrinsics_h defs e) (fun x : X => Tau (interp (interp_intrinsics_h defs) (kk x))).
      Proof.
        intros.
        unfold interp_intrinsics.
        rewrite interp_vis.
        reflexivity.
      Qed.

      Lemma interp_intrinsics_vis:
        forall X R (e : Eff X)
          (kk : X -> itree Eff R) defs,
          interp_intrinsics defs (Vis e kk) ≈
                            ITree.bind (interp_intrinsics_h defs e) (fun x : X => interp (interp_intrinsics_h defs) (kk x)).
      Proof.
        intros.
        rewrite interp_intrinsics_vis_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      Lemma interp_intrinsics_trigger:
        forall X (e : Eff X) defs,
          interp_intrinsics defs (ITree.trigger e) ≈ interp_intrinsics_h defs e.
      Proof.
        intros *.
        unfold interp_intrinsics.
        rewrite interp_trigger.
        reflexivity.
      Qed.

      Lemma interp_intrinsics_bind_trigger_eqit:
        forall X R (e : Eff X)
          (kk : X -> itree Eff R) defs,
          interp_intrinsics defs (ITree.bind (trigger e) kk) ≅
                            ITree.bind (interp_intrinsics_h defs e) (fun x : X => Tau (interp (interp_intrinsics_h defs) (kk x))).
      Proof.
        intros *.
        unfold interp_intrinsics.
        rewrite bind_trigger.
        rewrite interp_vis.
        reflexivity.
      Qed.

      Lemma interp_intrinsics_bind_trigger:
        forall X R (e : Eff X)
          (kk : X -> itree Eff R) defs,
          interp_intrinsics defs (ITree.bind (trigger e) kk) ≈
                            ITree.bind (interp_intrinsics_h defs e) (fun x : X => interp (interp_intrinsics_h defs) (kk x)).
      Proof.
        intros.
        rewrite interp_intrinsics_bind_trigger_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      Global Instance eutt_interp_intrinsics (user_intrinsics: intrinsic_definitions) {R} :
        Proper (eutt Logic.eq ==> eutt Logic.eq) (@interp_intrinsics user_intrinsics R).
      Proof.
        do 2 red; intros * EQ.
        unfold interp_intrinsics.
        rewrite EQ; reflexivity.
      Qed.

  End Structural_Lemmas.

  End PARAMS.

End Make.
