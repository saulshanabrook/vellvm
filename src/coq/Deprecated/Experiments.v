Require Import ZArith List String Omega.
Require Import paco.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.


CoInductive stream (A:Type) :=
| snil : stream A
| scons : A -> stream A -> stream A
.

Arguments scons {_} _ _.

Definition id_match_stream {A} (s:stream A) : stream A :=
  match s with
  | snil => snil
  | scons x t => scons x t
  end.

Lemma id_stream_eq : forall A (s:stream A), s = id_match_stream s.
Proof.
  intros.
  destruct s; auto.
Qed.

Inductive s_equiv_step (s_equiv: stream nat -> stream nat -> Prop) : stream nat -> stream nat -> Prop :=
| s_equiv_nil  : s_equiv_step s_equiv snil snil
| s_equiv_cons : forall s1 s2 n (R : s_equiv s1 s2), s_equiv_step s_equiv (scons n s1) (scons n s2)
| s_equiv_cons_z_l : forall s1 s2, s_equiv_step s_equiv s1 s2 -> s_equiv_step s_equiv (scons 0 s1) s2
.

Hint Constructors s_equiv_step.

Lemma s_equiv_step_mono : monotone2 s_equiv_step.
Proof.
  unfold monotone2. intros x0 x1 r r' IN LE. 
  induction IN; eauto.
Qed.
Hint Resolve s_equiv_step_mono : paco.

Definition s_equiv (s t : stream nat) := paco2 s_equiv_step bot2 s t .
Hint Unfold s_equiv.

Lemma s_equiv_refl : forall (s : stream nat), (s_equiv s s).
Proof.
  pcofix CIH.
  intros s.
  pfold.
  destruct s; auto.
Qed.

Lemma s_equiv_trans : forall (s t u : stream nat), s_equiv s t -> s_equiv t u -> s_equiv s u.
Proof.
  pcofix CIH.
  intros s t u H0 H1.
  generalize dependent s.
  punfold H1.
  remember (upaco2 s_equiv_step bot2) as R.
  induction H1; intros s Hs.
  - punfold Hs.
    pfold.
    eapply s_equiv_step_mono. eapply Hs.
    intros. pclearbot. right. eapply CIH. apply PR. apply s_equiv_refl.
  - remember (scons n s1) as s0.
    punfold Hs. rewrite <- HeqR in Hs. 
    induction Hs; try inversion Heqs0; subst.
    + pfold. apply s_equiv_cons. pclearbot. right. eapply CIH.
      exact R1. exact R0.
    + pfold. apply s_equiv_cons_z_l.
      pclearbot. 
      assert (paco2 s_equiv_step r s0 (scons n s2)).
      eapply IHHs; auto.
      punfold H0.
  - remember (scons 0 s1) as s0.
    punfold Hs. rewrite <- HeqR in Hs.
    induction Hs; try inversion Heqs0; subst.
    + pclearbot. pfold. apply s_equiv_cons_z_l.
      specialize IHs_equiv_step with (s:=s0). apply IHs_equiv_step in R0. punfold R0.
    + pfold. apply s_equiv_cons_z_l.
      apply IHHs in H. punfold H.
Qed.
Inductive seq_step (seq : stream nat -> stream nat -> Prop) : stream nat -> stream nat -> Prop :=
| seq_nil  : seq_step seq snil snil
| seq_cons : forall s1 s2 n (R : seq s1 s2), seq_step seq (scons n s1) (scons n s2)
| seq_cons_z_l : forall s1 s2, seq_step seq s1 s2 -> seq_step seq (scons 0 s1) s2
| seq_cons_z_r : forall s1 s2, seq_step seq s1 s2 -> seq_step seq s1 (scons 0 s2)
.
Hint Constructors seq_step.

Lemma seq_step_mono : monotone2 seq_step.
Proof.
  unfold monotone2. intros x0 x1 r r' IN LE. 
  induction IN; eauto.
Qed.
Hint Resolve seq_step_mono : paco.

Definition seq (s t : stream nat) := paco2 seq_step bot2 s t .
Hint Unfold seq.


Lemma seq_step_refl : forall (R:stream nat -> stream nat -> Prop),
    (forall d, R d d) -> forall d, seq_step R d d.
Proof.
  intros.
  destruct d; constructor; auto.
Qed.

Lemma seq_refl : forall s, seq s s.
Proof.
  pcofix CIH.
  intros s.
  pfold.
  destruct s; auto.
Qed. 


Require Import Program Classical.

Inductive zeros_star (P: stream nat -> Prop) : stream nat -> Prop :=
| zs_base t (BASE: P t): zeros_star P t
| zs_step t (LZ: zeros_star P t): zeros_star P (scons 0 t)
.
Hint Constructors zeros_star.

Lemma zeros_star_mono : monotone1 zeros_star.
Proof.
  red. intros. induction IN; eauto.
Qed.
Hint Resolve zeros_star_mono.

Inductive zeros_one (P: stream nat -> Prop) : stream nat -> Prop :=
| zo_step t (BASE: P t): zeros_one P (scons 0 t)
.
Hint Constructors zeros_one.

Lemma zeros_one_mono : monotone1 zeros_one.
Proof.
  pmonauto.
Qed.
Hint Resolve zeros_one_mono : paco.

Definition infzeros := paco1 zeros_one bot1.
Hint Unfold infzeros.

Inductive nonzero: stream nat -> Prop :=
| nz_nil: nonzero snil
| nz_cons n s (NZ: n <> 0): nonzero (scons n s)
.
Hint Constructors nonzero.

Inductive gseq_cons_or_nil (gseq: stream nat -> stream nat -> Prop) : stream nat -> stream nat -> Prop :=
| gseq_nil : gseq_cons_or_nil gseq snil snil
| gseq_cons s1 s2 n (R: gseq s1 s2) (NZ: n <> 0) : gseq_cons_or_nil gseq (scons n s1) (scons n s2)
.
Hint Constructors gseq_cons_or_nil.

Inductive gseq_step (gseq: stream nat -> stream nat -> Prop) : stream nat -> stream nat -> Prop :=
| gseq_inf s1 s2 (IZ1: infzeros s1) (IZ2: infzeros s2) : gseq_step gseq s1 s2
| gseq_fin s1 s2 t1 t2
     (ZS1: zeros_star (fun t => t = s1) t1)
     (ZS2: zeros_star (fun t => t = s2) t2)
     (R: gseq_cons_or_nil gseq s1 s2)
  : gseq_step gseq t1 t2
.
Hint Constructors gseq_step.

Lemma gseq_step_mono : monotone2 gseq_step.
Proof.
  unfold monotone2. intros.
  induction IN; eauto.
  eapply gseq_fin; eauto.
  destruct R; eauto.
Qed.
Hint Resolve gseq_step_mono : paco.

Definition gseq (s t : stream nat) := paco2 gseq_step bot2 s t .
Hint Unfold gseq.

Lemma nonzero_not_infzeros: forall s
    (ZST: zeros_star nonzero s)
    (INF: infzeros s),
  False.
Proof.
  intros. revert INF. induction ZST.
  - intro INF. punfold INF. dependent destruction INF.
    dependent destruction BASE. contradiction.
  - intro INF. apply IHZST. 
    punfold INF. dependent destruction INF. pclearbot. eauto.
Qed.

Lemma infzeros_or_finzeros: forall s,
  infzeros s \/ zeros_star nonzero s.
Proof.
  intros. destruct (classic (zeros_star nonzero s)); eauto.
  left. revert s H. pcofix CIH.
  intros. destruct s.
  - exfalso. eauto.
  - destruct n; [|exfalso; eauto].
    pfold. econstructor. right. eauto.
Qed.

Lemma seq_infzeros_imply: forall s t
  (R: seq s t) (IZ: infzeros s), infzeros t.
Proof.
  pcofix CIH. intros.
  punfold R. revert IZ. induction R; intros.
  - eapply paco1_mon. eauto. intros. inversion PR.
  - pfold. punfold IZ. dependent destruction IZ. pclearbot. eauto.
  - punfold IZ. dependent destruction IZ. pclearbot. eauto.
  - pfold. eauto.
Qed.

Lemma seq_zeros_star_imply: forall s t
  (R: seq s t) (IZ: zeros_star nonzero s), zeros_star nonzero t.
Proof.
  intros. revert t R. induction IZ; intros.
  - punfold R. induction R; pclearbot; eauto. 
    + inversion BASE. eauto.
    + inversion BASE. contradiction.
  - punfold R.  dependent induction R; intros; pclearbot; try dependent destruction Heqs; eauto. 
Qed.

Lemma seq_infzeros_or_finzeros: forall s t
    (R: seq s t),
  (infzeros s /\ infzeros t) \/ 
  (zeros_star nonzero s /\ zeros_star nonzero t).
Proof.
  intros. destruct (@infzeros_or_finzeros s).
  - eauto using seq_infzeros_imply.
  - eauto using seq_zeros_star_imply.
Qed.

Lemma seq_zero_l: forall s t 
    (EQ : seq (scons 0 s) t),
  seq s t.
Proof.
  intros. punfold EQ. pfold.
  dependent induction EQ; intros; try dependent destruction Heqs0; pclearbot; eauto.
  punfold R.
Qed.

Lemma seq_zero_r: forall s t 
    (EQ : seq s (scons 0 t)),
  seq s t.
Proof. 
  intros. punfold EQ. pfold.
  dependent induction EQ; intros; try dependent destruction Heqs0; pclearbot; eauto.
  punfold R.
Qed.

Lemma zero_gseq_l: forall r s t
    (R : paco2 gseq_step r s t),
  paco2 gseq_step r (scons 0 s) t.
Proof.
  intros. punfold R. pfold. destruct R; eauto.
  econstructor; eauto. pfold. eauto.
Qed.

Lemma zero_gseq_r: forall r s t
    (R : paco2 gseq_step r s t),
  paco2 gseq_step r s (scons 0 t).
Proof.
  intros. punfold R. pfold. destruct R; eauto.
  econstructor; eauto. pfold. eauto.
Qed.

Lemma seq_implies_gseq: forall s t
  (R: seq s t), gseq s t.
Proof.
  pcofix CIH.
  intros. destruct (seq_infzeros_or_finzeros R) as [[]|[]]; eauto.
  induction H.
  - induction H0.
    + pfold. punfold R. dependent destruction R; pclearbot; eauto.
      * dependent destruction BASE. eauto 10.
      * dependent destruction BASE. contradiction.
      * dependent destruction BASE0. contradiction.
    + eauto using seq_zero_r, zero_gseq_r.
  - eauto using seq_zero_l, zero_gseq_l.
Qed.

Lemma gseq_implies_seq: forall s t
  (R: gseq s t), seq s t.
Proof.
  pcofix CIH; intros.
  punfold R. destruct R.
  - punfold IZ1. punfold IZ2. 
    dependent destruction IZ1. dependent destruction IZ2. pclearbot.
    pfold. econstructor. right. eauto.
  - induction ZS1; subst.
    + induction ZS2; subst.
      * pfold. dependent destruction R; pclearbot; eauto.
      * pfold. punfold IHZS2.
    + pfold. punfold IHZS1.
Qed.

Lemma gseq_cons_or_nil_nonzero_l: forall r s t
    (R : gseq_cons_or_nil r s t),
  nonzero s.
Proof. intros; destruct R; eauto. Qed.

Lemma gseq_cons_or_nil_nonzero_r: forall r s t
    (R : gseq_cons_or_nil r s t),
  nonzero t.
Proof. intros; destruct R; eauto. Qed.

Lemma zeros_star_nonzero_uniq: forall s1 s2 t
    (ZS1: zeros_star (fun s => s = s1) t)
    (ZS2: zeros_star (fun s => s = s2) t)
    (NZ1: nonzero s1)
    (NZ2: nonzero s2),
  s1 = s2.
Proof.
  intros s1 s2 t ZS1. revert s2. 
  induction ZS1; subst; intros.
  - induction ZS2; subst; eauto.
    inversion NZ1. contradiction.
  - dependent destruction ZS2; eauto.
    inversion NZ2. contradiction.
Qed.

Lemma gseq_trans : forall d1 d2 d3 
  (EQL: gseq d1 d2) (EQR: gseq d2 d3), gseq d1 d3.
Proof.
  pcofix CIH; intros.
  punfold EQL. punfold EQR. destruct EQL, EQR; eauto.
  - exfalso. eapply nonzero_not_infzeros, IZ2.
    eapply zeros_star_mono; eauto.
    simpl. intros. subst. destruct R; eauto.
  - exfalso. eapply nonzero_not_infzeros, IZ1.
    eapply zeros_star_mono; eauto.
    simpl. intros. subst. destruct R; eauto.
  - eapply zeros_star_nonzero_uniq in ZS2; 
    eauto using gseq_cons_or_nil_nonzero_l, gseq_cons_or_nil_nonzero_r.
    subst. pfold. econstructor 2; eauto.
    destruct R; dependent destruction R0; pclearbot; eauto.
Qed.

Lemma seq_trans : forall d1 d2 d3
  (EQL: seq d1 d2) (EQR: seq d2 d3), seq d1 d3.
Proof.
  eauto using gseq_trans, seq_implies_gseq, gseq_implies_seq.
Qed.



Lemma teq_seq : forall s1 s2, teq s1 s2 -> seq s1 s2.
Proof.
  pcofix CIH.
  intros s1 s2 H.
  punfold H.
  induction H; auto.
  - pcofix CIH'. pfold.
    rewrite (@id_stream_eq _ zeros). simpl.
    apply seq_cons. right. apply CIH'.
  - pfold. apply seq_cons. pclearbot.  right. eapply CIH. apply H.
  - pfold. constructor. punfold IHteq_step.
  - pfold. constructor. punfold IHteq_step.
Qed.

Lemma seq_teq : forall s1 s2, seq s1 s2 -> teq s1 s2.
Proof.
  pcofix CIH.
  intros s1 s2 H.
  punfold H.
  induction H.
  - pfold. constructor.
  - destruct n.
    pcofix CIH'.
    pclearbot. pfold. constructor.
    





Lemma seq_symm : forall s1 s2, seq s1 s2 -> seq s2 s1.
Proof.
  pcofix CIH.
  intros s1 s2 H.
  pfold.
  punfold H.
  induction H; try constructor; auto.
  - pclearbot. right. apply CIH. punfold R.
Qed.
Lemma seq_trans : forall d1 d2 d3, seq d1 d2 -> seq d2 d3 -> seq d1 d2.
Proof.
Abort.








Lemma seq_step_trans' : forall (R:stream nat -> stream nat -> Prop) d1 d2 d3,
    (forall d1 d2 d3, R d1 d2 -> R d2 d3 -> R d1 d3) ->
    (forall d1 d2 d3, R d1 d2 -> seq_step R d2 d3 -> seq_step R d1 d3) ->
    (forall d1 d2 d3, seq_step R d1 d2 -> R d2 d3 -> seq_step R d1 d3) ->    
    seq_step R d1 d2 ->
    seq_step R d2 d3 ->
    seq_step R d1 d3.
Proof.
  intros R d1 d2 d3 TR RL RR H12.
  generalize dependent d3.
  induction H12; intros d3 H21.
  - inversion H21; subst; constructor; auto.
  - remember (scons n s2) as s.
    induction H21; inversion Heqs; subst; try clear Heqs.
    + constructor. eapply TR; eauto.
    + apply seq_cons_z_l. eapply RL; eauto.
    + apply seq_cons_z_r. apply IHseq_step; auto.
  - apply seq_cons_z_l. apply IHseq_step. apply H21.
  - remember (scons 0 s2) as s.
    induction H21; inversion Heqs; subst; try clear Heqs.
    + apply seq_cons_z_r. eapply RR. apply H12. exact R0.
    + apply IHseq_step. exact H21.
    + apply seq_cons_z_r. apply IHseq_step0; auto.
Qed.      
      

Lemma seq_trans' : forall (R:stream nat -> stream nat -> Prop) (s t u : stream nat),
    (forall d, paco2 seq_step R d d) ->
    (forall d1 d2 d3, seq_step R d1 d2 -> seq_step R d2 d3 -> seq_step R d1 d3) ->
    (forall d1 d2 d3, R d1 d2 -> seq_step R d2 d3 -> seq_step R d1 d3) ->
    (forall d1 d2 d3, seq_step R d1 d2 -> R d2 d3 -> seq_step R d1 d3) ->    
    paco2 seq_step R s t -> paco2 seq_step R t u -> paco2 seq_step R s u.
Proof.
Admitted.

Lemma seq_r_trans' : forall (R:stream nat -> stream nat -> Prop) (d1 d2 d3 : stream nat),
    (forall d1 d2 d3, seq_step R d1 d2 -> seq_step R d2 d3 -> seq_step R d1 d3) ->
    (forall s t u, paco2 seq_step R s t -> paco2 seq_step R t u -> paco2 seq_step R s u) ->
    paco2 seq_step R d1 d2 -> seq_step R d2 d3 -> seq_step R d1 d3.
Proof.
  intros.
  generalize dependent d1.
  induction H2; intros.
  - punfold H1. remember snil as d2.
    induction H1; inversion Heqd2; try subst.
    + constructor.
    + apply seq_cons_z_l. apply IHseq_step; auto.
Admitted.

Section S_EQUIV_COIND.

  Variable R : stream nat -> stream nat -> Prop.

  Variables (p:stream nat) (q:stream nat).
  Hypothesis Hrpq : R p q.
  Hypothesis H : forall d1 d2,
    R d1 d2 -> s_equiv_step R d1 d2.
  
  Theorem s_equiv_coind :
    s_equiv p q.
  Proof.
    revert p q Hrpq.
    pcofix CIH.
    intros ? ? Hr.
    apply H in Hr. induction Hr; intros; subst; try solve [clear CIH; auto].
    - pfold. constructor. right. auto.
    - pfold. constructor. 
      punfold IHHr.
  Qed.

End S_EQUIV_COIND.
Arguments s_equiv_coind [_] _ [_ _] _.


Inductive s_equiv_step' (s_equiv': stream nat -> stream nat -> Prop) : stream nat -> stream nat -> Prop :=
| s_equiv_nil' : s_equiv_step' s_equiv' snil snil
| s_equiv_cons' : forall s1 s2 (R : s_equiv' s1 s2) n, s_equiv_step' s_equiv' (scons n s1) (scons n s2)
| s_equiv_cons_z_l' : forall s1 s2 (R : s_equiv' s1 s2), s_equiv_step' s_equiv' (scons 0 s1) s2
.

Hint Constructors s_equiv_step'.

Lemma s_equiv_step'_mono : monotone2 s_equiv_step'.
Proof.
  unfold monotone2. intros x0 x1 r r' IN LE.
  destruct IN; eauto.
Qed.  
Hint Resolve s_equiv_step'_mono : paco.

Definition s_equiv' (s t : stream nat) := paco2 s_equiv_step' bot2 s t.
Hint Unfold s_equiv'.

Lemma s_equiv_equiv' : forall s t, s_equiv s t -> s_equiv' s t.
Proof.
  pcofix CIH.
  intros s t H.
  punfold H.
  remember (upaco2 s_equiv_step bot2) as d.
  induction H; eauto.
  - pfold. constructor. subst. destruct R. right. apply CIH. exact H. inversion H.
Qed.



Lemma zeros_equiv' : forall s, s_equiv' zeros s.
Proof.
  pcofix CIH.
  intros s.
  pfold.
  rewrite (@id_stream_eq _ zeros). simpl.
  apply s_equiv_cons_z_l'. right. apply CIH.
Qed.  

Lemma not_zeros_equiv : exists s, ~ s_equiv zeros s.
Proof.
  exists (scons 1 snil). unfold not.
  intros H.
  punfold H.
  remember (upaco2 s_equiv_step bot2) as d.
  remember zeros as s.
  remember (scons 1 snil) as t.
  induction H.
  - inversion Heqt.
  - inversion Heqt. subst. 
    rewrite (@id_stream_eq _ zeros) in Heqs.
    simpl in Heqs. inversion Heqs.
  - apply IHs_equiv_step.
    rewrite (@id_stream_eq _ zeros) in Heqs.
    simpl in Heqs. inversion Heqs. reflexivity.
    exact Heqt.
Qed.    
  





