From Coq Require Import
     Program Morphisms Setoid.
Set Nested Proofs Allowed.

(*
  Trying to understand why rewriting in hypotheses is slow, and hopefully how to fix it.
 *)

Typeclasses eauto := debug.
Set Typeclasses Debug Verbosity 2.

Section Top.

  (* Consider a relation R and a context P. We want to rewrite R under P. *)
  Context {A: Type} {R: A -> A -> Prop} {P: A -> Prop}.

  Section Test1.

    (* The basic prerequisite for this is the following: basically, R a b -> P b -> P a *)
    Context {HProp: Proper (R ==> flip impl) P}.

    Variable a b : A.
    Variable HR: R a b.

    Goal P a.
      Time rewrite HR. (* 0. secs *)
      (* We can rewrite, and HProp is directly sufficient evidence to justify it *)
    Abort.

    Goal True /\ P a.
      (* Now what happens when the goal is more complex *)
      Time rewrite HR. (* 0.014 secs *)
      (* Two new things take place. *)

    (* First, we need to provide a second justification:
       (Proper (impl --> flip impl) (and False))
       which desugars to (Proper (impl --> flip (flip impl)) (and False))
       That is to say that `(P -> Q) -> (and False P -> and False Q)
       Annoyingly enough, this is quite slow to justify.
     *)
    (* Second, the first justification required is now ambiguous:
       1: looking for (Proper (R ==> ?r) P)
       instead of
       1: looking for (Proper (R ==> flip impl) P)
       HProp is still a sufficient justification, but this metavariable will come and bite us later.
     *)

    Abort.

    (* The first problem may be solved by adding the following instance.
       It might be worth to have a few such for the main logical connectives
     *)
    Global Instance foo Q: Proper (impl --> flip impl) (and Q).
    Proof.
      repeat intro; intuition.
    Qed.

    (* Note of course that so far, we _cannot_ rewrite in hypotheses *)
    Goal P a -> False.
      intros HP.
      Fail rewrite HR in HP.
    Abort.
    (* Which is fair since it logically requires an entailment in the other direction. *)

  End Test1.

  Section Test2.

    (* Let's now ambition to rewrite _also_ in hypotheses. *)
    (* One solution is for R to be symmetric. *)
    Context {HProp: Proper (R ==> flip impl) P}.
    Context {Sym: Symmetric R}.

    Variable a b : A.
    Variable HR: R a b.

    Goal P a.
      Time rewrite HR. (* 0. secs *)
      (* Rewrites in goal work as before *)
    Abort.

    Goal False /\ P a.
      Time rewrite HR. (* 0. secs *)
      (* Rewrites in goal work as before *)
    Abort.

    Goal P a -> False.
      intros HP.
      Time rewrite HR in HP. (* 0.003 secs *)
    (* This now succeeds. The justification is not completely trivial however:
         we are looking for (Proper (R ==> impl) P)
         - First, we wonder whether by any chance R does not happen to be a subrelation of impl.
         It takes some churning, but eventually we conclude that it's a dead cause.
         - Second, we initiate a quite mysterious process, "proper_normalization",
         that reduces the goal to looking for:
         (Proper (flip (R --> flip impl)) P)
         Which takes some churning, but by symmetry eventually reduces to HProp
     *)
    Abort.

    Goal (True /\ P a) -> P b.
      intros HP.
      Time rewrite HR in HP. (* 0.054 secs *)
      (* Now funnily enough, rewriting in a product in an hypothesis is
         more complex than all other goals so far.
         The argument when doing so in the goal, to argue that
         Proper (impl --> flip impl) (and Q)
         Now becomes to argue that:
         Proper (impl --> impl) (and Q)
         Which is false:
       *)

      Goal (Proper (impl --> impl) (and True)) -> False.
        repeat intro.
        repeat red in H.
        unfold flip, impl in H.
        specialize (H True False).
        apply H; intuition.
      Qed.

    (* We therefore first need to discover that this branch is absurd before
       building a symmetry-based argument, which takes > 3k lines
     *)
    Abort.

  End Test2.

  Section Test3.

    (* Now what if our relation was not symmetric, but still respected P in both directions?
       And/or could we speed up things?
       Well one obvious thought is to prove/assume respect in both directions.
     *)
    Context {HProp: Proper (R ==> flip impl) P}.
    Context {HProp': Proper (R ==> impl) P}.

    Variable a b : A.
    Variable HR: R a b.

    Goal P a.
      Time rewrite HR. (* 0. secs *)
      (* Rewrites in goal works as before *)
    Abort.

    Goal P a -> True.
      intros HP.
      Time rewrite HR in HP. (* 0. secs *)
      (* Rewrites in hypotheses work as quickly as in goals now!! *)
    Abort.

    Goal False /\ P a.
      Time rewrite HR. (* 0.041 secs *)
    (* Woopsy. This one that was smoothh in both cases before is now >1.5k of justification.
         Indeed, the ambiguity of the goal:
         (Proper (R ==> ?r) P)
         with the metavariable ?r that shows up when working in non-trivial contexts has led the
         solver to pick HProp' instead of HProp! So that we are off the road on a journey to
         understand the errors of our ways before getting back where we started and using HProp.
     *)
    Abort.

    Goal False /\ P a -> False.
      intros H.
      Time rewrite HR in H. (* 0.006 secs *)
    (* Amusingly, this one is much easier to justify than with the Reflexivity assumption,
       since we do not have to wander toward the absurd goal.
     *)
    Abort.

    (* We could decide to get a bit hacky. Let's avoid the problem in the conjunction in goal case
       by forcing priority to HProp
     *)
    Existing Instance HProp | 0.

    Goal False /\ P a.
      Time rewrite HR. (* 0. secs *)
      (* And it works. *)
    Abort.

    Goal False /\ P a -> False.
      intros H.
      Time rewrite HR in H. (* 0.048 secs *)
      (* But of course we now broke the hypothesis case. *)
    Abort.

  End Test3.

  Section Test4.

    (* Instead of assuming both directions, we can have an instance w.r.t. [iff] *)
    Context {HProp: Proper (R ==> iff) P}.

    Variable a b : A.
    Variable HR: R a b.

    Goal P a.
      Time rewrite HR. (* 0.001 secs *)
    Abort.

    Goal P a -> True.
      intros HP.
      Time rewrite HR in HP. (* 0.001 secs *)
    Abort.

    Goal False /\ P a.
      Time rewrite HR. (* 0.002 secs *)
    Abort.

    Goal False /\ P a -> False.
      intros H.
      Time rewrite HR in H. (* 0.002 secs *)
    Abort.

  End Test4.

End Top.
