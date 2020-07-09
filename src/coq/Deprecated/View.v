From ITree Require Import 
     ITree
     Events.State.

Set Implicit Arguments.

(* View XY Z X generalizes the Subevent relation.
   Should be thought as `X` is a subdomain of `XY`, and `Z` a view of the complement.
   Note that one could always chose to take Z = unit, but it is important to express operations.
 *)
Class View {XY Z X : Type -> Type} : Type :=
  { preview : XY ~> X +' Z
    ; review : X ~> XY
    ; preview_review : forall {t} (x : X t), preview (review x) = inl1 x
    ; review_preview : forall {t} (xy : XY t) x, preview xy = inl1 x -> review x = xy
  }.
Arguments View : clear implicits.
Arguments preview {_ _ _} _ [_].
Arguments review {_ _ _} _ [_].

(* Partial injection of the bigger domain of events back into the smaller one *)
Definition isa {X Z y} {V : View X Z y} : forall t, X t -> option (y t) :=
  fun t mx =>
    match V.(preview) mx with
    | inl1 x => Some x
    | inr1 _ => None
    end.

(* Embedding of the subdomain into the bigger one *)
Definition subevent {X Z y} {V : View X Z y} : y ~> X := V.(review).

(* Generic lifting of an type-indexed function from the subdomain of effects `a`
   into the ambient one `A`.
   This is where we crucially need the `Z` argument to
   ̀View` for `preview` to also tell us how to embed the complement `A\a` into
   `B`. *)
Definition over {A B a} {z : View A B a} (f : a ~> B) : A ~> B :=
  fun t a => match z.(preview) a with
          | inl1 a => f _ a
          | inr1 b => b
          end.
Arguments over {_ _ _ _} _ [_] _.

(* The less informative previous Subevent relation is recovered by dismissing the `Z` parameter *)
Definition Subevent A B := forall x, View A x B.

(* Should be enough to express generic lemmas as needed for swap *)
(* The instance from atomic domains of events to bigger ones is expressed through `over` *)

(*
  forall f, translate f (trigger x) = trigger (f x)
  over {V} swap (subevent {V} x) = subevent {V} (swap {V} x)
  -----------------
  translate swap (trigger (subevent {f} x)) ~ trigger (subevent {f} (swap x))
  
  forall V, translate (over {z:=V} (swap a b)) X

  translate (over f) (Vis e k) = Vis (over f e) (fun x => translate (over f) k)
  translate (over f) (translate (over g) X) = 
*)

(* Things are also interested with respect to simplifying the construction of interpreters.
 Consider the case from GlobalE for example *)
From ITree Require Import 
     Events.State.
From Vir Require Import
     LLVMEvents.
From ExtLib Require Import
     Programming.Show
     Structures.Monads
     Structures.Maps.

Section Globals.
  Variable (k v:Type).
  Context {map : Type}.
  Context {M: Map k v map}.
  Context {SK : Show k}.
 
  Import ITree.Basics.Basics.Monads.
  Definition foo {e f s}
             {vv :View f (stateT s (itree e)) (GlobalE k v)}
             (g : GlobalE k v ~> stateT s (itree e))
    : itree f ~> stateT s (itree e).
  Proof.
    eapply interp_state.
    intros.
    generalize (@over _ _ _ vv). intros.
    eapply X0. eapply g. eapply X.
  Defined.

End Globals.
Instance View_id {A} : View A void1 A.
refine
  {| preview := inl1
     ; review := fun _ x => x
  |}.
auto.
intros ? ? ? H; inversion H; auto.
Defined.

Instance View_none {A}: View A A void1.
refine
  {| preview := inr1
     ; review := fun t (x: void1 t) => match x with end
  |}.
intros ? x; inversion x.
intros ? ? x; inversion x.
Defined.
Instance View_L {A B Z a} {_ : View A Z a} : View (A +' B) Z a.
Admitted.
Definition View_R {A B Z b} (_ : View B Z b) : View (A +' B) Z b.
Admitted.
 CoFixpoint join {E} : itree (itree E) ~> itree E.
  intros. econstructor.
  destruct (X.(observe)).
  { eapply RetF. exact r. }
  { eapply TauF. exact (join _ _ t). }
  { eapply TauF. eapply ITree.bind'. 2: exact e.
    exact (fun x => join _ _ (k x)). }
Defined.
