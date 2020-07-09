Require Import OrderedType OrderedTypeEx.

Module Type ADDRESS.
  Parameter addr : Set.
  Parameter null : addr.
  Parameter eq_dec : forall (a b : addr), {a = b} + {a <> b}.
End ADDRESS.
