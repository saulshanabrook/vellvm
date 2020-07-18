From ITree Require Import
     ITree
     Eq.Eq.

From Vellvm Require Import
     LLVMAst
     LLVMEvents
     Handlers.Handlers
     InterpreterCFG
     Denotation
     InstrLemmas
     DynamicTypes. 

Module D   := Denotation Addr LLVMEvents.

(* Minimal examples of weirdly slow rewrites for non-TC reasons.

   In the first case, surprisingly introducing the evars that are part of the lhs of the equation
   being rewritten by pattern matching on the goal speeds it up radically.
   Why is this faster than just doing the rewrite?

   In the second case, although better, it is still unreasonably slow even when pattern matching:
   why is it different than in the first case?
   
 *)

Goal forall {A: Type} (R: A -> _ -> Prop) t g l mem r id τ τ' align,
    eutt R t
         (interp_cfg_to_L3 nil
                           (D.denote_instr
                              (IId r,
                               INSTR_Load false τ (τ', EXP_Ident (ID_Global id)) align))
                           g l mem).
  intros.
  Time rewrite denote_instr_load. (* ~18s on my machine *) 
  Undo.
  Time
    match goal with
      |- context[interp_cfg_to_L3 ?defs (D.denote_instr (IId ?i, INSTR_Load ?volatile ?τ (?τp, ?ptr) ?align)) ?g ?l ?m] =>
      rewrite (denote_instr_load i volatile τ τp ptr align defs g l m) 
    end.
  (* 0.01s on my machine *)
Abort.

Goal forall {A: Type} (R: A -> _ -> Prop) t g l mem r op,
    eutt R t
         (interp_cfg_to_L3 nil
                           (D.denote_instr
                              (IId r,
                               INSTR_Op op))
                           g l mem).
  intros.
  Time rewrite denote_instr_op. (* ~20s on my machine *) 
  Undo.
  Time
    match goal with
      |- context[interp_cfg_to_L3 ?defs (D.denote_instr (IId ?i, INSTR_Op ?op)) ?g ?l ?m] =>
      rewrite (denote_instr_op i op defs g l m) 
    end.
  (* Still >4s on my machine *)
Abort.
