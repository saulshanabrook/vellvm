Require Import ZArith List String Omega.
Require Import  Vir.LLVMAst Vir.Util.
Require Import Vir.StepSemantics.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

(* SAZ: This file is deprecated. *)

Inductive Addr :=
| Null
| Ptr (n:nat)
.      

Module A : Vir.LLVMIO.ADDR with Definition addr := Addr.
  Definition addr := Addr.
  Definition null := Null.   
End A.  

Module SS := StepSemantics.StepSemantics(A).
Export SS.
Export SS.DV.

Definition memory := list dvalue.

Definition mem_step {X} (e:IO X) (m:memory) : (IO X) + (list dvalue * X) :=
  match e in IO Y return (IO Y) + (list dvalue * Y) with 
  | Alloca t =>
    inr  ((m ++ [undef t])%list,
          DVALUE_Addr (Ptr (List.length m)))

  | Load t a =>
    inr (m,
         match a with
         | DVALUE_Addr (Ptr n) => nth_default (undef t) m n
         | _ => undef t
         end)
        
  | Store a v =>
    inr (
        match a with
        | DVALUE_Addr (Ptr n) => replace m n v
        | _ => m
        end,
        ())

  | GEP t a vs => inl (GEP t a vs)

  | ItoP t i => inl (ItoP t i)

  | PtoI t a => inl (PtoI t a)                     
                       
  | Call t f args  => inl (Call t f args)

                         
  | DeclareFun f =>
    inr (m,
         DVALUE_FunPtr f)
  end.

CoFixpoint memD {X} (m:memory) (d:Trace X) : Trace X :=
  match d with
  | Trace.Tau d'            => Trace.Tau (memD m d')
  | Trace.Vis _ io k =>
    match mem_step io m with
    | inr (m', v) => Trace.Tau (memD m' (k v))
    | inl e => Trace.Vis io k
    end
  | Trace.Ret x => d
  | Trace.Err x => d
  end.


Definition run_with_memory prog : option (Trace dvalue) :=
  let scfg := AstLib.modul_of_toplevel_entities prog in
  match CFG.mcfg_of_modul scfg with
  | None => None
  | Some mcfg =>
    mret
      (memD [] 
      ('s <- SS.init_state mcfg "main";
         SS.step_sem mcfg (SS.Step s)))
  end.
