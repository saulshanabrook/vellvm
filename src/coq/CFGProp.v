Require Import ZArith List String Omega.
Require Import Vir.LLVMAst Vir.CFG Vir.Dom.
Require Vir.AstLib.

Import ListNotations.
Open Scope list_scope.
Section WithType.
  Variable (T:Set).

Lemma find_block_same_fid : forall CFG fid br phis p,
    find_block_entry T CFG fid br = Some (BlockEntry _ phis p) -> (fn p) = fid.
Proof.
  intros CFG fid br phis p H.
  unfold find_block_entry in H.
  destruct (find_function T CFG fid); simpl in H; try solve [inversion H].
  destruct (find_block T (blks T (df_instrs d)) br); simpl in H; try solve [inversion H].
  destruct b. unfold block_to_entry in H. simpl in H. inversion H.
  simpl. reflexivity.
Qed.
Fixpoint exp_uses (v:exp T) : list ident :=
  match v with
  | EXP_Ident id => [id]
  | EXP_Integer _
  | EXP_Float _
  | EXP_Double _
  | EXP_Hex _
  | EXP_Bool _
  | EXP_Null
  | EXP_Zero_initializer
  | EXP_Cstring _
  | EXP_Undef => []

  | EXP_Struct l
  | EXP_Packed_struct l
  | EXP_Array l
  | EXP_Vector l => List.flat_map (fun x => exp_uses (snd x)) l
  | OP_IBinop _ _ v1 v2
  | OP_ICmp _ _ v1 v2
  | OP_FBinop _ _ _ v1 v2
  | OP_FCmp _ _ v1 v2 => (exp_uses v1) ++ (exp_uses v2)
  | OP_Conversion _ _ v _ => exp_uses v
  | OP_GetElementPtr _ (_,ptr) idxs => (exp_uses ptr) ++ (List.flat_map (fun x => exp_uses (snd x)) idxs)
  | OP_ExtractElement  (_,vec) (_,idx) => (exp_uses vec) ++ (exp_uses idx)
  | OP_InsertElement (_,vec) (_,elt) (_,idx) => (exp_uses vec) ++ (exp_uses elt) ++ (exp_uses idx)
  | OP_ShuffleVector (_, vec1) (_,vec2) (_,idxmask) => (exp_uses vec1) ++ (exp_uses vec2) ++ (exp_uses idxmask)
  | OP_ExtractValue (_,vec) _ => exp_uses vec
  | OP_InsertValue (_,vec) (_,elt) _ => (exp_uses vec) ++ (exp_uses elt)
  | OP_Select (_,cnd) (_,v1) (_,v2) => (exp_uses cnd) ++ (exp_uses v1) ++ (exp_uses v2)
  | OP_Freeze (_,v) => exp_uses v
  end.

Definition texp_uses (tv:texp T) : list ident := exp_uses (snd tv).

Definition phi_uses (i:phi T) : (list ident) :=
  match i with
  | Phi  t args => List.flat_map (fun x => exp_uses (snd x)) args
  end.
Definition instr_uses (i:instr T) : (list ident) :=
  match i with
  | INSTR_Op op => exp_uses op
  | INSTR_Call (_, op) args => (exp_uses op) ++ (List.flat_map texp_uses args)
  | INSTR_Alloca t None align => []
  | INSTR_Alloca t (Some tv) align => texp_uses tv
  | INSTR_Load  volatile t ptr align => texp_uses ptr
  | INSTR_Store volatile val ptr align => (texp_uses val) ++ (texp_uses ptr)
  | INSTR_Comment _
  | INSTR_Fence
  | INSTR_AtomicCmpXchg
  | INSTR_AtomicRMW
  | INSTR_Unreachable
  | INSTR_VAArg
  | INSTR_LandingPad => []
  end.

Definition terminator_uses (t:terminator T) : list ident :=
  match t with
  | TERM_Ret tv => texp_uses tv
  | TERM_Ret_void => []
  | TERM_Br tv _ _ => texp_uses tv
  | TERM_Br_1  _ => []
  | TERM_Switch  tv _ brs => (texp_uses tv) ++ (List.flat_map (fun x => texp_uses (fst x)) brs)
  | TERM_IndirectBr tv _ => texp_uses tv
  | TERM_Resume tv => texp_uses tv
  | TERM_Invoke (_,fid) args _ _ => [fid] ++ (List.flat_map texp_uses args)
  end.
Definition lbls (t:terminator T) : list block_id :=
  match t with
  | TERM_Ret _
  | TERM_Ret_void   => []
  | TERM_Br _ l1 l2 => [l1; l2]
  | TERM_Br_1 l => [l]
  | TERM_Switch _ l brs => l::(List.map (fun x => snd x) brs)
  | TERM_IndirectBr _ brs => brs
  | TERM_Resume _    => []
  | TERM_Invoke  _ _ l1 l2 => [l1; l2]
  end.
End WithType.
