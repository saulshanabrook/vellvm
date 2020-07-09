From Coq Require Import
     ZArith String List
     FSets.FMapWeakList
     Bool.Bool.

Require Import Integers Floats.

From ExtLib Require Import
     Structures.Monads
     Structures.Functor
     Eqv.

From ITree Require Import
     ITree
     Interp.Recursion
     Events.Exception.

From Vir Require Import
     Util
     Error
     LLVMAst
     AstLib
     CFG
     DynamicTypes
     MemoryAddress
     LLVMEvents
     Handlers.Intrinsics.

Require Import Ceres.Ceres.

Import Sum.
Import Subevent.
Import EqvNotation.
Import ListNotations.
Import MonadNotation.

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope monad_scope.
Open Scope string_scope.
Open Scope Z_scope.
Module Denotation(A:MemoryAddress.ADDRESS)(LLVMEvents:LLVM_INTERACTIONS(A)).
  Import LLVMEvents.

  Section CONVERSIONS.
    Definition eval_conv_h conv (t1:dtyp) (x:dvalue) (t2:dtyp) : itree conv_E dvalue :=
      let raise := @raise conv_E dvalue _
      in
      match conv with
      | Trunc =>
        match t1, x, t2 with
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 1 =>
          ret (DVALUE_I1 (repr (unsigned i1)))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_I 1 =>
          ret DVALUE_Poison
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 1 =>
          ret (DVALUE_I1 (repr (unsigned i1)))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_I 1 =>
          ret DVALUE_Poison
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 8 =>
          ret (DVALUE_I8 (repr (unsigned i1)))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_I 8 =>
          ret DVALUE_Poison
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 1 =>
          ret (DVALUE_I1 (repr (unsigned i1)))
        | DTYPE_I 64, DVALUE_Poison, DTYPE_I 1 =>
          ret DVALUE_Poison
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 8 =>
          ret (DVALUE_I8 (repr (unsigned i1)))
        | DTYPE_I 64, DVALUE_Poison, DTYPE_I 8 =>
          ret DVALUE_Poison
        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_I 32 =>
          ret (DVALUE_I32 (repr (unsigned i1)))
        | DTYPE_I 64, DVALUE_Poison, DTYPE_I 32 =>
          ret DVALUE_Poison
        | _, _, _ => raise "ill typed-conv"
        end
      | Zext =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 8 =>
          ret (DVALUE_I8 (repr (unsigned i1)))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 8 =>
          ret DVALUE_Poison
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32 =>
          ret (DVALUE_I32 (repr (unsigned i1)))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 32 =>
          ret DVALUE_Poison
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64 =>
          ret (DVALUE_I64 (repr (unsigned i1)))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 64 =>
          ret DVALUE_Poison
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32 =>
          ret (DVALUE_I32 (repr (unsigned i1)))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_I 32 =>
          ret DVALUE_Poison
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64 =>
          ret (DVALUE_I64 (repr (unsigned i1)))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_I 64 =>
          ret DVALUE_Poison
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
          ret (DVALUE_I64 (repr (unsigned i1)))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_I 64 =>
          ret DVALUE_Poison
        | _, _, _ => raise "ill typed-conv"
        end
      | Sext =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 8 =>
          ret (DVALUE_I8 (repr (signed i1)))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 8 =>
          ret DVALUE_Poison
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 32 =>
          ret (DVALUE_I32 (repr (signed i1)))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 32 =>
          ret DVALUE_Poison
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_I 64 =>
          ret (DVALUE_I64 (repr (signed i1)))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_I 64 =>
          ret DVALUE_Poison
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 32 =>
          ret (DVALUE_I32 (repr (signed i1)))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_I 32 =>
          ret DVALUE_Poison
        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_I 64 =>
          ret (DVALUE_I64 (repr (signed i1)))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_I 64 =>
          ret DVALUE_Poison
        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_I 64 =>
          ret (DVALUE_I64 (repr (signed i1)))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_I 64 =>
          ret DVALUE_Poison
        | _, _, _ => raise "ill typed-conv"
        end
      | Bitcast =>
        match t1, x, t2 with
        | DTYPE_I bits1, x, DTYPE_I bits2 =>
          if bits1 =? bits2 then ret x else raise "unequal bitsize in cast"
        | DTYPE_Pointer, DVALUE_Addr a, DTYPE_Pointer =>
          ret (DVALUE_Addr a)
        | DTYPE_Pointer, DVALUE_Poison, DTYPE_Pointer =>
          ret DVALUE_Poison
        | _, _, _ => raise "ill-typed_conv"
        end
      | Uitofp =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (unsigned i1))))
        | DTYPE_I 64, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (unsigned i1))))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (unsigned i1))))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (unsigned i1))))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (unsigned i1))))
        | DTYPE_I 64, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | _, _, _ => raise "ill typed Uitofp"
        end
      | Sitofp =>
        match t1, x, t2 with
        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (signed i1))))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (signed i1))))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (signed i1))))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Float =>
          ret (DVALUE_Float (Float32.of_intu (repr (signed i1))))
        | DTYPE_I 64, DVALUE_Poison, DTYPE_Float =>
          ret DVALUE_Poison

        | DTYPE_I 1, DVALUE_I1 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (signed i1))))
        | DTYPE_I 1, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | DTYPE_I 8, DVALUE_I8 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (signed i1))))
        | DTYPE_I 8, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | DTYPE_I 32, DVALUE_I32 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (signed i1))))
        | DTYPE_I 32, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | DTYPE_I 64, DVALUE_I64 i1, DTYPE_Double =>
          ret (DVALUE_Double (Float.of_longu (repr (signed i1))))
        | DTYPE_I 64, DVALUE_Poison, DTYPE_Double =>
          ret DVALUE_Poison

        | _, _, _ => raise "ill typed Sitofp"
        end
      | Fptoui
      | Fptosi
      | Fptrunc
      | Fpext => raise "TODO: unimplemented numeric conversion"
      | Inttoptr =>
        match t1, t2 with
        | DTYPE_I 64, DTYPE_Pointer => trigger (ItoP x)
        | _, _ => raise "ERROR: Inttoptr got illegal arguments"
        end
      | Ptrtoint =>
        match t1, t2 with
        | DTYPE_Pointer, DTYPE_I _ => trigger (PtoI t2 x)
        | _, _ => raise "ERROR: Ptrtoint got illegal arguments"
        end
      end.
    Arguments eval_conv_h _ _ _ _ : simpl nomatch.

    Definition eval_conv (conv : conversion_type) (t1 : dtyp) (x : dvalue) (t2:dtyp) : itree conv_E dvalue :=
      match t1, x with
      | DTYPE_Vector s t, (DVALUE_Vector elts) =>
        raise "vectors unimplemented"
      | _, _ => eval_conv_h conv t1 x t2
      end.
    Arguments eval_conv _ _ _ _ : simpl nomatch.

  End CONVERSIONS.

  Definition dv_zero_initializer (t:dtyp) : err dvalue :=
    failwith "dv_zero_initializer unimplemented".
  Definition lookup_id (i:ident) : itree lookup_E uvalue :=
    match i with
    | ID_Global x => dv <- trigger (GlobalRead x);; ret (dvalue_to_uvalue dv)
    | ID_Local x  => trigger (LocalRead x)
    end.
  Definition iop_is_div (iop : ibinop) : bool :=
    match iop with
    | UDiv _ => true
    | SDiv _ => true
    | URem   => true
    | SRem   => true
    | _      => false
    end.

  Definition fop_is_div (fop : fbinop) : bool :=
    match fop with
    | FDiv => true
    | FRem => true
    | _    => false
    end.
  Definition dvalue_is_zero (dv : dvalue) : Prop :=
    match dv with
    | DVALUE_I1 x     => x = zero
    | DVALUE_I8 x     => x = zero
    | DVALUE_I32 x    => x = zero
    | DVALUE_I64 x    => x = zero
    | DVALUE_Double x => x = Float.zero
    | DVALUE_Float x  => x = Float32.zero
    | _               => False
    end.

  Definition dvalue_not_zero dv := ~ (dvalue_is_zero dv).
  Definition concretize_or_pick {E : Type -> Type} `{PickE -< E} `{FailureE -< E} (uv : uvalue) (P : Prop) : itree E dvalue :=
    if is_concrete uv
    then lift_err ret (uvalue_to_dvalue uv)
    else trigger (pick uv P).
  Definition pick_your_poison {E : Type -> Type} `{PickE -< E} `{FailureE -< E} (dt : dtyp) (uv : uvalue) : itree E dvalue :=
    match uv with
    | UVALUE_Poison => concretize_or_pick (UVALUE_Undef dt) True
    | _             => concretize_or_pick uv True
    end.

  Definition pickUnique {E : Type -> Type} `{PickE -< E} `{FailureE -< E} (uv : uvalue) : itree E dvalue
    := concretize_or_pick uv (unique_prop uv).

  Fixpoint denote_exp
           (top:option dtyp) (o:exp dtyp) {struct o} : itree exp_E uvalue :=
        let eval_texp '(dt,ex) := denote_exp (Some dt) ex
        in
        match o with
        | EXP_Ident i =>
          translate lookup_E_to_exp_E (lookup_id i)

        | EXP_Integer x =>
          match top with
          | None                => raise "denote_exp given untyped EXP_Integer"
          | Some (DTYPE_I bits) => lift_undef_or_err ret (fmap dvalue_to_uvalue (coerce_integer_to_int bits x))
          | Some typ            => raise ("bad type for constant int: " ++ to_string typ)
          end

        | EXP_Float x =>
          match top with
          | None              => raise "denote_exp given untyped EXP_Float"
          | Some DTYPE_Float  => ret (UVALUE_Float x)
          | _                 => raise "bad type for constant float"
          end

        | EXP_Double x =>
          match top with
          | None              => raise "denote_exp given untyped EXP_Double"
          | Some DTYPE_Double => ret (UVALUE_Double x)
          | _                 => raise "bad type for constant double"
          end

        | EXP_Hex x =>
          match top with
          | None              => raise "denote_exp given untyped EXP_Hex"
          | Some DTYPE_Float  => ret (UVALUE_Float (Float32.of_double x))
          | Some DTYPE_Double => ret (UVALUE_Double x)
          | _                 => raise "bad type for constant hex float"
          end

        | EXP_Bool b =>
          match b with
          | true  => ret (UVALUE_I1 one)
          | false => ret (UVALUE_I1 zero)
          end

        | EXP_Null => ret (UVALUE_Addr A.null)

        | EXP_Zero_initializer =>
          match top with
          | None   => raise "denote_exp given untyped EXP_Zero_initializer"
          | Some t => lift_err ret (fmap dvalue_to_uvalue (dv_zero_initializer t))
          end

        | EXP_Cstring s => raise "EXP_Cstring not yet implemented"

        | EXP_Undef =>
          match top with
          | None   => raise "denote_exp given untyped EXP_Undef"
          | Some t => ret (UVALUE_Undef t)
          end
        | EXP_Struct es =>
          vs <- map_monad eval_texp es ;;
          ret (UVALUE_Struct vs)
        | EXP_Packed_struct es =>
          match top with
          | None => raise "denote_exp given untyped EXP_Struct"
          | Some (DTYPE_Packed_struct _) =>
            vs <- map_monad eval_texp es ;;
            ret (UVALUE_Packed_struct vs)
          | _ => raise "bad type for VALUE_Packed_struct"
          end

        | EXP_Array es =>
          vs <- map_monad eval_texp es ;;
          ret (UVALUE_Array vs)

        | EXP_Vector es =>
          vs <- map_monad eval_texp es ;;
          ret (UVALUE_Vector vs)
        | OP_IBinop iop dt op1 op2 =>
          v1 <- denote_exp (Some dt) op1 ;;
          v2 <- denote_exp (Some dt) op2 ;;
          if iop_is_div iop && negb (is_concrete v2)
          then
            dv2 <- concretize_or_pick v2 (forall dv2, concretize v2 dv2 -> dvalue_not_zero dv2) ;;
            uvalue_to_dvalue_binop2
              (fun v1 v2 => ret (UVALUE_IBinop iop v1 v2))
              (fun v1 v2 => translate _failure_UB_to_ExpE
                                   (lift_undef_or_err ret (fmap dvalue_to_uvalue (eval_iop iop v1 v2))))
              v1 dv2
          else
            uvalue_to_dvalue_binop
              (fun v1 v2 => ret (UVALUE_IBinop iop v1 v2))
              (fun v1 v2 => translate _failure_UB_to_ExpE
                                   (lift_undef_or_err ret (fmap dvalue_to_uvalue (eval_iop iop v1 v2))))
              v1 v2

        | OP_ICmp cmp dt op1 op2 =>
          v1 <- denote_exp (Some dt) op1 ;;
          v2 <- denote_exp (Some dt) op2 ;;
          uvalue_to_dvalue_binop
            (fun v1 v2 => ret (UVALUE_ICmp cmp v1 v2))
            (fun v1 v2 => lift_undef_or_err ret (fmap dvalue_to_uvalue (eval_icmp cmp v1 v2)))
            v1 v2

        | OP_FBinop fop fm dt op1 op2 =>
          v1 <- denote_exp (Some dt) op1 ;;
          v2 <- denote_exp (Some dt) op2 ;;
          if fop_is_div fop && negb (is_concrete v2)
          then
            dv2 <- concretize_or_pick v2 (forall dv2, concretize v2 dv2 -> dvalue_is_zero dv2) ;;
            uvalue_to_dvalue_binop2
              (fun v1 v2 => ret (UVALUE_FBinop fop fm v1 v2))
              (fun v1 v2 =>
                 translate _failure_UB_to_ExpE
                                   (lift_undef_or_err ret (fmap dvalue_to_uvalue (eval_fop fop v1 v2))))
              v1 dv2
          else
            uvalue_to_dvalue_binop
            (fun v1 v2 =>
               ret (UVALUE_FBinop fop fm v1 v2))
              (fun v1 v2 =>
                 translate _failure_UB_to_ExpE
                                   (lift_undef_or_err ret (fmap dvalue_to_uvalue (eval_fop fop v1 v2))))
              v1 v2

        | OP_FCmp fcmp dt op1 op2 =>
          v1 <- denote_exp (Some dt) op1 ;;
          v2 <- denote_exp (Some dt) op2 ;;
          uvalue_to_dvalue_binop
            (fun v1 v2 => ret (UVALUE_FCmp fcmp v1 v2))
            (fun v1 v2 => lift_undef_or_err ret (fmap dvalue_to_uvalue (eval_fcmp fcmp v1 v2)))
            v1 v2

        | OP_Conversion conv dt1 op t2 =>
          v <- denote_exp (Some dt1) op ;;
          uvalue_to_dvalue_uop
            (fun v => ret (UVALUE_Conversion conv v t2))
            (fun v => translate conv_E_to_exp_E
                             (fmap dvalue_to_uvalue (eval_conv conv dt1 v t2)))
            v
        | OP_GetElementPtr dt1 (dt2, ptrval) idxs =>
          vptr <- denote_exp (Some dt2) ptrval ;;
          vs <- map_monad (fun '(dt, index) => denote_exp (Some dt) index) idxs ;;

          let maybe_dvs := dvptr <- uvalue_to_dvalue vptr ;;
                           dvs <- map_monad uvalue_to_dvalue vs ;;
                           ret (dvptr, dvs)
          in

          match maybe_dvs with
          | inr (dvptr, dvs) => fmap dvalue_to_uvalue (trigger (GEP dt1 dvptr dvs))
          | inl _ =>
            dvptr <- concretize_or_pick vptr True ;;
            dvs <- map_monad (fun v => concretize_or_pick v True) vs ;;
            fmap dvalue_to_uvalue (trigger (GEP dt1 dvptr dvs))
          end

        | OP_ExtractElement vecop idx =>
          raise "extractelement not implemented"

        | OP_InsertElement vecop eltop idx =>
          raise "insertelement not implemented"

        | OP_ShuffleVector vecop1 vecop2 idxmask =>
          raise "shufflevector not implemented"

        | OP_ExtractValue (dt, str) idxs =>
          str <- denote_exp (Some dt) str;;
          let fix loop str idxs : undef_or_err uvalue :=
              match idxs with
              | [] => ret str
              | i :: tl =>
                v <- index_into_str str i ;;
               loop v tl
              end in
          lift_undef_or_err ret (loop str idxs)

        | OP_InsertValue strop eltop idxs =>
          raise "TODO"

        | OP_Select (dt, cnd) (dt1, op1) (dt2, op2) =>
          cndv <- denote_exp (Some dt) cnd ;;
          v1   <- denote_exp (Some dt1) op1 ;;
          v2   <- denote_exp (Some dt2) op2 ;;
          match uvalue_to_dvalue cndv with
          | inl e => ret (UVALUE_Select cndv v1 v2)
          | inr dcndv => lift_undef_or_err ret (eval_select dcndv v1 v2)
          end

        | OP_Freeze (dt, e) =>
          uv <- denote_exp (Some dt) e ;;
          dv <- pick_your_poison dt uv;;
          ret (dvalue_to_uvalue dv)
        end.
  Arguments denote_exp _ : simpl nomatch.

  Definition denote_op (o:exp dtyp) : itree exp_E uvalue :=
    denote_exp None o.
  Arguments denote_op _ : simpl nomatch.

      Definition denote_instr
                 (i: (instr_id * instr dtyp)): itree instr_E unit :=
        match i with

        | (IId id, INSTR_Op op) =>
          dv <- translate exp_E_to_instr_E (denote_op op) ;;
          trigger (LocalWrite id dv)
        | (IId id, INSTR_Alloca dt _ _) =>
          dv <- trigger (Alloca dt);;
          trigger (LocalWrite id (dvalue_to_uvalue dv))
        | (IId id, INSTR_Load _ dt (du,ptr) _) =>
          ua <- translate exp_E_to_instr_E (denote_exp (Some du) ptr) ;;
          da <- concretize_or_pick ua True ;;
          match da with
          | DVALUE_Poison => raiseUB "Load from poisoned address."
          | _ => dv <- trigger (Load dt da);;
                trigger (LocalWrite id dv)
          end
        | (IVoid _, INSTR_Store _ (dt, val) (du, ptr) _) =>
          uv <- translate exp_E_to_instr_E (denote_exp (Some dt) val) ;;
          dv <- concretize_or_pick uv True ;;
          ua <- translate exp_E_to_instr_E (denote_exp (Some du) ptr) ;;
          da <- pickUnique ua ;;
          match da with
          | DVALUE_Poison => raiseUB "Store to poisoned address."
          | _ => trigger (Store da dv)
          end

        | (_, INSTR_Store _ _ _ _) => raise "ILL-FORMED itree ERROR: Store to non-void ID"
        | (pt, INSTR_Call (dt, f) args) =>
          uvs <- map_monad (fun '(t, op) => (translate exp_E_to_instr_E (denote_exp (Some t) op))) args ;;
          returned_value <-
          match Intrinsics.intrinsic_exp f with
          | Some s =>
            dvs <- map_monad (fun uv => pickUnique uv) uvs ;;
            fmap dvalue_to_uvalue (trigger (Intrinsic dt s dvs))
          | None =>
            fv <- translate exp_E_to_instr_E (denote_exp None f) ;;
            trigger (Call dt fv uvs)
          end
          ;;
          match pt with
          | IVoid _ => ret tt
          | IId id  => trigger (LocalWrite id returned_value)
          end

        | (_, INSTR_Comment _) => ret tt

        | (_, INSTR_Unreachable) => raise "IMPOSSIBLE: unreachable in reachable position"
        | (_, INSTR_Fence)
        | (_, INSTR_AtomicCmpXchg)
        | (_, INSTR_AtomicRMW)
        | (_, INSTR_VAArg)
        | (_, INSTR_LandingPad) => raise "Unsupported itree instruction"
        | (_, _) => raise "ID / Instr mismatch void/non-void"
        end.
      Definition denote_terminator (t: terminator dtyp): itree exp_E (block_id + uvalue) :=
        match t with

        | TERM_Ret (dt, op) =>
          dv <- denote_exp (Some dt) op ;;
          ret (inr dv)

        | TERM_Ret_void =>
          ret (inr UVALUE_None)

        | TERM_Br (dt,op) br1 br2 =>
          uv <- denote_exp (Some dt) op ;;
          dv <- concretize_or_pick uv True ;;
          match dv with
          | DVALUE_I1 comparison_bit =>
            if eq comparison_bit one then
              ret (inl br1)
            else
              ret (inl br2)
          | DVALUE_Poison => raiseUB "Branching on poison."
          | _ => raise "Br got non-bool value"
          end

        | TERM_Br_1 br => ret (inl br)
        | TERM_Switch _ _ _
        | TERM_IndirectBr _ _
        | TERM_Resume _
        | TERM_Invoke _ _ _ _ => raise "Unsupport itree terminator"
        end.
      Definition denote_code (c: code dtyp): itree instr_E unit :=
        map_monad_ denote_instr c.
      Definition denote_block (b: block dtyp) : itree instr_E (block_id + uvalue) :=
        denote_code (blk_code b);;
        translate exp_E_to_instr_E (denote_terminator (snd (blk_term b))).
      Definition denote_phi (bid : block_id) (id_p : local_id * phi dtyp) : itree exp_E (local_id * uvalue) :=
        let '(id, Phi dt args) := id_p in
        match assoc RawIDOrd.eq_dec bid args with
        | Some op =>
          uv <- denote_exp (Some dt) op ;;
          ret (id,uv)
        | None => raise ("jump: phi node doesn't include block " ++ to_string bid)
        end.
      
      Definition denote_bks (bks: list (block dtyp)): block_id -> itree instr_E (block_id + uvalue) :=
        iter (C := ktree _) (bif := sum) 
             (fun (bid_src : block_id) =>
                match find_block DynamicTypes.dtyp bks bid_src with
                | None => ret (inr (inl bid_src))
                | Some block_src =>
                  bd <- denote_block block_src;;
                  match bd with
                  | inr dv => ret (inr (inr dv))
                  | inl bid_target =>
                    match find_block DynamicTypes.dtyp bks bid_target with
                    | None => ret (inr (inl bid_target))
                    | Some block_target =>
                      dvs <- Util.map_monad
                              (fun x => translate exp_E_to_instr_E (denote_phi bid_src x))
                              (blk_phis block_target) ;;
                      Util.map_monad (fun '(id,dv) => trigger (LocalWrite id dv)) dvs;;
                      ret (inl bid_target)
                    end
                  end
                end).
      Definition denote_cfg (f: cfg dtyp) : itree instr_E uvalue :=
        r <- denote_bks (blks _ f) (init _ f) ;;
        match r with
        | inl bid => raise ("Can't find block in denote_cfg " ++ to_string bid)
        | inr uv  => ret uv
        end.
      Fixpoint combine_lists_err {A B:Type} (l1:list A) (l2:list B) : err (list (A * B)) :=
        match l1, l2 with
        | [], [] => ret []
        | x::xs, y::ys =>
          l <- combine_lists_err xs ys ;;
            ret ((x,y)::l)
        | _, _ =>
          ret []
        end.
      Definition function_denotation : Type :=
        list uvalue -> itree L0' uvalue.

      Definition denote_function (df:definition dtyp (cfg dtyp)) : function_denotation :=
        fun (args : list uvalue) =>
          bs <- lift_err ret (combine_lists_err (df_args df) args) ;;
          trigger MemPush ;;
          trigger (StackPush (map (fun '(k,v) => (k, v)) bs)) ;;
          rv <- translate instr_E_to_L0' (denote_cfg (df_instrs df)) ;;
          trigger StackPop ;;
          trigger MemPop ;;
          ret rv.
      Definition lookup_defn {B} := (@assoc _ B (@dvalue_eq_dec)).
      Definition denote_mcfg
                 (fundefs:list (dvalue * function_denotation)) (dt : dtyp)
                 (f_value : uvalue) (args : list uvalue) : itree L0 uvalue :=
        @mrec CallE (ExternalCallE +' _)
              (fun T call =>
                 match call with
                 | Call dt fv args =>
                   dfv <- concretize_or_pick fv True ;;
                   match (lookup_defn dfv fundefs) with
                   | Some f_den =>
                     f_den args
                   | None =>
                     dargs <- map_monad (fun uv => pickUnique uv) args ;;
                     fmap dvalue_to_uvalue (trigger (ExternalCall dt fv dargs))
                   end
                 end)
              _ (Call dt f_value args).

End Denotation.
