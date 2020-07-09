From Coq Require Import
     ZArith List String.

From ExtLib Require Import
     Structures.Monads
     Programming.Eqv
     Data.String.

From Vir Require Import
     LLVMEvents
     LLVMAst
     Error
     Coqlib
     Numeric.Integers
     Numeric.Floats.

From ITree Require Import
     ITree.

Import MonadNotation.
Import EqvNotation.
Import ListNotations.

Set Implicit Arguments.
Set Contextual Implicit.

Definition fabs_32_decl: declaration typ :=
  {|
    dc_name        := Name "llvm.fabs.f32";
    dc_type        := TYPE_Function TYPE_Float [TYPE_Float] ;
    dc_param_attrs := ([], [[]]);
    dc_linkage     := None ;
    dc_visibility  := None ;
    dc_dll_storage := None ;
    dc_cconv       := None ;
    dc_attrs       := [] ;
    dc_section     := None ;
    dc_align       := None ;
    dc_gc          := None
  |}.


Definition fabs_64_decl: declaration typ :=
  {|
    dc_name        := Name "llvm.fabs.f64";
    dc_type        := TYPE_Function TYPE_Double [TYPE_Double] ;
    dc_param_attrs := ([], [[]]);
    dc_linkage     := None ;
    dc_visibility  := None ;
    dc_dll_storage := None ;
    dc_cconv       := None ;
    dc_attrs       := [] ;
    dc_section     := None ;
    dc_align       := None ;
    dc_gc          := None
  |}.

Definition memcpy_8_decl: declaration typ :=
  let pt := TYPE_Pointer (TYPE_I 8%Z) in
  let i32 := TYPE_I 32%Z in
  let i1 := TYPE_I 1%Z in
  {|
    dc_name        := Name "llvm.memcpy.p0i8.p0i8.i32";
    dc_type        := TYPE_Function TYPE_Void [pt; pt; i32; i32; i1] ;
    dc_param_attrs := ([], [[];[];[];[];[]]);
    dc_linkage     := None ;
    dc_visibility  := None ;
    dc_dll_storage := None ;
    dc_cconv       := None ;
    dc_attrs       := [] ;
    dc_section     := None ;
    dc_align       := None ;
    dc_gc          := None
  |}.
Definition defined_intrinsics_decls :=
  [ fabs_32_decl; fabs_64_decl; memcpy_8_decl ].
Module Make(A:MemoryAddress.ADDRESS)(LLVMIO: LLVM_INTERACTIONS(A)).
  Open Scope string_scope.

  Import LLVMIO.
  Import DV.
  Definition semantic_function := (list dvalue) -> err dvalue.
  Definition intrinsic_definitions := list (declaration typ * semantic_function).
  Definition llvm_fabs_f32 : semantic_function :=
    fun args =>
      match args with
      | [DVALUE_Float d] => ret (DVALUE_Float (Float32.abs d))
      | _ => failwith "llvm_fabs_f64 got incorrect / ill-typed intputs"
      end.
  Definition llvm_fabs_f64 : semantic_function :=
    fun args =>
      match args with
      | [DVALUE_Double d] => ret (DVALUE_Double (Float.abs d))
      | _ => failwith "llvm_fabs_f64 got incorrect / ill-typed intputs"
      end.
  Definition defined_intrinsics : intrinsic_definitions :=
    [ (fabs_32_decl, llvm_fabs_f32) ;
    (fabs_64_decl, llvm_fabs_f64) ].

End Make.
