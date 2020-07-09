(* -------------------------------------------------------------------------- *
 *                     Vir - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith List String Omega.
Require Import Program.
Require Import Vir.Util.
Require Import Vir.LLVMAst Vir.AstLib Vir.CFG Vir.CFGProp.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Require Import Vir.Handlers.Memory.

Definition optimization {T} := definition T (list (block T)) -> definition T (list (block T)).

Definition optimize {T} (m:modul T (list (block T))) (o:optimization) : modul T (list (block T)) :=
 {|
  m_name := (m_name m);
  m_target := (m_target m);
  m_datalayout := (m_datalayout m);
  m_type_defs := (m_type_defs m);
  m_globals := (m_globals m);
  m_declarations := (m_declarations m);
  m_definitions := map o (m_definitions m);
 |}.
