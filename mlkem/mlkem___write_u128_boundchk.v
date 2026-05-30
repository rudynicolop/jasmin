From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* __write_u128_boundchk *)
(* Local variables *)
Definition pol_0 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13838).
Definition ctr : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13839).
Definition data_11 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 13840).
Definition ms_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13841).
Definition condition_8 : gvar := mk_rocq_gvar Slocal (abool) (mkident 13842).
Definition data_u64 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13843).
Definition condition_4 : gvar := mk_rocq_gvar Slocal (abool) (mkident 13844).
Definition condition_2 : gvar := mk_rocq_gvar Slocal (abool) (mkident 13845).
Definition condition_1 : gvar := mk_rocq_gvar Slocal (abool) (mkident 13846).

(* Signature *)
Definition tyin___write_u128_boundchk : seq atype :=
  [:: aarr U16 256; aword U64; aword U128; aword U64 ].
Definition args___write_u128_boundchk : seq var_i :=
  [:: pol_0.(gv); ctr.(gv); data_11.(gv); ms_0.(gv) ].
Definition tyout___write_u128_boundchk : seq atype :=
  [:: aarr U16 256; aword U64 ].
Definition res___write_u128_boundchk : seq var_i :=
  [:: pol_0.(gv); ms_0.(gv) ].

(* Body *)
Definition body___write_u128_boundchk : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar condition_8.(gv)) AT_none (abool) (Papp2 (Ole (Cmp_w Unsigned U64)) (Pvar ctr) (Papp1 (Oword_of_int U64) (Papp2 (Osub (Op_int)) (Pconst (256)%Z) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cif
                              (Pvar condition_8)
                              [:: MkI dummy_instr_info (Copn [:: Lvar ms_0.(gv) ] AT_none (Oslh (SLHupdate)) [:: Pvar condition_8
                                                                    ; Pvar ms_0 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U128 pol_0.(gv) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Papp1 (Oint_of_word Unsigned U64) (Pvar ctr)))) AT_none (aword U128) (Pvar data_11)) ]
                              [:: MkI dummy_instr_info (Copn [:: Lvar ms_0.(gv) ] AT_none (Oslh (SLHupdate)) [:: Papp1 (Onot) (Pvar condition_8)
                                                                    ; Pvar ms_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar data_u64.(gv) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar data_11 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar condition_4.(gv)) AT_none (abool) (Papp2 (Ole (Cmp_w Unsigned U64)) (Pvar ctr) (Papp1 (Oword_of_int U64) (Papp2 (Osub (Op_int)) (Pconst (256)%Z) (Pconst (4)%Z)))))
                                ; MkI dummy_instr_info (Cif
                                                          (Pvar condition_4)
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar ms_0.(gv) ] AT_none (Oslh (SLHupdate)) [:: Pvar condition_4
                                                                    ; Pvar ms_0 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U64 pol_0.(gv) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Papp1 (Oint_of_word Unsigned U64) (Pvar ctr)))) AT_none (aword U64) (Pvar data_u64))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar data_u64.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPEXTR U64))))) [:: Pvar data_11
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar ctr.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar ctr) (Papp1 (Oword_of_int U64) (Pconst (4)%Z)))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar ms_0.(gv) ] AT_none (Oslh (SLHupdate)) [:: Papp1 (Onot) (Pvar condition_4)
                                                                    ; Pvar ms_0 ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar condition_2.(gv)) AT_none (abool) (Papp2 (Ole (Cmp_w Unsigned U64)) (Pvar ctr) (Papp1 (Oword_of_int U64) (Papp2 (Osub (Op_int)) (Pconst (256)%Z) (Pconst (2)%Z)))))
                                ; MkI dummy_instr_info (Cif
                                                          (Pvar condition_2)
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar ms_0.(gv) ] AT_none (Oslh (SLHupdate)) [:: Pvar condition_2
                                                                    ; Pvar ms_0 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U32 pol_0.(gv) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Papp1 (Oint_of_word Unsigned U64) (Pvar ctr)))) AT_none (aword U32) (Pvar data_u64))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar data_u64.(gv)) AT_none (aword U64) (Papp2 (Olsr U64) (Pvar data_u64) (Papp1 (Oword_of_int U8) (Pconst (32)%Z))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar ctr.(gv)) AT_none (aword U64) (Papp2 (Oadd (Op_w U64)) (Pvar ctr) (Papp1 (Oword_of_int U64) (Pconst (2)%Z)))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar ms_0.(gv) ] AT_none (Oslh (SLHupdate)) [:: Papp1 (Onot) (Pvar condition_2)
                                                                    ; Pvar ms_0 ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar condition_1.(gv)) AT_none (abool) (Papp2 (Ole (Cmp_w Unsigned U64)) (Pvar ctr) (Papp1 (Oword_of_int U64) (Papp2 (Osub (Op_int)) (Pconst (256)%Z) (Pconst (1)%Z)))))
                                ; MkI dummy_instr_info (Cif
                                                          (Pvar condition_1)
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar ms_0.(gv) ] AT_none (Oslh (SLHupdate)) [:: Pvar condition_1
                                                                    ; Pvar ms_0 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U16 pol_0.(gv) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Papp1 (Oint_of_word Unsigned U64) (Pvar ctr)))) AT_none (aword U16) (Pvar data_u64)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Copn [:: Lvar ms_0.(gv) ] AT_none (Oslh (SLHupdate)) [:: Papp1 (Onot) (Pvar condition_1)
                                                                    ; Pvar ms_0 ]) ]) ]) ].

Definition fd___write_u128_boundchk : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___write_u128_boundchk;
    f_params := args___write_u128_boundchk;
    f_body := body___write_u128_boundchk;
    f_tyout := tyout___write_u128_boundchk;
    f_res := res___write_u128_boundchk;
    f_extra := tt;
  |}.

End IDO.
