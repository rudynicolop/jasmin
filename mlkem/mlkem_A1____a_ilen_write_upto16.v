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

(* A1____a_ilen_write_upto16 *)
(* Local variables *)
Definition buf_18316 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18316).
Definition offset_18317 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18317).
Definition DELTA_18318 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18318).
Definition LEN_18319 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18319).
Definition w_18320 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 18320).
Definition t64_18321 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18321).

(* Signature *)
Definition tyin_A1____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 1; aword U64; aint; aint; aword U128 ].
Definition args_A1____a_ilen_write_upto16 : seq var_i :=
  [:: buf_18316.(gv)
    ; offset_18317.(gv)
    ; DELTA_18318.(gv)
    ; LEN_18319.(gv)
    ; w_18320.(gv) ].
Definition tyout_A1____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 1; aint; aint ].
Definition res_A1____a_ilen_write_upto16 : seq var_i :=
  [:: buf_18316.(gv); DELTA_18318.(gv); LEN_18319.(gv) ].

(* Body *)
Definition body_A1____a_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_18319))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_18319))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U128 buf_18316.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18317) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18318))))) AT_none (aword U128) (Pvar w_18320))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_18318.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18318) (Pconst (16)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_18319.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18319) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_18319))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Laset Unaligned AAdirect U64 buf_18316.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18317) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18318)))) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_18320 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_18318.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18318) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_18319.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18319) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_18320.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_18320
                                                                    ; Pvar w_18320 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64_18321.(gv)) AT_none (aword U64) (Pvar w_18320))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_18316.(gv)
                                                                  ; Lvar DELTA_18318.(gv)
                                                                  ; Lvar LEN_18319.(gv) ] A1____a_ilen_write_upto8 [:: Pvar buf_18316
                                                                    ; Pvar offset_18317
                                                                    ; Pvar DELTA_18318
                                                                    ; Pvar LEN_18319
                                                                    ; Pvar t64_18321 ]) ]) ]
                              [::]) ].

Definition fd_A1____a_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____a_ilen_write_upto16;
    f_params := args_A1____a_ilen_write_upto16;
    f_body := body_A1____a_ilen_write_upto16;
    f_tyout := tyout_A1____a_ilen_write_upto16;
    f_res := res_A1____a_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
