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

(* A64____a_ilen_write_upto16 *)
(* Local variables *)
Definition buf_75 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 16788).
Definition offset_72 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16789).
Definition DELTA_48 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16790).
Definition LEN_39 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16791).
Definition w_53 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 16792).
Definition t64_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16793).

(* Signature *)
Definition tyin_A64____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 64; aword U64; aint; aint; aword U128 ].
Definition args_A64____a_ilen_write_upto16 : seq var_i :=
  [:: buf_75.(gv); offset_72.(gv); DELTA_48.(gv); LEN_39.(gv); w_53.(gv) ].
Definition tyout_A64____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 64; aint; aint ].
Definition res_A64____a_ilen_write_upto16 : seq var_i :=
  [:: buf_75.(gv); DELTA_48.(gv); LEN_39.(gv) ].

(* Body *)
Definition body_A64____a_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_39))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_39))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U128 buf_75.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_72) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_48))))) AT_none (aword U128) (Pvar w_53))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_48.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_48) (Pconst (16)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_39.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_39) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_39))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Laset Unaligned AAdirect U64 buf_75.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_72) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_48)))) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_53 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_48.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_48) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_39.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_39) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_53.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_53
                                                                    ; Pvar w_53 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64_6.(gv)) AT_none (aword U64) (Pvar w_53))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_75.(gv)
                                                                  ; Lvar DELTA_48.(gv)
                                                                  ; Lvar LEN_39.(gv) ] A64____a_ilen_write_upto8 [:: Pvar buf_75
                                                                    ; Pvar offset_72
                                                                    ; Pvar DELTA_48
                                                                    ; Pvar LEN_39
                                                                    ; Pvar t64_6 ]) ]) ]
                              [::]) ].

Definition fd_A64____a_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____a_ilen_write_upto16;
    f_params := args_A64____a_ilen_write_upto16;
    f_body := body_A64____a_ilen_write_upto16;
    f_tyout := tyout_A64____a_ilen_write_upto16;
    f_res := res_A64____a_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
