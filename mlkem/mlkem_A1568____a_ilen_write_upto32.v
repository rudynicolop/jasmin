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

(* A1568____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_116 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15763).
Definition offset_118 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15764).
Definition DELTA_80 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15765).
Definition LEN_61 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15766).
Definition w_83 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15767).
Definition t128_18 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 15768).

(* Signature *)
Definition tyin_A1568____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 1568; aword U64; aint; aint; aword U256 ].
Definition args_A1568____a_ilen_write_upto32 : seq var_i :=
  [:: buf_116.(gv); offset_118.(gv); DELTA_80.(gv); LEN_61.(gv); w_83.(gv) ].
Definition tyout_A1568____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 1568; aint; aint ].
Definition res_A1568____a_ilen_write_upto32 : seq var_i :=
  [:: buf_116.(gv); DELTA_80.(gv); LEN_61.(gv) ].

(* Body *)
Definition body_A1568____a_ilen_write_upto32 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_61))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_61))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 buf_116.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_118) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_80))))) AT_none (aword U256) (Pvar w_83))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_80.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_80) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_61.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_61) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_18.(gv)) AT_none (aword U128) (Pvar w_83))
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_61))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U128 buf_116.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_118) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_80))))) AT_none (aword U128) (Pvar t128_18))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_80.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_80) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_61.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_61) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_18.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_83
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_116.(gv)
                                                                  ; Lvar DELTA_80.(gv)
                                                                  ; Lvar LEN_61.(gv) ] A1568____a_ilen_write_upto16 [:: Pvar buf_116
                                                                    ; Pvar offset_118
                                                                    ; Pvar DELTA_80
                                                                    ; Pvar LEN_61
                                                                    ; Pvar t128_18 ]) ]) ]
                              [::]) ].

Definition fd_A1568____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____a_ilen_write_upto32;
    f_params := args_A1568____a_ilen_write_upto32;
    f_body := body_A1568____a_ilen_write_upto32;
    f_tyout := tyout_A1568____a_ilen_write_upto32;
    f_res := res_A1568____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
