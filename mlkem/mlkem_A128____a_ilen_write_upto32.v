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

(* A128____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_88 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 16527).
Definition offset_84 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16528).
Definition DELTA_58 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16529).
Definition LEN_47 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16530).
Definition w_63 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16531).
Definition t128_14 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 16532).

(* Signature *)
Definition tyin_A128____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 128; aword U64; aint; aint; aword U256 ].
Definition args_A128____a_ilen_write_upto32 : seq var_i :=
  [:: buf_88.(gv); offset_84.(gv); DELTA_58.(gv); LEN_47.(gv); w_63.(gv) ].
Definition tyout_A128____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 128; aint; aint ].
Definition res_A128____a_ilen_write_upto32 : seq var_i :=
  [:: buf_88.(gv); DELTA_58.(gv); LEN_47.(gv) ].

(* Body *)
Definition body_A128____a_ilen_write_upto32 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_47))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_47))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 buf_88.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_84) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_58))))) AT_none (aword U256) (Pvar w_63))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_58.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_58) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_47.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_47) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_14.(gv)) AT_none (aword U128) (Pvar w_63))
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_47))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U128 buf_88.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_84) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_58))))) AT_none (aword U128) (Pvar t128_14))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_58.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_58) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_47.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_47) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_14.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_63
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_88.(gv)
                                                                  ; Lvar DELTA_58.(gv)
                                                                  ; Lvar LEN_47.(gv) ] A128____a_ilen_write_upto16 [:: Pvar buf_88
                                                                    ; Pvar offset_84
                                                                    ; Pvar DELTA_58
                                                                    ; Pvar LEN_47
                                                                    ; Pvar t128_14 ]) ]) ]
                              [::]) ].

Definition fd_A128____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____a_ilen_write_upto32;
    f_params := args_A128____a_ilen_write_upto32;
    f_body := body_A128____a_ilen_write_upto32;
    f_tyout := tyout_A128____a_ilen_write_upto32;
    f_res := res_A128____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
