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

(* A2____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_34 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17920).
Definition offset_22 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17921).
Definition DELTA_16 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17922).
Definition LEN_19 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17923).
Definition w_24 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17924).
Definition t128_6 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 17925).

(* Signature *)
Definition tyin_A2____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 2; aword U64; aint; aint; aword U256 ].
Definition args_A2____a_ilen_write_upto32 : seq var_i :=
  [:: buf_34.(gv); offset_22.(gv); DELTA_16.(gv); LEN_19.(gv); w_24.(gv) ].
Definition tyout_A2____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 2; aint; aint ].
Definition res_A2____a_ilen_write_upto32 : seq var_i :=
  [:: buf_34.(gv); DELTA_16.(gv); LEN_19.(gv) ].

(* Body *)
Definition body_A2____a_ilen_write_upto32 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_19))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_19))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 buf_34.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_22) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16))))) AT_none (aword U256) (Pvar w_24))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_16.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_19.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_19) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_6.(gv)) AT_none (aword U128) (Pvar w_24))
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_19))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U128 buf_34.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_22) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16))))) AT_none (aword U128) (Pvar t128_6))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_16.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_19.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_19) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_6.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_24
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_34.(gv)
                                                                  ; Lvar DELTA_16.(gv)
                                                                  ; Lvar LEN_19.(gv) ] A2____a_ilen_write_upto16 [:: Pvar buf_34
                                                                    ; Pvar offset_22
                                                                    ; Pvar DELTA_16
                                                                    ; Pvar LEN_19
                                                                    ; Pvar t128_6 ]) ]) ]
                              [::]) ].

Definition fd_A2____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____a_ilen_write_upto32;
    f_params := args_A2____a_ilen_write_upto32;
    f_body := body_A2____a_ilen_write_upto32;
    f_tyout := tyout_A2____a_ilen_write_upto32;
    f_res := res_A2____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
