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

(* A32____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_48 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17538).
Definition offset_39 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17539).
Definition DELTA_27 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17540).
Definition LEN_26 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17541).
Definition w_34 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17542).
Definition t128_8 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 17543).

(* Signature *)
Definition tyin_A32____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 32; aword U64; aint; aint; aword U256 ].
Definition args_A32____a_ilen_write_upto32 : seq var_i :=
  [:: buf_48.(gv); offset_39.(gv); DELTA_27.(gv); LEN_26.(gv); w_34.(gv) ].
Definition tyout_A32____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 32; aint; aint ].
Definition res_A32____a_ilen_write_upto32 : seq var_i :=
  [:: buf_48.(gv); DELTA_27.(gv); LEN_26.(gv) ].

(* Body *)
Definition body_A32____a_ilen_write_upto32 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_26))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_26))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 buf_48.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_39) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_27))))) AT_none (aword U256) (Pvar w_34))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_27.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_27) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_26.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_26) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_8.(gv)) AT_none (aword U128) (Pvar w_34))
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_26))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U128 buf_48.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_39) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_27))))) AT_none (aword U128) (Pvar t128_8))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_27.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_27) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_26.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_26) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_8.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_34
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_48.(gv)
                                                                  ; Lvar DELTA_27.(gv)
                                                                  ; Lvar LEN_26.(gv) ] A32____a_ilen_write_upto16 [:: Pvar buf_48
                                                                    ; Pvar offset_39
                                                                    ; Pvar DELTA_27
                                                                    ; Pvar LEN_26
                                                                    ; Pvar t128_8 ]) ]) ]
                              [::]) ].

Definition fd_A32____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____a_ilen_write_upto32;
    f_params := args_A32____a_ilen_write_upto32;
    f_body := body_A32____a_ilen_write_upto32;
    f_tyout := tyout_A32____a_ilen_write_upto32;
    f_res := res_A32____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
