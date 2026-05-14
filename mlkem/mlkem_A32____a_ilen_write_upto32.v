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
Definition buf_17538 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17538).
Definition offset_17539 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17539).
Definition DELTA_17540 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17540).
Definition LEN_17541 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17541).
Definition w_17542 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17542).
Definition t128_17543 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17543).

(* Signature *)
Definition tyin_A32____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 32; aword U64; aint; aint; aword U256 ].
Definition args_A32____a_ilen_write_upto32 : seq var_i :=
  [:: buf_17538.(gv)
    ; offset_17539.(gv)
    ; DELTA_17540.(gv)
    ; LEN_17541.(gv)
    ; w_17542.(gv) ].
Definition tyout_A32____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 32; aint; aint ].
Definition res_A32____a_ilen_write_upto32 : seq var_i :=
  [:: buf_17538.(gv); DELTA_17540.(gv); LEN_17541.(gv) ].

(* Body *)
Definition body_A32____a_ilen_write_upto32 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_17541))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_17541))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 buf_17538.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17539) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17540))))) AT_none (aword U256) (Pvar w_17542))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_17540.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17540) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_17541.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17541) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_17543.(gv)) AT_none (aword U128) (Pvar w_17542))
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_17541))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U128 buf_17538.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17539) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17540))))) AT_none (aword U128) (Pvar t128_17543))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_17540.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17540) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_17541.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17541) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_17543.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_17542
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_17538.(gv)
                                                                  ; Lvar DELTA_17540.(gv)
                                                                  ; Lvar LEN_17541.(gv) ] A32____a_ilen_write_upto16 [:: Pvar buf_17538
                                                                    ; Pvar offset_17539
                                                                    ; Pvar DELTA_17540
                                                                    ; Pvar LEN_17541
                                                                    ; Pvar t128_17543 ]) ]) ]
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
