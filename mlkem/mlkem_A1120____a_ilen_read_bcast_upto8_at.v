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

(* A1120____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_127 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15422).
Definition offset_132 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15423).
Definition DELTA_88 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15424).
Definition LEN_65 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15425).
Definition TRAIL_38 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15426).
Definition CUR_38 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15427).
Definition AT_88 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15428).
Definition w256_8 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15429).
Definition AT8_34 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15430).
Definition w_90 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15431).
Definition t128_19 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 15432).

(* Signature *)
Definition tyin_A1120____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 1120; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1120____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_127.(gv)
    ; offset_132.(gv)
    ; DELTA_88.(gv)
    ; LEN_65.(gv)
    ; TRAIL_38.(gv)
    ; CUR_38.(gv)
    ; AT_88.(gv) ].
Definition tyout_A1120____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1120____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_88.(gv); LEN_65.(gv); TRAIL_38.(gv); AT_88.(gv); w256_8.(gv) ].

(* Body *)
Definition body_A1120____a_ilen_read_bcast_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_88) (Pvar CUR_38)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_38) (Pconst (8)%Z)) (Pvar AT_88))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_65) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_38) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w256_8.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_65))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_34.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_88) (Pvar CUR_38)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_127 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_132) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_88)))) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_8.(gv) ] __SHLQ_256 [:: Pvar w256_8
                                                                    ; Pvar AT8_34 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_88.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_88) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_34))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_65.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_65) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_34))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT_88.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_38) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_34.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_88) (Pvar CUR_38)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_88.(gv)
                                                                  ; Lvar LEN_65.(gv)
                                                                  ; Lvar TRAIL_38.(gv)
                                                                  ; Lvar AT_88.(gv)
                                                                  ; Lvar w_90.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf_127
                                                                    ; Pvar offset_132
                                                                    ; Pvar DELTA_88
                                                                    ; Pvar LEN_65
                                                                    ; Pvar TRAIL_38
                                                                    ; Pvar CUR_38
                                                                    ; Pvar AT_88 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_19.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_90)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_8.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_19 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_8.(gv) ] __SHLQ_256 [:: Pvar w256_8
                                                                    ; Pvar AT8_34 ]) ]) ]) ].

Definition fd_A1120____a_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____a_ilen_read_bcast_upto8_at;
    f_params := args_A1120____a_ilen_read_bcast_upto8_at;
    f_body := body_A1120____a_ilen_read_bcast_upto8_at;
    f_tyout := tyout_A1120____a_ilen_read_bcast_upto8_at;
    f_res := res_A1120____a_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
