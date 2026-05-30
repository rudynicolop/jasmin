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

(* A2____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_31 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17961).
Definition offset_19 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17962).
Definition DELTA_13 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17963).
Definition LEN_16 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17964).
Definition TRAIL_10 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17965).
Definition CUR_10 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17966).
Definition AT_22 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17967).
Definition w256_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17968).
Definition AT8_8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17969).
Definition w_21 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17970).
Definition t128_5 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 17971).

(* Signature *)
Definition tyin_A2____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 2; aword U64; aint; aint; aint; aint; aint ].
Definition args_A2____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_31.(gv)
    ; offset_19.(gv)
    ; DELTA_13.(gv)
    ; LEN_16.(gv)
    ; TRAIL_10.(gv)
    ; CUR_10.(gv)
    ; AT_22.(gv) ].
Definition tyout_A2____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A2____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_13.(gv); LEN_16.(gv); TRAIL_10.(gv); AT_22.(gv); w256_1.(gv) ].

(* Body *)
Definition body_A2____a_ilen_read_bcast_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_22) (Pvar CUR_10)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_10) (Pconst (8)%Z)) (Pvar AT_22))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_16) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_10) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w256_1.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_16))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_8.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_22) (Pvar CUR_10)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_31 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_19) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_13)))) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_1.(gv) ] __SHLQ_256 [:: Pvar w256_1
                                                                    ; Pvar AT8_8 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_13.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_13) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_8))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_16.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_8))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT_22.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_10) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_8.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_22) (Pvar CUR_10)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_13.(gv)
                                                                  ; Lvar LEN_16.(gv)
                                                                  ; Lvar TRAIL_10.(gv)
                                                                  ; Lvar AT_22.(gv)
                                                                  ; Lvar w_21.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_31
                                                                    ; Pvar offset_19
                                                                    ; Pvar DELTA_13
                                                                    ; Pvar LEN_16
                                                                    ; Pvar TRAIL_10
                                                                    ; Pvar CUR_10
                                                                    ; Pvar AT_22 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_5.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_21)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_5 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_1.(gv) ] __SHLQ_256 [:: Pvar w256_1
                                                                    ; Pvar AT8_8 ]) ]) ]) ].

Definition fd_A2____a_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____a_ilen_read_bcast_upto8_at;
    f_params := args_A2____a_ilen_read_bcast_upto8_at;
    f_body := body_A2____a_ilen_read_bcast_upto8_at;
    f_tyout := tyout_A2____a_ilen_read_bcast_upto8_at;
    f_res := res_A2____a_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
