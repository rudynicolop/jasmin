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
Definition buf_15422 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15422).
Definition offset_15423 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15423).
Definition DELTA_15424 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15424).
Definition LEN_15425 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15425).
Definition TRAIL_15426 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15426).
Definition CUR_15427 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15427).
Definition AT_15428 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15428).
Definition w256_15429 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15429).
Definition AT8_15430 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15430).
Definition w_15431 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15431).
Definition t128_15432 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15432).

(* Signature *)
Definition tyin_A1120____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 1120; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1120____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_15422.(gv)
    ; offset_15423.(gv)
    ; DELTA_15424.(gv)
    ; LEN_15425.(gv)
    ; TRAIL_15426.(gv)
    ; CUR_15427.(gv)
    ; AT_15428.(gv) ].
Definition tyout_A1120____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1120____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_15424.(gv)
    ; LEN_15425.(gv)
    ; TRAIL_15426.(gv)
    ; AT_15428.(gv)
    ; w256_15429.(gv) ].

(* Body *)
Definition body_A1120____a_ilen_read_bcast_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_15428) (Pvar CUR_15427)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_15427) (Pconst (8)%Z)) (Pvar AT_15428))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_15425) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_15426) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w256_15429.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_15425))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_15430.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_15428) (Pvar CUR_15427)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_15429.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_15422 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15423) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15424)))) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_15429.(gv) ] __SHLQ_256 [:: Pvar w256_15429
                                                                    ; Pvar AT8_15430 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_15424.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15424) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15430))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_15425.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15425) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15430))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT_15428.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_15427) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_15430.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_15428) (Pvar CUR_15427)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_15424.(gv)
                                                                  ; Lvar LEN_15425.(gv)
                                                                  ; Lvar TRAIL_15426.(gv)
                                                                  ; Lvar AT_15428.(gv)
                                                                  ; Lvar w_15431.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf_15422
                                                                    ; Pvar offset_15423
                                                                    ; Pvar DELTA_15424
                                                                    ; Pvar LEN_15425
                                                                    ; Pvar TRAIL_15426
                                                                    ; Pvar CUR_15427
                                                                    ; Pvar AT_15428 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_15432.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_15431)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_15429.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_15432 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_15429.(gv) ] __SHLQ_256 [:: Pvar w256_15429
                                                                    ; Pvar AT8_15430 ]) ]) ]) ].

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
