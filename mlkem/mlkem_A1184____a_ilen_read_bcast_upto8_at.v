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

(* A1184____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_99 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16186).
Definition offset_98 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16187).
Definition DELTA_66 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16188).
Definition LEN_51 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16189).
Definition TRAIL_30 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16190).
Definition CUR_30 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16191).
Definition AT_68 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16192).
Definition w256_6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16193).
Definition AT8_26 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16194).
Definition w_70 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16195).
Definition t128_15 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 16196).

(* Signature *)
Definition tyin_A1184____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 1184; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1184____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_99.(gv)
    ; offset_98.(gv)
    ; DELTA_66.(gv)
    ; LEN_51.(gv)
    ; TRAIL_30.(gv)
    ; CUR_30.(gv)
    ; AT_68.(gv) ].
Definition tyout_A1184____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1184____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_66.(gv); LEN_51.(gv); TRAIL_30.(gv); AT_68.(gv); w256_6.(gv) ].

(* Body *)
Definition body_A1184____a_ilen_read_bcast_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_68) (Pvar CUR_30)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_30) (Pconst (8)%Z)) (Pvar AT_68))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_51) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_30) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w256_6.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_51))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_26.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_68) (Pvar CUR_30)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_6.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_99 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_98) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_66)))) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_6.(gv) ] __SHLQ_256 [:: Pvar w256_6
                                                                    ; Pvar AT8_26 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_66.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_66) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_26))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_51.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_51) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_26))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT_68.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_30) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_26.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_68) (Pvar CUR_30)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_66.(gv)
                                                                  ; Lvar LEN_51.(gv)
                                                                  ; Lvar TRAIL_30.(gv)
                                                                  ; Lvar AT_68.(gv)
                                                                  ; Lvar w_70.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf_99
                                                                    ; Pvar offset_98
                                                                    ; Pvar DELTA_66
                                                                    ; Pvar LEN_51
                                                                    ; Pvar TRAIL_30
                                                                    ; Pvar CUR_30
                                                                    ; Pvar AT_68 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_15.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_70)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_6.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_15 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_6.(gv) ] __SHLQ_256 [:: Pvar w256_6
                                                                    ; Pvar AT8_26 ]) ]) ]) ].

Definition fd_A1184____a_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____a_ilen_read_bcast_upto8_at;
    f_params := args_A1184____a_ilen_read_bcast_upto8_at;
    f_body := body_A1184____a_ilen_read_bcast_upto8_at;
    f_tyout := tyout_A1184____a_ilen_read_bcast_upto8_at;
    f_res := res_A1184____a_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
