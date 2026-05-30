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

(* A64____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_73 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 16815).
Definition offset_70 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16816).
Definition DELTA_46 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16817).
Definition LEN_37 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16818).
Definition TRAIL_22 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16819).
Definition CUR_22 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16820).
Definition AT_52 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16821).
Definition w256_4 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16822).
Definition AT8_20 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16823).
Definition w_51 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16824).
Definition t128_11 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 16825).

(* Signature *)
Definition tyin_A64____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 64; aword U64; aint; aint; aint; aint; aint ].
Definition args_A64____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_73.(gv)
    ; offset_70.(gv)
    ; DELTA_46.(gv)
    ; LEN_37.(gv)
    ; TRAIL_22.(gv)
    ; CUR_22.(gv)
    ; AT_52.(gv) ].
Definition tyout_A64____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A64____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_46.(gv); LEN_37.(gv); TRAIL_22.(gv); AT_52.(gv); w256_4.(gv) ].

(* Body *)
Definition body_A64____a_ilen_read_bcast_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_52) (Pvar CUR_22)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_22) (Pconst (8)%Z)) (Pvar AT_52))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_37) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_22) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w256_4.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_37))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_20.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_52) (Pvar CUR_22)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_73 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_70) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_46)))) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_4.(gv) ] __SHLQ_256 [:: Pvar w256_4
                                                                    ; Pvar AT8_20 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_46.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_46) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_20))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_37.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_37) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_20))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT_52.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_22) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_20.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_52) (Pvar CUR_22)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_46.(gv)
                                                                  ; Lvar LEN_37.(gv)
                                                                  ; Lvar TRAIL_22.(gv)
                                                                  ; Lvar AT_52.(gv)
                                                                  ; Lvar w_51.(gv) ] A64____a_ilen_read_upto8_at [:: Pvar buf_73
                                                                    ; Pvar offset_70
                                                                    ; Pvar DELTA_46
                                                                    ; Pvar LEN_37
                                                                    ; Pvar TRAIL_22
                                                                    ; Pvar CUR_22
                                                                    ; Pvar AT_52 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_11.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_51)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_4.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_11 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_4.(gv) ] __SHLQ_256 [:: Pvar w256_4
                                                                    ; Pvar AT8_20 ]) ]) ]) ].

Definition fd_A64____a_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____a_ilen_read_bcast_upto8_at;
    f_params := args_A64____a_ilen_read_bcast_upto8_at;
    f_body := body_A64____a_ilen_read_bcast_upto8_at;
    f_tyout := tyout_A64____a_ilen_read_bcast_upto8_at;
    f_res := res_A64____a_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
