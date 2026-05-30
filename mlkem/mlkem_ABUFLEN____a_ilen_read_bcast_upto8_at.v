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

(* ABUFLEN____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_155 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14658).
Definition offset_166 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14659).
Definition DELTA_110 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14660).
Definition LEN_79 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14661).
Definition TRAIL_46 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14662).
Definition CUR_46 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14663).
Definition AT_108 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14664).
Definition w256_10 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14665).
Definition AT8_42 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14666).
Definition w_110 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14667).
Definition t128_23 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 14668).

(* Signature *)
Definition tyin_ABUFLEN____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 536; aword U64; aint; aint; aint; aint; aint ].
Definition args_ABUFLEN____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_155.(gv)
    ; offset_166.(gv)
    ; DELTA_110.(gv)
    ; LEN_79.(gv)
    ; TRAIL_46.(gv)
    ; CUR_46.(gv)
    ; AT_108.(gv) ].
Definition tyout_ABUFLEN____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_ABUFLEN____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_110.(gv); LEN_79.(gv); TRAIL_46.(gv); AT_108.(gv); w256_10.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_ilen_read_bcast_upto8_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_108) (Pvar CUR_46)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_46) (Pconst (8)%Z)) (Pvar AT_108))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_79) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_46) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w256_10.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U256)))) [::]) ]
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_79))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_42.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_108) (Pvar CUR_46)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_155 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_166) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_110)))) ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_10.(gv) ] __SHLQ_256 [:: Pvar w256_10
                                                                    ; Pvar AT8_42 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_110.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_110) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_42))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_79.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_79) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_42))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT_108.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_46) (Pconst (8)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar AT8_42.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_108) (Pvar CUR_46)))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar DELTA_110.(gv)
                                                                  ; Lvar LEN_79.(gv)
                                                                  ; Lvar TRAIL_46.(gv)
                                                                  ; Lvar AT_108.(gv)
                                                                  ; Lvar w_110.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_155
                                                                    ; Pvar offset_166
                                                                    ; Pvar DELTA_110
                                                                    ; Pvar LEN_79
                                                                    ; Pvar TRAIL_46
                                                                    ; Pvar CUR_46
                                                                    ; Pvar AT_108 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_23.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_110)))
                                                            ; MkI dummy_instr_info (
                                                          Copn [:: Lvar w256_10.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_23 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w256_10.(gv) ] __SHLQ_256 [:: Pvar w256_10
                                                                    ; Pvar AT8_42 ]) ]) ]) ].

Definition fd_ABUFLEN____a_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____a_ilen_read_bcast_upto8_at;
    f_params := args_ABUFLEN____a_ilen_read_bcast_upto8_at;
    f_body := body_ABUFLEN____a_ilen_read_bcast_upto8_at;
    f_tyout := tyout_ABUFLEN____a_ilen_read_bcast_upto8_at;
    f_res := res_ABUFLEN____a_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
