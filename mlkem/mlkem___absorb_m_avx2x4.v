From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi syntax data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* __absorb_m_avx2x4 *)
(* Local variables *)
Definition st_18478 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 18478).
Definition AT_18479 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18479).
Definition buf0_18480 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18480).
Definition buf1_18481 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18481).
Definition buf2_18482 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18482).
Definition buf3_18483 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18483).
Definition _LEN_18484 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18484).
Definition _TRAILB_18485 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18485).
Definition _RATE8_18486 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18486).
Definition ITERS_18487 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18487).
Definition i_18488 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18488).

(* Signature *)
Definition tyin___absorb_m_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aword U64
    ; aword U64
    ; aword U64
    ; aword U64
    ; aint
    ; aint
    ; aint ].
Definition args___absorb_m_avx2x4 : seq var_i :=
  [:: st_18478.(gv)
    ; AT_18479.(gv)
    ; buf0_18480.(gv)
    ; buf1_18481.(gv)
    ; buf2_18482.(gv)
    ; buf3_18483.(gv)
    ; _LEN_18484.(gv)
    ; _TRAILB_18485.(gv)
    ; _RATE8_18486.(gv) ].
Definition tyout___absorb_m_avx2x4 : seq atype := [:: aarr U256 25; aint ].
Definition res___absorb_m_avx2x4 : seq var_i :=
  [:: st_18478.(gv); AT_18479.(gv) ].

(* Body *)
Definition body___absorb_m_avx2x4 : cmd :=
  [:: cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_18479) (Pvar _LEN_18484)) (Pvar _RATE8_18486))
        [:: ccall [:: Lvar st_18478.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar buf0_18480.(gv)
                    ; Lvar buf1_18481.(gv)
                    ; Lvar buf2_18482.(gv)
                    ; Lvar buf3_18483.(gv) ] __addstate_m_avx2x4 [:: Pvar st_18478
                                                                   ; Pvar AT_18479
                                                                   ; Pvar buf0_18480
                                                                   ; Pvar buf1_18481
                                                                   ; Pvar buf2_18482
                                                                   ; Pvar buf3_18483
                                                                   ; Papp2 (Osub (Op_int)) (Pvar _RATE8_18486) (Pvar AT_18479)
                                                                   ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_18484.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_18484) (Papp2 (Osub (Op_int)) (Pvar _RATE8_18486) (Pvar AT_18479)))
          ; cassgn (Lvar AT_18479.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_18478.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_18478 ]
          ; cassgn (Lvar ITERS_18487.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18484) (Pvar _RATE8_18486))
          ; cassgn (Lvar i_18488.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_18488) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_18487)))
              [:: ccall [:: Lvar st_18478.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar buf0_18480.(gv)
                          ; Lvar buf1_18481.(gv)
                          ; Lvar buf2_18482.(gv)
                          ; Lvar buf3_18483.(gv) ] __addstate_m_avx2x4 [:: Pvar st_18478
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_18480
                                                                    ; Pvar buf1_18481
                                                                    ; Pvar buf2_18482
                                                                    ; Pvar buf3_18483
                                                                    ; Pvar _RATE8_18486
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_18478.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_18478 ]
                ; cassgn (Lvar i_18488.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_18488) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_18484.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18484) (Pvar _RATE8_18486)) ]
        [::]
    ; ccall [:: Lvar st_18478.(gv)
              ; Lvar AT_18479.(gv)
              ; Lnone dummy_var_info (aword U64)
              ; Lnone dummy_var_info (aword U64)
              ; Lnone dummy_var_info (aword U64)
              ; Lnone dummy_var_info (aword U64) ] __addstate_m_avx2x4 [:: Pvar st_18478
                                                                    ; Pvar AT_18479
                                                                    ; Pvar buf0_18480
                                                                    ; Pvar buf1_18481
                                                                    ; Pvar buf2_18482
                                                                    ; Pvar buf3_18483
                                                                    ; Pvar _LEN_18484
                                                                    ; Pvar _TRAILB_18485 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_18485) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_18478.(gv) ] __addratebit_avx2x4 [:: Pvar st_18478
                                                                 ; Pvar _RATE8_18486 ] ]
        [::] ].

Definition fd___absorb_m_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___absorb_m_avx2x4;
    f_params := args___absorb_m_avx2x4;
    f_body := body___absorb_m_avx2x4;
    f_tyout := tyout___absorb_m_avx2x4;
    f_res := res___absorb_m_avx2x4;
    f_extra := tt;
  |}.

End IDO.
