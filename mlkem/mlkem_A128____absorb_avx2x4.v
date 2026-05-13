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

(* A128____absorb_avx2x4 *)
(* Local variables *)
Definition st_16328 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 16328).
Definition AT_16329 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16329).
Definition buf0_16330 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16330).
Definition buf1_16331 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16331).
Definition buf2_16332 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16332).
Definition buf3_16333 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16333).
Definition _TRAILB_16334 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16334).
Definition _RATE8_16335 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16335).
Definition offset_16336 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16336).
Definition _LEN_16337 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16337).
Definition ITERS_16338 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16338).
Definition i_16339 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16339).

(* Signature *)
Definition tyin_A128____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 128
    ; aarr U8 128
    ; aarr U8 128
    ; aarr U8 128
    ; aint
    ; aint ].
Definition args_A128____absorb_avx2x4 : seq var_i :=
  [:: st_16328.(gv)
    ; AT_16329.(gv)
    ; buf0_16330.(gv)
    ; buf1_16331.(gv)
    ; buf2_16332.(gv)
    ; buf3_16333.(gv)
    ; _TRAILB_16334.(gv)
    ; _RATE8_16335.(gv) ].
Definition tyout_A128____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A128____absorb_avx2x4 : seq var_i :=
  [:: st_16328.(gv); AT_16329.(gv) ].

(* Body *)
Definition body_A128____absorb_avx2x4 : cmd :=
  [:: cassgn (Lvar offset_16336.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_16337.(gv)) (aint) (Pconst (128)%Z)
    ; cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_16329) (Pvar _LEN_16337)) (Pvar _RATE8_16335))
        [:: ccall [:: Lvar st_16328.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar offset_16336.(gv) ] A128____addstate_avx2x4 [:: Pvar st_16328
                                                                    ; Pvar AT_16329
                                                                    ; Pvar buf0_16330
                                                                    ; Pvar buf1_16331
                                                                    ; Pvar buf2_16332
                                                                    ; Pvar buf3_16333
                                                                    ; Pvar offset_16336
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_16335) (Pvar AT_16329)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_16337.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_16337) (Papp2 (Osub (Op_int)) (Pvar _RATE8_16335) (Pvar AT_16329)))
          ; cassgn (Lvar AT_16329.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_16328.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_16328 ]
          ; cassgn (Lvar ITERS_16338.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16337) (Pvar _RATE8_16335))
          ; cassgn (Lvar i_16339.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16339) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_16338)))
              [:: ccall [:: Lvar st_16328.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar offset_16336.(gv) ] A128____addstate_avx2x4 [:: Pvar st_16328
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_16330
                                                                    ; Pvar buf1_16331
                                                                    ; Pvar buf2_16332
                                                                    ; Pvar buf3_16333
                                                                    ; Pvar offset_16336
                                                                    ; Pvar _RATE8_16335
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_16328.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_16328 ]
                ; cassgn (Lvar i_16339.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16339) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_16337.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16337) (Pvar _RATE8_16335)) ]
        [::]
    ; ccall [:: Lvar st_16328.(gv)
              ; Lvar AT_16329.(gv)
              ; Lnone dummy_var_info (aword U64) ] A128____addstate_avx2x4 [:: Pvar st_16328
                                                                    ; Pvar AT_16329
                                                                    ; Pvar buf0_16330
                                                                    ; Pvar buf1_16331
                                                                    ; Pvar buf2_16332
                                                                    ; Pvar buf3_16333
                                                                    ; Pvar offset_16336
                                                                    ; Pvar _LEN_16337
                                                                    ; Pvar _TRAILB_16334 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16334) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_16328.(gv) ] __addratebit_avx2x4 [:: Pvar st_16328
                                                                 ; Pvar _RATE8_16335 ] ]
        [::] ].

Definition fd_A128____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____absorb_avx2x4;
    f_params := args_A128____absorb_avx2x4;
    f_body := body_A128____absorb_avx2x4;
    f_tyout := tyout_A128____absorb_avx2x4;
    f_res := res_A128____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
