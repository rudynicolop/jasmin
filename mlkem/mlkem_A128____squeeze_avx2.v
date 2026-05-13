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

(* A128____squeeze_avx2 *)
(* Local variables *)
Definition st_16413 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 16413).
Definition buf_16414 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16414).
Definition _RATE8_16415 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16415).
Definition offset_16416 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16416).
Definition _LEN_16417 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16417).
Definition ITERS_16418 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16418).
Definition LO_16419 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16419).
Definition i_16420 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16420).

(* Signature *)
Definition tyin_A128____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 128; aint ].
Definition args_A128____squeeze_avx2 : seq var_i :=
  [:: st_16413.(gv); buf_16414.(gv); _RATE8_16415.(gv) ].
Definition tyout_A128____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 128 ].
Definition res_A128____squeeze_avx2 : seq var_i :=
  [:: st_16413.(gv); buf_16414.(gv) ].

(* Body *)
Definition body_A128____squeeze_avx2 : cmd :=
  [:: cassgn (Lvar offset_16416.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_16417.(gv)) (aint) (Pconst (128)%Z)
    ; cassgn (Lvar ITERS_16418.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16417) (Pvar _RATE8_16415))
    ; cassgn (Lvar LO_16419.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16417) (Pvar _RATE8_16415))
    ; cassgn (Lvar i_16420.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16420) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_16418)))
        [:: ccall [:: Lvar st_16413.(gv) ] _keccakf1600_avx2 [:: Pvar st_16413 ]
          ; ccall [:: Lvar buf_16414.(gv); Lvar offset_16416.(gv) ] A128____dumpstate_avx2 [:: Pvar buf_16414
                                                                    ; Pvar offset_16416
                                                                    ; Pvar _RATE8_16415
                                                                    ; Pvar st_16413 ]
          ; cassgn (Lvar i_16420.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16420) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_16419))
        [:: ccall [:: Lvar st_16413.(gv) ] _keccakf1600_avx2 [:: Pvar st_16413 ]
          ; ccall [:: Lvar buf_16414.(gv); Lvar offset_16416.(gv) ] A128____dumpstate_avx2 [:: Pvar buf_16414
                                                                    ; Pvar offset_16416
                                                                    ; Pvar LO_16419
                                                                    ; Pvar st_16413 ] ]
        [::] ].

Definition fd_A128____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____squeeze_avx2;
    f_params := args_A128____squeeze_avx2;
    f_body := body_A128____squeeze_avx2;
    f_tyout := tyout_A128____squeeze_avx2;
    f_res := res_A128____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
