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
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_16416.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_16417.(gv)) AT_none (aint) (Pconst (128)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_16418.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16417) (Pvar _RATE8_16415)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_16419.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16417) (Pvar _RATE8_16415)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_16420.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16420) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_16418)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_16413.(gv) ] _keccakf1600_avx2 [:: Pvar st_16413 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_16414.(gv)
                                                                ; Lvar offset_16416.(gv) ] A128____dumpstate_avx2 [:: Pvar buf_16414
                                                                    ; Pvar offset_16416
                                                                    ; Pvar _RATE8_16415
                                                                    ; Pvar st_16413 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_16420.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16420) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_16419))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_16413.(gv) ] _keccakf1600_avx2 [:: Pvar st_16413 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_16414.(gv)
                                                                ; Lvar offset_16416.(gv) ] A128____dumpstate_avx2 [:: Pvar buf_16414
                                                                    ; Pvar offset_16416
                                                                    ; Pvar LO_16419
                                                                    ; Pvar st_16413 ]) ]
                              [::]) ].

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
