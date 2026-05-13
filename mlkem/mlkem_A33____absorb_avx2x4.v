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

(* A33____absorb_avx2x4 *)
(* Local variables *)
Definition st_16957 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 16957).
Definition AT_16958 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16958).
Definition buf0_16959 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16959).
Definition buf1_16960 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16960).
Definition buf2_16961 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16961).
Definition buf3_16962 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16962).
Definition _TRAILB_16963 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16963).
Definition _RATE8_16964 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16964).
Definition offset_16965 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16965).
Definition _LEN_16966 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16966).
Definition ITERS_16967 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16967).
Definition i_16968 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16968).

(* Signature *)
Definition tyin_A33____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 33
    ; aarr U8 33
    ; aarr U8 33
    ; aarr U8 33
    ; aint
    ; aint ].
Definition args_A33____absorb_avx2x4 : seq var_i :=
  [:: st_16957.(gv)
    ; AT_16958.(gv)
    ; buf0_16959.(gv)
    ; buf1_16960.(gv)
    ; buf2_16961.(gv)
    ; buf3_16962.(gv)
    ; _TRAILB_16963.(gv)
    ; _RATE8_16964.(gv) ].
Definition tyout_A33____absorb_avx2x4 : seq atype := [:: aarr U256 25; aint ].
Definition res_A33____absorb_avx2x4 : seq var_i :=
  [:: st_16957.(gv); AT_16958.(gv) ].

(* Body *)
Definition body_A33____absorb_avx2x4 : cmd :=
  [:: cassgn (Lvar offset_16965.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_16966.(gv)) (aint) (Pconst (33)%Z)
    ; cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_16958) (Pvar _LEN_16966)) (Pvar _RATE8_16964))
        [:: ccall [:: Lvar st_16957.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar offset_16965.(gv) ] A33____addstate_avx2x4 [:: Pvar st_16957
                                                                    ; Pvar AT_16958
                                                                    ; Pvar buf0_16959
                                                                    ; Pvar buf1_16960
                                                                    ; Pvar buf2_16961
                                                                    ; Pvar buf3_16962
                                                                    ; Pvar offset_16965
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_16964) (Pvar AT_16958)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_16966.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_16966) (Papp2 (Osub (Op_int)) (Pvar _RATE8_16964) (Pvar AT_16958)))
          ; cassgn (Lvar AT_16958.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_16957.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_16957 ]
          ; cassgn (Lvar ITERS_16967.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16966) (Pvar _RATE8_16964))
          ; cassgn (Lvar i_16968.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16968) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_16967)))
              [:: ccall [:: Lvar st_16957.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar offset_16965.(gv) ] A33____addstate_avx2x4 [:: Pvar st_16957
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_16959
                                                                    ; Pvar buf1_16960
                                                                    ; Pvar buf2_16961
                                                                    ; Pvar buf3_16962
                                                                    ; Pvar offset_16965
                                                                    ; Pvar _RATE8_16964
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_16957.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_16957 ]
                ; cassgn (Lvar i_16968.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16968) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_16966.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16966) (Pvar _RATE8_16964)) ]
        [::]
    ; ccall [:: Lvar st_16957.(gv)
              ; Lvar AT_16958.(gv)
              ; Lnone dummy_var_info (aword U64) ] A33____addstate_avx2x4 [:: Pvar st_16957
                                                                    ; Pvar AT_16958
                                                                    ; Pvar buf0_16959
                                                                    ; Pvar buf1_16960
                                                                    ; Pvar buf2_16961
                                                                    ; Pvar buf3_16962
                                                                    ; Pvar offset_16965
                                                                    ; Pvar _LEN_16966
                                                                    ; Pvar _TRAILB_16963 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16963) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_16957.(gv) ] __addratebit_avx2x4 [:: Pvar st_16957
                                                                 ; Pvar _RATE8_16964 ] ]
        [::] ].

Definition fd_A33____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____absorb_avx2x4;
    f_params := args_A33____absorb_avx2x4;
    f_body := body_A33____absorb_avx2x4;
    f_tyout := tyout_A33____absorb_avx2x4;
    f_res := res_A33____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
