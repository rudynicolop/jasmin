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

(* A128____absorb_avx2 *)
(* Local variables *)
Definition st_16445 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 16445).
Definition AT_16446 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16446).
Definition buf_16447 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16447).
Definition _TRAILB_16448 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16448).
Definition _RATE8_16449 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16449).
Definition offset_16450 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16450).
Definition _LEN_16451 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16451).
Definition ITERS_16452 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16452).
Definition i_16453 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16453).

(* Signature *)
Definition tyin_A128____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 128; aint; aint ].
Definition args_A128____absorb_avx2 : seq var_i :=
  [:: st_16445.(gv)
    ; AT_16446.(gv)
    ; buf_16447.(gv)
    ; _TRAILB_16448.(gv)
    ; _RATE8_16449.(gv) ].
Definition tyout_A128____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A128____absorb_avx2 : seq var_i :=
  [:: st_16445.(gv); AT_16446.(gv) ].

(* Body *)
Definition body_A128____absorb_avx2 : cmd :=
  [:: cassgn (Lvar offset_16450.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_16451.(gv)) (aint) (Pconst (128)%Z)
    ; cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_16446) (Pvar _LEN_16451)) (Pvar _RATE8_16449))
        [:: ccall [:: Lvar st_16445.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar offset_16450.(gv) ] A128____addstate_avx2 [:: Pvar st_16445
                                                                    ; Pvar AT_16446
                                                                    ; Pvar buf_16447
                                                                    ; Pvar offset_16450
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_16449) (Pvar AT_16446)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_16451.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_16451) (Papp2 (Osub (Op_int)) (Pvar _RATE8_16449) (Pvar AT_16446)))
          ; cassgn (Lvar AT_16446.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_16445.(gv) ] _keccakf1600_avx2 [:: Pvar st_16445 ]
          ; cassgn (Lvar ITERS_16452.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16451) (Pvar _RATE8_16449))
          ; cassgn (Lvar i_16453.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16453) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_16452)))
              [:: ccall [:: Lvar st_16445.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar offset_16450.(gv) ] A128____addstate_avx2 [:: Pvar st_16445
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_16447
                                                                    ; Pvar offset_16450
                                                                    ; Pvar _RATE8_16449
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_16445.(gv) ] _keccakf1600_avx2 [:: Pvar st_16445 ]
                ; cassgn (Lvar i_16453.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16453) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_16451.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16451) (Pvar _RATE8_16449)) ]
        [::]
    ; ccall [:: Lvar st_16445.(gv)
              ; Lvar AT_16446.(gv)
              ; Lnone dummy_var_info (aword U64) ] A128____addstate_avx2 [:: Pvar st_16445
                                                                    ; Pvar AT_16446
                                                                    ; Pvar buf_16447
                                                                    ; Pvar offset_16450
                                                                    ; Pvar _LEN_16451
                                                                    ; Pvar _TRAILB_16448 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16448) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_16445.(gv) ] __addratebit_avx2 [:: Pvar st_16445
                                                               ; Pvar _RATE8_16449 ] ]
        [::] ].

Definition fd_A128____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____absorb_avx2;
    f_params := args_A128____absorb_avx2;
    f_body := body_A128____absorb_avx2;
    f_tyout := tyout_A128____absorb_avx2;
    f_res := res_A128____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
