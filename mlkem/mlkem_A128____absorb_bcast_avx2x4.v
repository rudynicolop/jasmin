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

(* A128____absorb_bcast_avx2x4 *)
(* Local variables *)
Definition st_16378 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 16378).
Definition AT_16379 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16379).
Definition buf_16380 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16380).
Definition _TRAILB_16381 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16381).
Definition _RATE8_16382 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16382).
Definition offset_16383 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16383).
Definition _LEN_16384 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16384).
Definition ITERS_16385 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16385).
Definition i_16386 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16386).

(* Signature *)
Definition tyin_A128____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 128; aint; aint ].
Definition args_A128____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_16378.(gv)
    ; AT_16379.(gv)
    ; buf_16380.(gv)
    ; _TRAILB_16381.(gv)
    ; _RATE8_16382.(gv) ].
Definition tyout_A128____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A128____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_16378.(gv); AT_16379.(gv) ].

(* Body *)
Definition body_A128____absorb_bcast_avx2x4 : cmd :=
  [:: cassgn (Lvar offset_16383.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_16384.(gv)) (aint) (Pconst (128)%Z)
    ; cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_16379) (Pvar _LEN_16384)) (Pvar _RATE8_16382))
        [:: ccall [:: Lvar st_16378.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar offset_16383.(gv) ] A128____addstate_bcast_avx2x4 [:: Pvar st_16378
                                                                    ; Pvar AT_16379
                                                                    ; Pvar buf_16380
                                                                    ; Pvar offset_16383
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_16382) (Pvar AT_16379)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_16384.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_16384) (Papp2 (Osub (Op_int)) (Pvar _RATE8_16382) (Pvar AT_16379)))
          ; cassgn (Lvar AT_16379.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_16378.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_16378 ]
          ; cassgn (Lvar ITERS_16385.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16384) (Pvar _RATE8_16382))
          ; cassgn (Lvar i_16386.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16386) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_16385)))
              [:: ccall [:: Lvar st_16378.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar offset_16383.(gv) ] A128____addstate_bcast_avx2x4 [:: Pvar st_16378
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_16380
                                                                    ; Pvar offset_16383
                                                                    ; Pvar _RATE8_16382
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_16378.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_16378 ]
                ; cassgn (Lvar i_16386.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16386) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_16384.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16384) (Pvar _RATE8_16382)) ]
        [::]
    ; ccall [:: Lvar st_16378.(gv)
              ; Lvar AT_16379.(gv)
              ; Lnone dummy_var_info (aword U64) ] A128____addstate_bcast_avx2x4 [:: Pvar st_16378
                                                                    ; Pvar AT_16379
                                                                    ; Pvar buf_16380
                                                                    ; Pvar offset_16383
                                                                    ; Pvar _LEN_16384
                                                                    ; Pvar _TRAILB_16381 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16381) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_16378.(gv) ] __addratebit_avx2x4 [:: Pvar st_16378
                                                                 ; Pvar _RATE8_16382 ] ]
        [::] ].

Definition fd_A128____absorb_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____absorb_bcast_avx2x4;
    f_params := args_A128____absorb_bcast_avx2x4;
    f_body := body_A128____absorb_bcast_avx2x4;
    f_tyout := tyout_A128____absorb_bcast_avx2x4;
    f_res := res_A128____absorb_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
