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

(* A1600____absorb_avx2 *)
(* Local variables *)
Definition st_14917 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 14917).
Definition AT_14918 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14918).
Definition buf_14919 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14919).
Definition _TRAILB_14920 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14920).
Definition _RATE8_14921 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14921).
Definition offset_14922 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14922).
Definition _LEN_14923 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14923).
Definition ITERS_14924 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14924).
Definition i_14925 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14925).

(* Signature *)
Definition tyin_A1600____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1600; aint; aint ].
Definition args_A1600____absorb_avx2 : seq var_i :=
  [:: st_14917.(gv)
    ; AT_14918.(gv)
    ; buf_14919.(gv)
    ; _TRAILB_14920.(gv)
    ; _RATE8_14921.(gv) ].
Definition tyout_A1600____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A1600____absorb_avx2 : seq var_i :=
  [:: st_14917.(gv); AT_14918.(gv) ].

(* Body *)
Definition body_A1600____absorb_avx2 : cmd :=
  [:: cassgn (Lvar offset_14922.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_14923.(gv)) (aint) (Pconst (1600)%Z)
    ; cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_14918) (Pvar _LEN_14923)) (Pvar _RATE8_14921))
        [:: ccall [:: Lvar st_14917.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar offset_14922.(gv) ] A1600____addstate_avx2 [:: Pvar st_14917
                                                                    ; Pvar AT_14918
                                                                    ; Pvar buf_14919
                                                                    ; Pvar offset_14922
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_14921) (Pvar AT_14918)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_14923.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_14923) (Papp2 (Osub (Op_int)) (Pvar _RATE8_14921) (Pvar AT_14918)))
          ; cassgn (Lvar AT_14918.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_14917.(gv) ] _keccakf1600_avx2 [:: Pvar st_14917 ]
          ; cassgn (Lvar ITERS_14924.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14923) (Pvar _RATE8_14921))
          ; cassgn (Lvar i_14925.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_14925) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_14924)))
              [:: ccall [:: Lvar st_14917.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar offset_14922.(gv) ] A1600____addstate_avx2 [:: Pvar st_14917
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_14919
                                                                    ; Pvar offset_14922
                                                                    ; Pvar _RATE8_14921
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_14917.(gv) ] _keccakf1600_avx2 [:: Pvar st_14917 ]
                ; cassgn (Lvar i_14925.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_14925) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_14923.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14923) (Pvar _RATE8_14921)) ]
        [::]
    ; ccall [:: Lvar st_14917.(gv)
              ; Lvar AT_14918.(gv)
              ; Lnone dummy_var_info (aword U64) ] A1600____addstate_avx2 [:: Pvar st_14917
                                                                    ; Pvar AT_14918
                                                                    ; Pvar buf_14919
                                                                    ; Pvar offset_14922
                                                                    ; Pvar _LEN_14923
                                                                    ; Pvar _TRAILB_14920 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_14920) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_14917.(gv) ] __addratebit_avx2 [:: Pvar st_14917
                                                               ; Pvar _RATE8_14921 ] ]
        [::] ].

Definition fd_A1600____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____absorb_avx2;
    f_params := args_A1600____absorb_avx2;
    f_body := body_A1600____absorb_avx2;
    f_tyout := tyout_A1600____absorb_avx2;
    f_res := res_A1600____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
