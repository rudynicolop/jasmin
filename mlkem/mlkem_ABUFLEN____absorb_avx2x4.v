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

(* ABUFLEN____absorb_avx2x4 *)
(* Local variables *)
Definition st_14418 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14418).
Definition AT_14419 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14419).
Definition buf0_14420 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14420).
Definition buf1_14421 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14421).
Definition buf2_14422 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14422).
Definition buf3_14423 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14423).
Definition _TRAILB_14424 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14424).
Definition _RATE8_14425 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14425).
Definition offset_14426 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14426).
Definition _LEN_14427 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14427).
Definition ITERS_14428 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14428).
Definition i_14429 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14429).

(* Signature *)
Definition tyin_ABUFLEN____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 536
    ; aarr U8 536
    ; aarr U8 536
    ; aarr U8 536
    ; aint
    ; aint ].
Definition args_ABUFLEN____absorb_avx2x4 : seq var_i :=
  [:: st_14418.(gv)
    ; AT_14419.(gv)
    ; buf0_14420.(gv)
    ; buf1_14421.(gv)
    ; buf2_14422.(gv)
    ; buf3_14423.(gv)
    ; _TRAILB_14424.(gv)
    ; _RATE8_14425.(gv) ].
Definition tyout_ABUFLEN____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_ABUFLEN____absorb_avx2x4 : seq var_i :=
  [:: st_14418.(gv); AT_14419.(gv) ].

(* Body *)
Definition body_ABUFLEN____absorb_avx2x4 : cmd :=
  [:: cassgn (Lvar offset_14426.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_14427.(gv)) (aint) (Pconst (536)%Z)
    ; cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_14419) (Pvar _LEN_14427)) (Pvar _RATE8_14425))
        [:: ccall [:: Lvar st_14418.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar offset_14426.(gv) ] ABUFLEN____addstate_avx2x4 [:: Pvar st_14418
                                                                    ; Pvar AT_14419
                                                                    ; Pvar buf0_14420
                                                                    ; Pvar buf1_14421
                                                                    ; Pvar buf2_14422
                                                                    ; Pvar buf3_14423
                                                                    ; Pvar offset_14426
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_14425) (Pvar AT_14419)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_14427.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_14427) (Papp2 (Osub (Op_int)) (Pvar _RATE8_14425) (Pvar AT_14419)))
          ; cassgn (Lvar AT_14419.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_14418.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_14418 ]
          ; cassgn (Lvar ITERS_14428.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14427) (Pvar _RATE8_14425))
          ; cassgn (Lvar i_14429.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_14429) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_14428)))
              [:: ccall [:: Lvar st_14418.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar offset_14426.(gv) ] ABUFLEN____addstate_avx2x4 [:: Pvar st_14418
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_14420
                                                                    ; Pvar buf1_14421
                                                                    ; Pvar buf2_14422
                                                                    ; Pvar buf3_14423
                                                                    ; Pvar offset_14426
                                                                    ; Pvar _RATE8_14425
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_14418.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_14418 ]
                ; cassgn (Lvar i_14429.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_14429) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_14427.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14427) (Pvar _RATE8_14425)) ]
        [::]
    ; ccall [:: Lvar st_14418.(gv)
              ; Lvar AT_14419.(gv)
              ; Lnone dummy_var_info (aword U64) ] ABUFLEN____addstate_avx2x4 [:: Pvar st_14418
                                                                    ; Pvar AT_14419
                                                                    ; Pvar buf0_14420
                                                                    ; Pvar buf1_14421
                                                                    ; Pvar buf2_14422
                                                                    ; Pvar buf3_14423
                                                                    ; Pvar offset_14426
                                                                    ; Pvar _LEN_14427
                                                                    ; Pvar _TRAILB_14424 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_14424) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_14418.(gv) ] __addratebit_avx2x4 [:: Pvar st_14418
                                                                 ; Pvar _RATE8_14425 ] ]
        [::] ].

Definition fd_ABUFLEN____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____absorb_avx2x4;
    f_params := args_ABUFLEN____absorb_avx2x4;
    f_body := body_ABUFLEN____absorb_avx2x4;
    f_tyout := tyout_ABUFLEN____absorb_avx2x4;
    f_res := res_ABUFLEN____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
