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

(* A1568____absorb_avx2x4 *)
(* Local variables *)
Definition st_15564 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 15564).
Definition AT_15565 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15565).
Definition buf0_15566 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15566).
Definition buf1_15567 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15567).
Definition buf2_15568 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15568).
Definition buf3_15569 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15569).
Definition _TRAILB_15570 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15570).
Definition _RATE8_15571 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15571).
Definition offset_15572 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15572).
Definition _LEN_15573 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15573).
Definition ITERS_15574 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15574).
Definition i_15575 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15575).

(* Signature *)
Definition tyin_A1568____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 1568
    ; aarr U8 1568
    ; aarr U8 1568
    ; aarr U8 1568
    ; aint
    ; aint ].
Definition args_A1568____absorb_avx2x4 : seq var_i :=
  [:: st_15564.(gv)
    ; AT_15565.(gv)
    ; buf0_15566.(gv)
    ; buf1_15567.(gv)
    ; buf2_15568.(gv)
    ; buf3_15569.(gv)
    ; _TRAILB_15570.(gv)
    ; _RATE8_15571.(gv) ].
Definition tyout_A1568____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A1568____absorb_avx2x4 : seq var_i :=
  [:: st_15564.(gv); AT_15565.(gv) ].

(* Body *)
Definition body_A1568____absorb_avx2x4 : cmd :=
  [:: cassgn (Lvar offset_15572.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_15573.(gv)) (aint) (Pconst (1568)%Z)
    ; cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_15565) (Pvar _LEN_15573)) (Pvar _RATE8_15571))
        [:: ccall [:: Lvar st_15564.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar offset_15572.(gv) ] A1568____addstate_avx2x4 [:: Pvar st_15564
                                                                    ; Pvar AT_15565
                                                                    ; Pvar buf0_15566
                                                                    ; Pvar buf1_15567
                                                                    ; Pvar buf2_15568
                                                                    ; Pvar buf3_15569
                                                                    ; Pvar offset_15572
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_15571) (Pvar AT_15565)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_15573.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_15573) (Papp2 (Osub (Op_int)) (Pvar _RATE8_15571) (Pvar AT_15565)))
          ; cassgn (Lvar AT_15565.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_15564.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_15564 ]
          ; cassgn (Lvar ITERS_15574.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15573) (Pvar _RATE8_15571))
          ; cassgn (Lvar i_15575.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15575) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_15574)))
              [:: ccall [:: Lvar st_15564.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar offset_15572.(gv) ] A1568____addstate_avx2x4 [:: Pvar st_15564
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_15566
                                                                    ; Pvar buf1_15567
                                                                    ; Pvar buf2_15568
                                                                    ; Pvar buf3_15569
                                                                    ; Pvar offset_15572
                                                                    ; Pvar _RATE8_15571
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_15564.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_15564 ]
                ; cassgn (Lvar i_15575.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15575) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_15573.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15573) (Pvar _RATE8_15571)) ]
        [::]
    ; ccall [:: Lvar st_15564.(gv)
              ; Lvar AT_15565.(gv)
              ; Lnone dummy_var_info (aword U64) ] A1568____addstate_avx2x4 [:: Pvar st_15564
                                                                    ; Pvar AT_15565
                                                                    ; Pvar buf0_15566
                                                                    ; Pvar buf1_15567
                                                                    ; Pvar buf2_15568
                                                                    ; Pvar buf3_15569
                                                                    ; Pvar offset_15572
                                                                    ; Pvar _LEN_15573
                                                                    ; Pvar _TRAILB_15570 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_15570) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_15564.(gv) ] __addratebit_avx2x4 [:: Pvar st_15564
                                                                 ; Pvar _RATE8_15571 ] ]
        [::] ].

Definition fd_A1568____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____absorb_avx2x4;
    f_params := args_A1568____absorb_avx2x4;
    f_body := body_A1568____absorb_avx2x4;
    f_tyout := tyout_A1568____absorb_avx2x4;
    f_res := res_A1568____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
