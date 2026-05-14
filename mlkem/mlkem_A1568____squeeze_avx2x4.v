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

(* A1568____squeeze_avx2x4 *)
(* Local variables *)
Definition st_15514 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 15514).
Definition buf0_15515 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15515).
Definition buf1_15516 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15516).
Definition buf2_15517 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15517).
Definition buf3_15518 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15518).
Definition _RATE8_15519 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15519).
Definition offset_15520 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15520).
Definition _LEN_15521 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15521).
Definition ITERS_15522 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15522).
Definition LO_15523 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15523).
Definition i_15524 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15524).

(* Signature *)
Definition tyin_A1568____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aarr U8 1568
    ; aarr U8 1568
    ; aarr U8 1568
    ; aarr U8 1568
    ; aint ].
Definition args_A1568____squeeze_avx2x4 : seq var_i :=
  [:: st_15514.(gv)
    ; buf0_15515.(gv)
    ; buf1_15516.(gv)
    ; buf2_15517.(gv)
    ; buf3_15518.(gv)
    ; _RATE8_15519.(gv) ].
Definition tyout_A1568____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 1568; aarr U8 1568; aarr U8 1568; aarr U8 1568 ].
Definition res_A1568____squeeze_avx2x4 : seq var_i :=
  [:: st_15514.(gv)
    ; buf0_15515.(gv)
    ; buf1_15516.(gv)
    ; buf2_15517.(gv)
    ; buf3_15518.(gv) ].

(* Body *)
Definition body_A1568____squeeze_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_15520.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15521.(gv)) AT_none (aint) (Pconst (1568)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_15522.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15521) (Pvar _RATE8_15519)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_15523.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15521) (Pvar _RATE8_15519)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_15522))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_15524.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15524) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_15522)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_15514.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_15514 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_15515.(gv)
                                                                  ; Lvar buf1_15516.(gv)
                                                                  ; Lvar buf2_15517.(gv)
                                                                  ; Lvar buf3_15518.(gv)
                                                                  ; Lvar offset_15520.(gv) ] A1568____dumpstate_avx2x4 [:: Pvar buf0_15515
                                                                    ; Pvar buf1_15516
                                                                    ; Pvar buf2_15517
                                                                    ; Pvar buf3_15518
                                                                    ; Pvar offset_15520
                                                                    ; Pvar _RATE8_15519
                                                                    ; Pvar st_15514 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_15524.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15524) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_15523))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_15514.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_15514 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_15515.(gv)
                                                                ; Lvar buf1_15516.(gv)
                                                                ; Lvar buf2_15517.(gv)
                                                                ; Lvar buf3_15518.(gv)
                                                                ; Lvar offset_15520.(gv) ] A1568____dumpstate_avx2x4 [:: Pvar buf0_15515
                                                                    ; Pvar buf1_15516
                                                                    ; Pvar buf2_15517
                                                                    ; Pvar buf3_15518
                                                                    ; Pvar offset_15520
                                                                    ; Pvar LO_15523
                                                                    ; Pvar st_15514 ]) ]
                              [::]) ].

Definition fd_A1568____squeeze_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____squeeze_avx2x4;
    f_params := args_A1568____squeeze_avx2x4;
    f_body := body_A1568____squeeze_avx2x4;
    f_tyout := tyout_A1568____squeeze_avx2x4;
    f_res := res_A1568____squeeze_avx2x4;
    f_extra := tt;
  |}.

End IDO.
