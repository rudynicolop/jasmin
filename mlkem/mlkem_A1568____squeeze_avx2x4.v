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
Definition st_89 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 15514).
Definition buf0_30 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15515).
Definition buf1_30 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15516).
Definition buf2_30 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15517).
Definition buf3_30 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15518).
Definition _RATE8_40 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15519).
Definition offset_128 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15520).
Definition _LEN_82 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15521).
Definition ITERS_40 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15522).
Definition LO_15 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15523).
Definition i_54 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15524).

(* Signature *)
Definition tyin_A1568____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aarr U8 1568
    ; aarr U8 1568
    ; aarr U8 1568
    ; aarr U8 1568
    ; aint ].
Definition args_A1568____squeeze_avx2x4 : seq var_i :=
  [:: st_89.(gv)
    ; buf0_30.(gv)
    ; buf1_30.(gv)
    ; buf2_30.(gv)
    ; buf3_30.(gv)
    ; _RATE8_40.(gv) ].
Definition tyout_A1568____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 1568; aarr U8 1568; aarr U8 1568; aarr U8 1568 ].
Definition res_A1568____squeeze_avx2x4 : seq var_i :=
  [:: st_89.(gv); buf0_30.(gv); buf1_30.(gv); buf2_30.(gv); buf3_30.(gv) ].

(* Body *)
Definition body_A1568____squeeze_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_128.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_82.(gv)) AT_none (aint) (Pconst (1568)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_40.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_82) (Pvar _RATE8_40)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_15.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_82) (Pvar _RATE8_40)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_40))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_54.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_54) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_40)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_89.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_89 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_30.(gv)
                                                                  ; Lvar buf1_30.(gv)
                                                                  ; Lvar buf2_30.(gv)
                                                                  ; Lvar buf3_30.(gv)
                                                                  ; Lvar offset_128.(gv) ] A1568____dumpstate_avx2x4 [:: Pvar buf0_30
                                                                    ; Pvar buf1_30
                                                                    ; Pvar buf2_30
                                                                    ; Pvar buf3_30
                                                                    ; Pvar offset_128
                                                                    ; Pvar _RATE8_40
                                                                    ; Pvar st_89 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_54.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_54) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_15))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_89.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_89 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_30.(gv)
                                                                ; Lvar buf1_30.(gv)
                                                                ; Lvar buf2_30.(gv)
                                                                ; Lvar buf3_30.(gv)
                                                                ; Lvar offset_128.(gv) ] A1568____dumpstate_avx2x4 [:: Pvar buf0_30
                                                                    ; Pvar buf1_30
                                                                    ; Pvar buf2_30
                                                                    ; Pvar buf3_30
                                                                    ; Pvar offset_128
                                                                    ; Pvar LO_15
                                                                    ; Pvar st_89 ]) ]
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
