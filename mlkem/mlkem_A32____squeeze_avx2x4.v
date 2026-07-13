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

(* A32____squeeze_avx2x4 *)
(* Local variables *)
Definition st_45 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 17289).
Definition buf0_14 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17290).
Definition buf1_14 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17291).
Definition buf2_14 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17292).
Definition buf3_14 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17293).
Definition _RATE8_18 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17294).
Definition offset_49 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17295).
Definition _LEN_38 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17296).
Definition ITERS_18 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17297).
Definition LO_6 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17298).
Definition i_28 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17299).

(* Signature *)
Definition tyin_A32____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 32; aarr U8 32; aarr U8 32; aarr U8 32; aint ].
Definition args_A32____squeeze_avx2x4 : seq var_i :=
  [:: st_45.(gv)
    ; buf0_14.(gv)
    ; buf1_14.(gv)
    ; buf2_14.(gv)
    ; buf3_14.(gv)
    ; _RATE8_18.(gv) ].
Definition tyout_A32____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 32; aarr U8 32; aarr U8 32; aarr U8 32 ].
Definition res_A32____squeeze_avx2x4 : seq var_i :=
  [:: st_45.(gv); buf0_14.(gv); buf1_14.(gv); buf2_14.(gv); buf3_14.(gv) ].

(* Body *)
Definition body_A32____squeeze_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_49.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_38.(gv)) AT_none (aint) (Pconst (32)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_18.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_38) (Pvar _RATE8_18)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_6.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_38) (Pvar _RATE8_18)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_18))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_28.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_28) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_18)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_45.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_45 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_14.(gv)
                                                                  ; Lvar buf1_14.(gv)
                                                                  ; Lvar buf2_14.(gv)
                                                                  ; Lvar buf3_14.(gv)
                                                                  ; Lvar offset_49.(gv) ] A32____dumpstate_avx2x4 [:: Pvar buf0_14
                                                                    ; Pvar buf1_14
                                                                    ; Pvar buf2_14
                                                                    ; Pvar buf3_14
                                                                    ; Pvar offset_49
                                                                    ; Pvar _RATE8_18
                                                                    ; Pvar st_45 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_28.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_28) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_6))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_45.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_45 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_14.(gv)
                                                                ; Lvar buf1_14.(gv)
                                                                ; Lvar buf2_14.(gv)
                                                                ; Lvar buf3_14.(gv)
                                                                ; Lvar offset_49.(gv) ] A32____dumpstate_avx2x4 [:: Pvar buf0_14
                                                                    ; Pvar buf1_14
                                                                    ; Pvar buf2_14
                                                                    ; Pvar buf3_14
                                                                    ; Pvar offset_49
                                                                    ; Pvar LO_6
                                                                    ; Pvar st_45 ]) ]
                              [::]) ].

Definition fd_A32____squeeze_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____squeeze_avx2x4;
    f_params := args_A32____squeeze_avx2x4;
    f_body := body_A32____squeeze_avx2x4;
    f_tyout := tyout_A32____squeeze_avx2x4;
    f_res := res_A32____squeeze_avx2x4;
    f_extra := tt;
  |}.

End IDO.
