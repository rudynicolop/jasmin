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

(* ABUFLEN____squeeze_avx2x4 *)
(* Local variables *)
Definition st_14368 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14368).
Definition buf0_14369 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14369).
Definition buf1_14370 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14370).
Definition buf2_14371 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14371).
Definition buf3_14372 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14372).
Definition _RATE8_14373 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14373).
Definition offset_14374 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14374).
Definition _LEN_14375 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14375).
Definition ITERS_14376 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14376).
Definition LO_14377 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14377).
Definition i_14378 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14378).

(* Signature *)
Definition tyin_ABUFLEN____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aarr U8 536
    ; aarr U8 536
    ; aarr U8 536
    ; aarr U8 536
    ; aint ].
Definition args_ABUFLEN____squeeze_avx2x4 : seq var_i :=
  [:: st_14368.(gv)
    ; buf0_14369.(gv)
    ; buf1_14370.(gv)
    ; buf2_14371.(gv)
    ; buf3_14372.(gv)
    ; _RATE8_14373.(gv) ].
Definition tyout_ABUFLEN____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 536; aarr U8 536; aarr U8 536; aarr U8 536 ].
Definition res_ABUFLEN____squeeze_avx2x4 : seq var_i :=
  [:: st_14368.(gv)
    ; buf0_14369.(gv)
    ; buf1_14370.(gv)
    ; buf2_14371.(gv)
    ; buf3_14372.(gv) ].

(* Body *)
Definition body_ABUFLEN____squeeze_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_14374.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14375.(gv)) AT_none (aint) (Pconst (536)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_14376.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14375) (Pvar _RATE8_14373)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_14377.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14375) (Pvar _RATE8_14373)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_14376))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_14378.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_14378) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_14376)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_14368.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_14368 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_14369.(gv)
                                                                  ; Lvar buf1_14370.(gv)
                                                                  ; Lvar buf2_14371.(gv)
                                                                  ; Lvar buf3_14372.(gv)
                                                                  ; Lvar offset_14374.(gv) ] ABUFLEN____dumpstate_avx2x4 [:: Pvar buf0_14369
                                                                    ; Pvar buf1_14370
                                                                    ; Pvar buf2_14371
                                                                    ; Pvar buf3_14372
                                                                    ; Pvar offset_14374
                                                                    ; Pvar _RATE8_14373
                                                                    ; Pvar st_14368 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_14378.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_14378) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_14377))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_14368.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_14368 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_14369.(gv)
                                                                ; Lvar buf1_14370.(gv)
                                                                ; Lvar buf2_14371.(gv)
                                                                ; Lvar buf3_14372.(gv)
                                                                ; Lvar offset_14374.(gv) ] ABUFLEN____dumpstate_avx2x4 [:: Pvar buf0_14369
                                                                    ; Pvar buf1_14370
                                                                    ; Pvar buf2_14371
                                                                    ; Pvar buf3_14372
                                                                    ; Pvar offset_14374
                                                                    ; Pvar LO_14377
                                                                    ; Pvar st_14368 ]) ]
                              [::]) ].

Definition fd_ABUFLEN____squeeze_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____squeeze_avx2x4;
    f_params := args_ABUFLEN____squeeze_avx2x4;
    f_body := body_ABUFLEN____squeeze_avx2x4;
    f_tyout := tyout_ABUFLEN____squeeze_avx2x4;
    f_res := res_ABUFLEN____squeeze_avx2x4;
    f_extra := tt;
  |}.

End IDO.
