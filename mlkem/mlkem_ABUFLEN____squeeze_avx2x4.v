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
Definition st_119 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14368).
Definition buf0_42 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14369).
Definition buf1_42 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14370).
Definition buf2_42 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14371).
Definition buf3_42 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14372).
Definition _RATE8_55 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14373).
Definition offset_179 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14374).
Definition _LEN_112 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14375).
Definition ITERS_55 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14376).
Definition LO_21 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14377).
Definition i_72 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14378).

(* Signature *)
Definition tyin_ABUFLEN____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aarr U8 536
    ; aarr U8 536
    ; aarr U8 536
    ; aarr U8 536
    ; aint ].
Definition args_ABUFLEN____squeeze_avx2x4 : seq var_i :=
  [:: st_119.(gv)
    ; buf0_42.(gv)
    ; buf1_42.(gv)
    ; buf2_42.(gv)
    ; buf3_42.(gv)
    ; _RATE8_55.(gv) ].
Definition tyout_ABUFLEN____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 536; aarr U8 536; aarr U8 536; aarr U8 536 ].
Definition res_ABUFLEN____squeeze_avx2x4 : seq var_i :=
  [:: st_119.(gv); buf0_42.(gv); buf1_42.(gv); buf2_42.(gv); buf3_42.(gv) ].

(* Body *)
Definition body_ABUFLEN____squeeze_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_179.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_112.(gv)) AT_none (aint) (Pconst (536)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_55.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_112) (Pvar _RATE8_55)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_21.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_112) (Pvar _RATE8_55)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_55))
                              [:: MkI dummy_instr_info (Cassgn (Lvar i_72.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_72) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_55)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_119.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_119 ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf0_42.(gv)
                                                                  ; Lvar buf1_42.(gv)
                                                                  ; Lvar buf2_42.(gv)
                                                                  ; Lvar buf3_42.(gv)
                                                                  ; Lvar offset_179.(gv) ] ABUFLEN____dumpstate_avx2x4 [:: Pvar buf0_42
                                                                    ; Pvar buf1_42
                                                                    ; Pvar buf2_42
                                                                    ; Pvar buf3_42
                                                                    ; Pvar offset_179
                                                                    ; Pvar _RATE8_55
                                                                    ; Pvar st_119 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_72.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_72) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ]) ]
                              [::])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_21))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_119.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_119 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_42.(gv)
                                                                ; Lvar buf1_42.(gv)
                                                                ; Lvar buf2_42.(gv)
                                                                ; Lvar buf3_42.(gv)
                                                                ; Lvar offset_179.(gv) ] ABUFLEN____dumpstate_avx2x4 [:: Pvar buf0_42
                                                                    ; Pvar buf1_42
                                                                    ; Pvar buf2_42
                                                                    ; Pvar buf3_42
                                                                    ; Pvar offset_179
                                                                    ; Pvar LO_21
                                                                    ; Pvar st_119 ]) ]
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
