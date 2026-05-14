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

(* ABUFLEN____squeeze_avx2 *)
(* Local variables *)
Definition st_14503 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 14503).
Definition buf_14504 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14504).
Definition _RATE8_14505 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14505).
Definition offset_14506 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14506).
Definition _LEN_14507 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14507).
Definition ITERS_14508 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14508).
Definition LO_14509 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14509).
Definition i_14510 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14510).

(* Signature *)
Definition tyin_ABUFLEN____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 536; aint ].
Definition args_ABUFLEN____squeeze_avx2 : seq var_i :=
  [:: st_14503.(gv); buf_14504.(gv); _RATE8_14505.(gv) ].
Definition tyout_ABUFLEN____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 536 ].
Definition res_ABUFLEN____squeeze_avx2 : seq var_i :=
  [:: st_14503.(gv); buf_14504.(gv) ].

(* Body *)
Definition body_ABUFLEN____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_14506.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14507.(gv)) AT_none (aint) (Pconst (536)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_14508.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14507) (Pvar _RATE8_14505)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_14509.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14507) (Pvar _RATE8_14505)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_14510.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_14510) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_14508)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_14503.(gv) ] _keccakf1600_avx2 [:: Pvar st_14503 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_14504.(gv)
                                                                ; Lvar offset_14506.(gv) ] ABUFLEN____dumpstate_avx2 [:: Pvar buf_14504
                                                                    ; Pvar offset_14506
                                                                    ; Pvar _RATE8_14505
                                                                    ; Pvar st_14503 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_14510.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_14510) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_14509))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_14503.(gv) ] _keccakf1600_avx2 [:: Pvar st_14503 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_14504.(gv)
                                                                ; Lvar offset_14506.(gv) ] ABUFLEN____dumpstate_avx2 [:: Pvar buf_14504
                                                                    ; Pvar offset_14506
                                                                    ; Pvar LO_14509
                                                                    ; Pvar st_14503 ]) ]
                              [::]) ].

Definition fd_ABUFLEN____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____squeeze_avx2;
    f_params := args_ABUFLEN____squeeze_avx2;
    f_body := body_ABUFLEN____squeeze_avx2;
    f_tyout := tyout_ABUFLEN____squeeze_avx2;
    f_res := res_ABUFLEN____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
