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

(* A1____squeeze_avx2 *)
(* Local variables *)
Definition st_19 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 18188).
Definition buf_25 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18189).
Definition _RATE8_5 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18190).
Definition offset_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18191).
Definition _LEN_12 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18192).
Definition ITERS_5 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18193).
Definition LO_1 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18194).
Definition i_12 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18195).

(* Signature *)
Definition tyin_A1____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1; aint ].
Definition args_A1____squeeze_avx2 : seq var_i :=
  [:: st_19.(gv); buf_25.(gv); _RATE8_5.(gv) ].
Definition tyout_A1____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1 ].
Definition res_A1____squeeze_avx2 : seq var_i :=
  [:: st_19.(gv); buf_25.(gv) ].

(* Body *)
Definition body_A1____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_9.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_12.(gv)) AT_none (aint) (Pconst (1)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_5.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_12) (Pvar _RATE8_5)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_1.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_12) (Pvar _RATE8_5)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_12.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_5)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_19.(gv) ] _keccakf1600_avx2 [:: Pvar st_19 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_25.(gv)
                                                                ; Lvar offset_9.(gv) ] A1____dumpstate_avx2 [:: Pvar buf_25
                                                                    ; Pvar offset_9
                                                                    ; Pvar _RATE8_5
                                                                    ; Pvar st_19 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_12.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_1))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_19.(gv) ] _keccakf1600_avx2 [:: Pvar st_19 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_25.(gv)
                                                                ; Lvar offset_9.(gv) ] A1____dumpstate_avx2 [:: Pvar buf_25
                                                                    ; Pvar offset_9
                                                                    ; Pvar LO_1
                                                                    ; Pvar st_19 ]) ]
                              [::]) ].

Definition fd_A1____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____squeeze_avx2;
    f_params := args_A1____squeeze_avx2;
    f_body := body_A1____squeeze_avx2;
    f_tyout := tyout_A1____squeeze_avx2;
    f_res := res_A1____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
