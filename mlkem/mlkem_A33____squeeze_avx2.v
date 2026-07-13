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

(* A33____squeeze_avx2 *)
(* Local variables *)
Definition st_49 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 17042).
Definition buf_67 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 17043).
Definition _RATE8_20 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17044).
Definition offset_60 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17045).
Definition _LEN_42 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17046).
Definition ITERS_20 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17047).
Definition LO_7 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17048).
Definition i_30 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17049).

(* Signature *)
Definition tyin_A33____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 33; aint ].
Definition args_A33____squeeze_avx2 : seq var_i :=
  [:: st_49.(gv); buf_67.(gv); _RATE8_20.(gv) ].
Definition tyout_A33____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 33 ].
Definition res_A33____squeeze_avx2 : seq var_i :=
  [:: st_49.(gv); buf_67.(gv) ].

(* Body *)
Definition body_A33____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_60.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_42.(gv)) AT_none (aint) (Pconst (33)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_20.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_42) (Pvar _RATE8_20)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_7.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_42) (Pvar _RATE8_20)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_30.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_30) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_20)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_49.(gv) ] _keccakf1600_avx2 [:: Pvar st_49 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_67.(gv)
                                                                ; Lvar offset_60.(gv) ] A33____dumpstate_avx2 [:: Pvar buf_67
                                                                    ; Pvar offset_60
                                                                    ; Pvar _RATE8_20
                                                                    ; Pvar st_49 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_30.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_30) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_7))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_49.(gv) ] _keccakf1600_avx2 [:: Pvar st_49 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_67.(gv)
                                                                ; Lvar offset_60.(gv) ] A33____dumpstate_avx2 [:: Pvar buf_67
                                                                    ; Pvar offset_60
                                                                    ; Pvar LO_7
                                                                    ; Pvar st_49 ]) ]
                              [::]) ].

Definition fd_A33____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____squeeze_avx2;
    f_params := args_A33____squeeze_avx2;
    f_body := body_A33____squeeze_avx2;
    f_tyout := tyout_A33____squeeze_avx2;
    f_res := res_A33____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
