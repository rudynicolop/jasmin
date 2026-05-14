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

(* A64____squeeze_avx2 *)
(* Local variables *)
Definition st_16660 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 16660).
Definition buf_16661 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 16661).
Definition _RATE8_16662 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16662).
Definition offset_16663 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16663).
Definition _LEN_16664 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16664).
Definition ITERS_16665 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16665).
Definition LO_16666 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16666).
Definition i_16667 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16667).

(* Signature *)
Definition tyin_A64____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 64; aint ].
Definition args_A64____squeeze_avx2 : seq var_i :=
  [:: st_16660.(gv); buf_16661.(gv); _RATE8_16662.(gv) ].
Definition tyout_A64____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 64 ].
Definition res_A64____squeeze_avx2 : seq var_i :=
  [:: st_16660.(gv); buf_16661.(gv) ].

(* Body *)
Definition body_A64____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_16663.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_16664.(gv)) AT_none (aint) (Pconst (64)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_16665.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16664) (Pvar _RATE8_16662)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_16666.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16664) (Pvar _RATE8_16662)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_16667.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16667) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_16665)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_16660.(gv) ] _keccakf1600_avx2 [:: Pvar st_16660 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_16661.(gv)
                                                                ; Lvar offset_16663.(gv) ] A64____dumpstate_avx2 [:: Pvar buf_16661
                                                                    ; Pvar offset_16663
                                                                    ; Pvar _RATE8_16662
                                                                    ; Pvar st_16660 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_16667.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16667) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_16666))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_16660.(gv) ] _keccakf1600_avx2 [:: Pvar st_16660 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_16661.(gv)
                                                                ; Lvar offset_16663.(gv) ] A64____dumpstate_avx2 [:: Pvar buf_16661
                                                                    ; Pvar offset_16663
                                                                    ; Pvar LO_16666
                                                                    ; Pvar st_16660 ]) ]
                              [::]) ].

Definition fd_A64____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____squeeze_avx2;
    f_params := args_A64____squeeze_avx2;
    f_body := body_A64____squeeze_avx2;
    f_tyout := tyout_A64____squeeze_avx2;
    f_res := res_A64____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
