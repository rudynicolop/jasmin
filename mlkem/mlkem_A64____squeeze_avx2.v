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
Definition st_59 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 16660).
Definition buf_81 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 16661).
Definition _RATE8_25 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16662).
Definition offset_77 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16663).
Definition _LEN_52 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16664).
Definition ITERS_25 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16665).
Definition LO_9 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16666).
Definition i_36 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16667).

(* Signature *)
Definition tyin_A64____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 64; aint ].
Definition args_A64____squeeze_avx2 : seq var_i :=
  [:: st_59.(gv); buf_81.(gv); _RATE8_25.(gv) ].
Definition tyout_A64____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 64 ].
Definition res_A64____squeeze_avx2 : seq var_i :=
  [:: st_59.(gv); buf_81.(gv) ].

(* Body *)
Definition body_A64____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_77.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_52.(gv)) AT_none (aint) (Pconst (64)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_25.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_52) (Pvar _RATE8_25)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_9.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_52) (Pvar _RATE8_25)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_36.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_36) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_25)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_59.(gv) ] _keccakf1600_avx2 [:: Pvar st_59 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_81.(gv)
                                                                ; Lvar offset_77.(gv) ] A64____dumpstate_avx2 [:: Pvar buf_81
                                                                    ; Pvar offset_77
                                                                    ; Pvar _RATE8_25
                                                                    ; Pvar st_59 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_36.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_36) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_9))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_59.(gv) ] _keccakf1600_avx2 [:: Pvar st_59 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_81.(gv)
                                                                ; Lvar offset_77.(gv) ] A64____dumpstate_avx2 [:: Pvar buf_81
                                                                    ; Pvar offset_77
                                                                    ; Pvar LO_9
                                                                    ; Pvar st_59 ]) ]
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
