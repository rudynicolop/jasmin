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
Definition st_18188 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 18188).
Definition buf_18189 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18189).
Definition _RATE8_18190 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18190).
Definition offset_18191 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18191).
Definition _LEN_18192 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18192).
Definition ITERS_18193 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18193).
Definition LO_18194 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18194).
Definition i_18195 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18195).

(* Signature *)
Definition tyin_A1____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1; aint ].
Definition args_A1____squeeze_avx2 : seq var_i :=
  [:: st_18188.(gv); buf_18189.(gv); _RATE8_18190.(gv) ].
Definition tyout_A1____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1 ].
Definition res_A1____squeeze_avx2 : seq var_i :=
  [:: st_18188.(gv); buf_18189.(gv) ].

(* Body *)
Definition body_A1____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_18191.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_18192.(gv)) AT_none (aint) (Pconst (1)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_18193.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18192) (Pvar _RATE8_18190)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_18194.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18192) (Pvar _RATE8_18190)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_18195.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_18195) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_18193)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_18188.(gv) ] _keccakf1600_avx2 [:: Pvar st_18188 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_18189.(gv)
                                                                ; Lvar offset_18191.(gv) ] A1____dumpstate_avx2 [:: Pvar buf_18189
                                                                    ; Pvar offset_18191
                                                                    ; Pvar _RATE8_18190
                                                                    ; Pvar st_18188 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_18195.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_18195) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_18194))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_18188.(gv) ] _keccakf1600_avx2 [:: Pvar st_18188 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_18189.(gv)
                                                                ; Lvar offset_18191.(gv) ] A1____dumpstate_avx2 [:: Pvar buf_18189
                                                                    ; Pvar offset_18191
                                                                    ; Pvar LO_18194
                                                                    ; Pvar st_18188 ]) ]
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
