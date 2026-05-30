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

(* A32____squeeze_avx2 *)
(* Local variables *)
Definition st_39 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 17424).
Definition buf_53 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17425).
Definition _RATE8_15 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17426).
Definition offset_43 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17427).
Definition _LEN_32 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17428).
Definition ITERS_15 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17429).
Definition LO_5 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17430).
Definition i_24 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17431).

(* Signature *)
Definition tyin_A32____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 32; aint ].
Definition args_A32____squeeze_avx2 : seq var_i :=
  [:: st_39.(gv); buf_53.(gv); _RATE8_15.(gv) ].
Definition tyout_A32____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 32 ].
Definition res_A32____squeeze_avx2 : seq var_i :=
  [:: st_39.(gv); buf_53.(gv) ].

(* Body *)
Definition body_A32____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_43.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_32.(gv)) AT_none (aint) (Pconst (32)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_15.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_32) (Pvar _RATE8_15)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_5.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_32) (Pvar _RATE8_15)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_24.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_24) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_15)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_39.(gv) ] _keccakf1600_avx2 [:: Pvar st_39 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_53.(gv)
                                                                ; Lvar offset_43.(gv) ] A32____dumpstate_avx2 [:: Pvar buf_53
                                                                    ; Pvar offset_43
                                                                    ; Pvar _RATE8_15
                                                                    ; Pvar st_39 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_24.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_24) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_5))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_39.(gv) ] _keccakf1600_avx2 [:: Pvar st_39 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_53.(gv)
                                                                ; Lvar offset_43.(gv) ] A32____dumpstate_avx2 [:: Pvar buf_53
                                                                    ; Pvar offset_43
                                                                    ; Pvar LO_5
                                                                    ; Pvar st_39 ]) ]
                              [::]) ].

Definition fd_A32____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____squeeze_avx2;
    f_params := args_A32____squeeze_avx2;
    f_body := body_A32____squeeze_avx2;
    f_tyout := tyout_A32____squeeze_avx2;
    f_res := res_A32____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
