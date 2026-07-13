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

(* A1568____squeeze_avx2 *)
(* Local variables *)
Definition st_83 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 15649).
Definition buf_121 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15650).
Definition _RATE8_37 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15651).
Definition offset_122 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15652).
Definition _LEN_76 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15653).
Definition ITERS_37 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15654).
Definition LO_14 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15655).
Definition i_50 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15656).

(* Signature *)
Definition tyin_A1568____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1568; aint ].
Definition args_A1568____squeeze_avx2 : seq var_i :=
  [:: st_83.(gv); buf_121.(gv); _RATE8_37.(gv) ].
Definition tyout_A1568____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1568 ].
Definition res_A1568____squeeze_avx2 : seq var_i :=
  [:: st_83.(gv); buf_121.(gv) ].

(* Body *)
Definition body_A1568____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_122.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_76.(gv)) AT_none (aint) (Pconst (1568)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_37.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_76) (Pvar _RATE8_37)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_14.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_76) (Pvar _RATE8_37)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_50.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_50) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_37)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_83.(gv) ] _keccakf1600_avx2 [:: Pvar st_83 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_121.(gv)
                                                                ; Lvar offset_122.(gv) ] A1568____dumpstate_avx2 [:: Pvar buf_121
                                                                    ; Pvar offset_122
                                                                    ; Pvar _RATE8_37
                                                                    ; Pvar st_83 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_50.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_50) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_14))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_83.(gv) ] _keccakf1600_avx2 [:: Pvar st_83 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_121.(gv)
                                                                ; Lvar offset_122.(gv) ] A1568____dumpstate_avx2 [:: Pvar buf_121
                                                                    ; Pvar offset_122
                                                                    ; Pvar LO_14
                                                                    ; Pvar st_83 ]) ]
                              [::]) ].

Definition fd_A1568____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____squeeze_avx2;
    f_params := args_A1568____squeeze_avx2;
    f_body := body_A1568____squeeze_avx2;
    f_tyout := tyout_A1568____squeeze_avx2;
    f_res := res_A1568____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
