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

(* A1120____squeeze_avx2 *)
(* Local variables *)
Definition st_93 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 15267).
Definition buf_135 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15268).
Definition _RATE8_42 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15269).
Definition offset_139 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15270).
Definition _LEN_86 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15271).
Definition ITERS_42 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15272).
Definition LO_16 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15273).
Definition i_56 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15274).

(* Signature *)
Definition tyin_A1120____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1120; aint ].
Definition args_A1120____squeeze_avx2 : seq var_i :=
  [:: st_93.(gv); buf_135.(gv); _RATE8_42.(gv) ].
Definition tyout_A1120____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1120 ].
Definition res_A1120____squeeze_avx2 : seq var_i :=
  [:: st_93.(gv); buf_135.(gv) ].

(* Body *)
Definition body_A1120____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_139.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_86.(gv)) AT_none (aint) (Pconst (1120)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_42.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_86) (Pvar _RATE8_42)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_16.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_86) (Pvar _RATE8_42)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_56.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_56) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_42)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_93.(gv) ] _keccakf1600_avx2 [:: Pvar st_93 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_135.(gv)
                                                                ; Lvar offset_139.(gv) ] A1120____dumpstate_avx2 [:: Pvar buf_135
                                                                    ; Pvar offset_139
                                                                    ; Pvar _RATE8_42
                                                                    ; Pvar st_93 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_56.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_56) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_16))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_93.(gv) ] _keccakf1600_avx2 [:: Pvar st_93 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_135.(gv)
                                                                ; Lvar offset_139.(gv) ] A1120____dumpstate_avx2 [:: Pvar buf_135
                                                                    ; Pvar offset_139
                                                                    ; Pvar LO_16
                                                                    ; Pvar st_93 ]) ]
                              [::]) ].

Definition fd_A1120____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____squeeze_avx2;
    f_params := args_A1120____squeeze_avx2;
    f_body := body_A1120____squeeze_avx2;
    f_tyout := tyout_A1120____squeeze_avx2;
    f_res := res_A1120____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
