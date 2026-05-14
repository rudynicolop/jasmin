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
Definition st_15267 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 15267).
Definition buf_15268 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15268).
Definition _RATE8_15269 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15269).
Definition offset_15270 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15270).
Definition _LEN_15271 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15271).
Definition ITERS_15272 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15272).
Definition LO_15273 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15273).
Definition i_15274 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15274).

(* Signature *)
Definition tyin_A1120____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1120; aint ].
Definition args_A1120____squeeze_avx2 : seq var_i :=
  [:: st_15267.(gv); buf_15268.(gv); _RATE8_15269.(gv) ].
Definition tyout_A1120____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1120 ].
Definition res_A1120____squeeze_avx2 : seq var_i :=
  [:: st_15267.(gv); buf_15268.(gv) ].

(* Body *)
Definition body_A1120____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_15270.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15271.(gv)) AT_none (aint) (Pconst (1120)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_15272.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15271) (Pvar _RATE8_15269)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_15273.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15271) (Pvar _RATE8_15269)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_15274.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15274) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_15272)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_15267.(gv) ] _keccakf1600_avx2 [:: Pvar st_15267 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_15268.(gv)
                                                                ; Lvar offset_15270.(gv) ] A1120____dumpstate_avx2 [:: Pvar buf_15268
                                                                    ; Pvar offset_15270
                                                                    ; Pvar _RATE8_15269
                                                                    ; Pvar st_15267 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_15274.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15274) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_15273))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_15267.(gv) ] _keccakf1600_avx2 [:: Pvar st_15267 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_15268.(gv)
                                                                ; Lvar offset_15270.(gv) ] A1120____dumpstate_avx2 [:: Pvar buf_15268
                                                                    ; Pvar offset_15270
                                                                    ; Pvar LO_15273
                                                                    ; Pvar st_15267 ]) ]
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
