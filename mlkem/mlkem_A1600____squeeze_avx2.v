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

(* A1600____squeeze_avx2 *)
(* Local variables *)
Definition st_103 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14885).
Definition buf_149 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14886).
Definition _RATE8_47 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14887).
Definition offset_156 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14888).
Definition _LEN_96 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14889).
Definition ITERS_47 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14890).
Definition LO_18 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14891).
Definition i_62 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14892).

(* Signature *)
Definition tyin_A1600____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1600; aint ].
Definition args_A1600____squeeze_avx2 : seq var_i :=
  [:: st_103.(gv); buf_149.(gv); _RATE8_47.(gv) ].
Definition tyout_A1600____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1600 ].
Definition res_A1600____squeeze_avx2 : seq var_i :=
  [:: st_103.(gv); buf_149.(gv) ].

(* Body *)
Definition body_A1600____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_156.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_96.(gv)) AT_none (aint) (Pconst (1600)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_47.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_96) (Pvar _RATE8_47)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_18.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_96) (Pvar _RATE8_47)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_62.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_62) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_47)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_103.(gv) ] _keccakf1600_avx2 [:: Pvar st_103 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_149.(gv)
                                                                ; Lvar offset_156.(gv) ] A1600____dumpstate_avx2 [:: Pvar buf_149
                                                                    ; Pvar offset_156
                                                                    ; Pvar _RATE8_47
                                                                    ; Pvar st_103 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_62.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_62) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_18))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_103.(gv) ] _keccakf1600_avx2 [:: Pvar st_103 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_149.(gv)
                                                                ; Lvar offset_156.(gv) ] A1600____dumpstate_avx2 [:: Pvar buf_149
                                                                    ; Pvar offset_156
                                                                    ; Pvar LO_18
                                                                    ; Pvar st_103 ]) ]
                              [::]) ].

Definition fd_A1600____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____squeeze_avx2;
    f_params := args_A1600____squeeze_avx2;
    f_body := body_A1600____squeeze_avx2;
    f_tyout := tyout_A1600____squeeze_avx2;
    f_res := res_A1600____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
