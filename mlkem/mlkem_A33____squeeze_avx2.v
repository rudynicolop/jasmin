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
Definition st_17042 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 17042).
Definition buf_17043 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 17043).
Definition _RATE8_17044 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17044).
Definition offset_17045 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17045).
Definition _LEN_17046 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17046).
Definition ITERS_17047 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17047).
Definition LO_17048 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17048).
Definition i_17049 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17049).

(* Signature *)
Definition tyin_A33____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 33; aint ].
Definition args_A33____squeeze_avx2 : seq var_i :=
  [:: st_17042.(gv); buf_17043.(gv); _RATE8_17044.(gv) ].
Definition tyout_A33____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 33 ].
Definition res_A33____squeeze_avx2 : seq var_i :=
  [:: st_17042.(gv); buf_17043.(gv) ].

(* Body *)
Definition body_A33____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_17045.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_17046.(gv)) AT_none (aint) (Pconst (33)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_17047.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17046) (Pvar _RATE8_17044)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_17048.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17046) (Pvar _RATE8_17044)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_17049.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17049) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_17047)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_17042.(gv) ] _keccakf1600_avx2 [:: Pvar st_17042 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_17043.(gv)
                                                                ; Lvar offset_17045.(gv) ] A33____dumpstate_avx2 [:: Pvar buf_17043
                                                                    ; Pvar offset_17045
                                                                    ; Pvar _RATE8_17044
                                                                    ; Pvar st_17042 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_17049.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17049) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_17048))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_17042.(gv) ] _keccakf1600_avx2 [:: Pvar st_17042 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_17043.(gv)
                                                                ; Lvar offset_17045.(gv) ] A33____dumpstate_avx2 [:: Pvar buf_17043
                                                                    ; Pvar offset_17045
                                                                    ; Pvar LO_17048
                                                                    ; Pvar st_17042 ]) ]
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
