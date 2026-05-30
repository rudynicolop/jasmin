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

(* A2____squeeze_avx2 *)
(* Local variables *)
Definition st_29 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 17806).
Definition buf_39 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17807).
Definition _RATE8_10 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17808).
Definition offset_26 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17809).
Definition _LEN_22 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17810).
Definition ITERS_10 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17811).
Definition LO_3 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17812).
Definition i_18 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17813).

(* Signature *)
Definition tyin_A2____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 2; aint ].
Definition args_A2____squeeze_avx2 : seq var_i :=
  [:: st_29.(gv); buf_39.(gv); _RATE8_10.(gv) ].
Definition tyout_A2____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 2 ].
Definition res_A2____squeeze_avx2 : seq var_i :=
  [:: st_29.(gv); buf_39.(gv) ].

(* Body *)
Definition body_A2____squeeze_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_26.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_22.(gv)) AT_none (aint) (Pconst (2)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar ITERS_10.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_22) (Pvar _RATE8_10)))
    ; MkI dummy_instr_info (Cassgn (Lvar LO_3.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_22) (Pvar _RATE8_10)))
    ; MkI dummy_instr_info (Cassgn (Lvar i_18.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_10)))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_29.(gv) ] _keccakf1600_avx2 [:: Pvar st_29 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_39.(gv)
                                                                ; Lvar offset_26.(gv) ] A2____dumpstate_avx2 [:: Pvar buf_39
                                                                    ; Pvar offset_26
                                                                    ; Pvar _RATE8_10
                                                                    ; Pvar st_29 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar i_18.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_3))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_29.(gv) ] _keccakf1600_avx2 [:: Pvar st_29 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf_39.(gv)
                                                                ; Lvar offset_26.(gv) ] A2____dumpstate_avx2 [:: Pvar buf_39
                                                                    ; Pvar offset_26
                                                                    ; Pvar LO_3
                                                                    ; Pvar st_29 ]) ]
                              [::]) ].

Definition fd_A2____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____squeeze_avx2;
    f_params := args_A2____squeeze_avx2;
    f_body := body_A2____squeeze_avx2;
    f_tyout := tyout_A2____squeeze_avx2;
    f_res := res_A2____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
