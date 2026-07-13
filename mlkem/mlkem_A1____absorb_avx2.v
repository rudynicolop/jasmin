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

(* A1____absorb_avx2 *)
(* Local variables *)
Definition st_17 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 18220).
Definition AT_14 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18221).
Definition buf_23 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18222).
Definition _TRAILB_6 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18223).
Definition _RATE8_4 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18224).
Definition offset_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18225).
Definition _LEN_10 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18226).
Definition ITERS_4 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18227).
Definition i_11 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18228).

(* Signature *)
Definition tyin_A1____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1; aint; aint ].
Definition args_A1____absorb_avx2 : seq var_i :=
  [:: st_17.(gv); AT_14.(gv); buf_23.(gv); _TRAILB_6.(gv); _RATE8_4.(gv) ].
Definition tyout_A1____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A1____absorb_avx2 : seq var_i := [:: st_17.(gv); AT_14.(gv) ].

(* Body *)
Definition body_A1____absorb_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_7.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_10.(gv)) AT_none (aint) (Pconst (1)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_14) (Pvar _LEN_10)) (Pvar _RATE8_4))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_17.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_7.(gv) ] A1____addstate_avx2 [:: Pvar st_17
                                                                    ; Pvar AT_14
                                                                    ; Pvar buf_23
                                                                    ; Pvar offset_7
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_4) (Pvar AT_14)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_10.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_10) (Papp2 (Osub (Op_int)) (Pvar _RATE8_4) (Pvar AT_14))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_14.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_17.(gv) ] _keccakf1600_avx2 [:: Pvar st_17 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_4.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_10) (Pvar _RATE8_4)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_11.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_11) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_4)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_17.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_7.(gv) ] A1____addstate_avx2 [:: Pvar st_17
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_23
                                                                    ; Pvar offset_7
                                                                    ; Pvar _RATE8_4
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_17.(gv) ] _keccakf1600_avx2 [:: Pvar st_17 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_11.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_11) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_10.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_10) (Pvar _RATE8_4))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_17.(gv)
                                    ; Lvar AT_14.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1____addstate_avx2 [:: Pvar st_17
                                                                    ; Pvar AT_14
                                                                    ; Pvar buf_23
                                                                    ; Pvar offset_7
                                                                    ; Pvar _LEN_10
                                                                    ; Pvar _TRAILB_6 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_6) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_17.(gv) ] __addratebit_avx2 [:: Pvar st_17
                                                                    ; Pvar _RATE8_4 ]) ]
                              [::]) ].

Definition fd_A1____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____absorb_avx2;
    f_params := args_A1____absorb_avx2;
    f_body := body_A1____absorb_avx2;
    f_tyout := tyout_A1____absorb_avx2;
    f_res := res_A1____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
