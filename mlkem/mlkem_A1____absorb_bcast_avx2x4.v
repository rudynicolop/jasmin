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

(* A1____absorb_bcast_avx2x4 *)
(* Local variables *)
Definition st_21 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18153).
Definition AT_16 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18154).
Definition buf_27 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18155).
Definition _TRAILB_8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18156).
Definition _RATE8_6 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18157).
Definition offset_11 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18158).
Definition _LEN_14 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18159).
Definition ITERS_6 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18160).
Definition i_13 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18161).

(* Signature *)
Definition tyin_A1____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 1; aint; aint ].
Definition args_A1____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_21.(gv); AT_16.(gv); buf_27.(gv); _TRAILB_8.(gv); _RATE8_6.(gv) ].
Definition tyout_A1____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A1____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_21.(gv); AT_16.(gv) ].

(* Body *)
Definition body_A1____absorb_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_11.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14.(gv)) AT_none (aint) (Pconst (1)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_16) (Pvar _LEN_14)) (Pvar _RATE8_6))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_21.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_11.(gv) ] A1____addstate_bcast_avx2x4 [:: Pvar st_21
                                                                    ; Pvar AT_16
                                                                    ; Pvar buf_27
                                                                    ; Pvar offset_11
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_6) (Pvar AT_16)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_14) (Papp2 (Osub (Op_int)) (Pvar _RATE8_6) (Pvar AT_16))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_16.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_21.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_21 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_6.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14) (Pvar _RATE8_6)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_13.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_13) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_6)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_21.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_11.(gv) ] A1____addstate_bcast_avx2x4 [:: Pvar st_21
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_27
                                                                    ; Pvar offset_11
                                                                    ; Pvar _RATE8_6
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_21.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_21 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_13.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_13) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14) (Pvar _RATE8_6))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_21.(gv)
                                    ; Lvar AT_16.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1____addstate_bcast_avx2x4 [:: Pvar st_21
                                                                    ; Pvar AT_16
                                                                    ; Pvar buf_27
                                                                    ; Pvar offset_11
                                                                    ; Pvar _LEN_14
                                                                    ; Pvar _TRAILB_8 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_8) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_21.(gv) ] __addratebit_avx2x4 [:: Pvar st_21
                                                                    ; Pvar _RATE8_6 ]) ]
                              [::]) ].

Definition fd_A1____absorb_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____absorb_bcast_avx2x4;
    f_params := args_A1____absorb_bcast_avx2x4;
    f_body := body_A1____absorb_bcast_avx2x4;
    f_tyout := tyout_A1____absorb_bcast_avx2x4;
    f_res := res_A1____absorb_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
