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

(* A2____absorb_bcast_avx2x4 *)
(* Local variables *)
Definition st_31 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 17771).
Definition AT_26 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17772).
Definition buf_41 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17773).
Definition _TRAILB_14 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17774).
Definition _RATE8_11 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17775).
Definition offset_28 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17776).
Definition _LEN_24 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17777).
Definition ITERS_11 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17778).
Definition i_19 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17779).

(* Signature *)
Definition tyin_A2____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 2; aint; aint ].
Definition args_A2____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_31.(gv); AT_26.(gv); buf_41.(gv); _TRAILB_14.(gv); _RATE8_11.(gv) ].
Definition tyout_A2____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A2____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_31.(gv); AT_26.(gv) ].

(* Body *)
Definition body_A2____absorb_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_28.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_24.(gv)) AT_none (aint) (Pconst (2)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_26) (Pvar _LEN_24)) (Pvar _RATE8_11))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_31.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_28.(gv) ] A2____addstate_bcast_avx2x4 [:: Pvar st_31
                                                                    ; Pvar AT_26
                                                                    ; Pvar buf_41
                                                                    ; Pvar offset_28
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_11) (Pvar AT_26)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_24.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_24) (Papp2 (Osub (Op_int)) (Pvar _RATE8_11) (Pvar AT_26))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_26.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_31.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_31 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_11.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_24) (Pvar _RATE8_11)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_19.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_19) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_11)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_31.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_28.(gv) ] A2____addstate_bcast_avx2x4 [:: Pvar st_31
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_41
                                                                    ; Pvar offset_28
                                                                    ; Pvar _RATE8_11
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_31.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_31 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_19.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_19) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_24.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_24) (Pvar _RATE8_11))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_31.(gv)
                                    ; Lvar AT_26.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A2____addstate_bcast_avx2x4 [:: Pvar st_31
                                                                    ; Pvar AT_26
                                                                    ; Pvar buf_41
                                                                    ; Pvar offset_28
                                                                    ; Pvar _LEN_24
                                                                    ; Pvar _TRAILB_14 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_14) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_31.(gv) ] __addratebit_avx2x4 [:: Pvar st_31
                                                                    ; Pvar _RATE8_11 ]) ]
                              [::]) ].

Definition fd_A2____absorb_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____absorb_bcast_avx2x4;
    f_params := args_A2____absorb_bcast_avx2x4;
    f_body := body_A2____absorb_bcast_avx2x4;
    f_tyout := tyout_A2____absorb_bcast_avx2x4;
    f_res := res_A2____absorb_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
