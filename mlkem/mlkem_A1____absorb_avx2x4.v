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

(* A1____absorb_avx2x4 *)
(* Local variables *)
Definition st_23 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18103).
Definition AT_18 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18104).
Definition buf0_4 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18105).
Definition buf1_4 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18106).
Definition buf2_4 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18107).
Definition buf3_4 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18108).
Definition _TRAILB_10 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18109).
Definition _RATE8_7 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18110).
Definition offset_13 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18111).
Definition _LEN_16 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18112).
Definition ITERS_7 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18113).
Definition i_14 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18114).

(* Signature *)
Definition tyin_A1____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 1
    ; aarr U8 1
    ; aarr U8 1
    ; aarr U8 1
    ; aint
    ; aint ].
Definition args_A1____absorb_avx2x4 : seq var_i :=
  [:: st_23.(gv)
    ; AT_18.(gv)
    ; buf0_4.(gv)
    ; buf1_4.(gv)
    ; buf2_4.(gv)
    ; buf3_4.(gv)
    ; _TRAILB_10.(gv)
    ; _RATE8_7.(gv) ].
Definition tyout_A1____absorb_avx2x4 : seq atype := [:: aarr U256 25; aint ].
Definition res_A1____absorb_avx2x4 : seq var_i :=
  [:: st_23.(gv); AT_18.(gv) ].

(* Body *)
Definition body_A1____absorb_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_13.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_16.(gv)) AT_none (aint) (Pconst (1)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_18) (Pvar _LEN_16)) (Pvar _RATE8_7))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_23.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_13.(gv) ] A1____addstate_avx2x4 [:: Pvar st_23
                                                                    ; Pvar AT_18
                                                                    ; Pvar buf0_4
                                                                    ; Pvar buf1_4
                                                                    ; Pvar buf2_4
                                                                    ; Pvar buf3_4
                                                                    ; Pvar offset_13
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_7) (Pvar AT_18)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_16.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_16) (Papp2 (Osub (Op_int)) (Pvar _RATE8_7) (Pvar AT_18))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_18.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_23.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_23 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_7.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16) (Pvar _RATE8_7)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_14.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_14) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_7)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_23.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_13.(gv) ] A1____addstate_avx2x4 [:: Pvar st_23
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_4
                                                                    ; Pvar buf1_4
                                                                    ; Pvar buf2_4
                                                                    ; Pvar buf3_4
                                                                    ; Pvar offset_13
                                                                    ; Pvar _RATE8_7
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_23.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_23 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_14.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_14) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_16.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16) (Pvar _RATE8_7))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_23.(gv)
                                    ; Lvar AT_18.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1____addstate_avx2x4 [:: Pvar st_23
                                                                    ; Pvar AT_18
                                                                    ; Pvar buf0_4
                                                                    ; Pvar buf1_4
                                                                    ; Pvar buf2_4
                                                                    ; Pvar buf3_4
                                                                    ; Pvar offset_13
                                                                    ; Pvar _LEN_16
                                                                    ; Pvar _TRAILB_10 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_10) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_23.(gv) ] __addratebit_avx2x4 [:: Pvar st_23
                                                                    ; Pvar _RATE8_7 ]) ]
                              [::]) ].

Definition fd_A1____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____absorb_avx2x4;
    f_params := args_A1____absorb_avx2x4;
    f_body := body_A1____absorb_avx2x4;
    f_tyout := tyout_A1____absorb_avx2x4;
    f_res := res_A1____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
