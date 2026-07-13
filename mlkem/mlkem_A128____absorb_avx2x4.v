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

(* A128____absorb_avx2x4 *)
(* Local variables *)
Definition st_67 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 16328).
Definition AT_64 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16329).
Definition buf0_20 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16330).
Definition buf1_20 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16331).
Definition buf2_20 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16332).
Definition buf3_20 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16333).
Definition _TRAILB_36 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16334).
Definition _RATE8_29 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16335).
Definition offset_92 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16336).
Definition _LEN_60 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16337).
Definition ITERS_29 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16338).
Definition i_40 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16339).

(* Signature *)
Definition tyin_A128____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 128
    ; aarr U8 128
    ; aarr U8 128
    ; aarr U8 128
    ; aint
    ; aint ].
Definition args_A128____absorb_avx2x4 : seq var_i :=
  [:: st_67.(gv)
    ; AT_64.(gv)
    ; buf0_20.(gv)
    ; buf1_20.(gv)
    ; buf2_20.(gv)
    ; buf3_20.(gv)
    ; _TRAILB_36.(gv)
    ; _RATE8_29.(gv) ].
Definition tyout_A128____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A128____absorb_avx2x4 : seq var_i :=
  [:: st_67.(gv); AT_64.(gv) ].

(* Body *)
Definition body_A128____absorb_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_92.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_60.(gv)) AT_none (aint) (Pconst (128)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_64) (Pvar _LEN_60)) (Pvar _RATE8_29))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_67.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_92.(gv) ] A128____addstate_avx2x4 [:: Pvar st_67
                                                                    ; Pvar AT_64
                                                                    ; Pvar buf0_20
                                                                    ; Pvar buf1_20
                                                                    ; Pvar buf2_20
                                                                    ; Pvar buf3_20
                                                                    ; Pvar offset_92
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_29) (Pvar AT_64)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_60.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_60) (Papp2 (Osub (Op_int)) (Pvar _RATE8_29) (Pvar AT_64))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_64.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_67.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_67 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_29.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_60) (Pvar _RATE8_29)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_40.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_40) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_29)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_67.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_92.(gv) ] A128____addstate_avx2x4 [:: Pvar st_67
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_20
                                                                    ; Pvar buf1_20
                                                                    ; Pvar buf2_20
                                                                    ; Pvar buf3_20
                                                                    ; Pvar offset_92
                                                                    ; Pvar _RATE8_29
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_67.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_67 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_40.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_40) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_60.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_60) (Pvar _RATE8_29))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_67.(gv)
                                    ; Lvar AT_64.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A128____addstate_avx2x4 [:: Pvar st_67
                                                                    ; Pvar AT_64
                                                                    ; Pvar buf0_20
                                                                    ; Pvar buf1_20
                                                                    ; Pvar buf2_20
                                                                    ; Pvar buf3_20
                                                                    ; Pvar offset_92
                                                                    ; Pvar _LEN_60
                                                                    ; Pvar _TRAILB_36 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_36) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_67.(gv) ] __addratebit_avx2x4 [:: Pvar st_67
                                                                    ; Pvar _RATE8_29 ]) ]
                              [::]) ].

Definition fd_A128____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____absorb_avx2x4;
    f_params := args_A128____absorb_avx2x4;
    f_body := body_A128____absorb_avx2x4;
    f_tyout := tyout_A128____absorb_avx2x4;
    f_res := res_A128____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
