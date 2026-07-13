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

(* A32____absorb_avx2x4 *)
(* Local variables *)
Definition st_43 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 17339).
Definition AT_38 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17340).
Definition buf0_12 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17341).
Definition buf1_12 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17342).
Definition buf2_12 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17343).
Definition buf3_12 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17344).
Definition _TRAILB_22 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17345).
Definition _RATE8_17 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17346).
Definition offset_47 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17347).
Definition _LEN_36 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17348).
Definition ITERS_17 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17349).
Definition i_26 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17350).

(* Signature *)
Definition tyin_A32____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 32
    ; aarr U8 32
    ; aarr U8 32
    ; aarr U8 32
    ; aint
    ; aint ].
Definition args_A32____absorb_avx2x4 : seq var_i :=
  [:: st_43.(gv)
    ; AT_38.(gv)
    ; buf0_12.(gv)
    ; buf1_12.(gv)
    ; buf2_12.(gv)
    ; buf3_12.(gv)
    ; _TRAILB_22.(gv)
    ; _RATE8_17.(gv) ].
Definition tyout_A32____absorb_avx2x4 : seq atype := [:: aarr U256 25; aint ].
Definition res_A32____absorb_avx2x4 : seq var_i :=
  [:: st_43.(gv); AT_38.(gv) ].

(* Body *)
Definition body_A32____absorb_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_47.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_36.(gv)) AT_none (aint) (Pconst (32)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_38) (Pvar _LEN_36)) (Pvar _RATE8_17))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_43.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_47.(gv) ] A32____addstate_avx2x4 [:: Pvar st_43
                                                                    ; Pvar AT_38
                                                                    ; Pvar buf0_12
                                                                    ; Pvar buf1_12
                                                                    ; Pvar buf2_12
                                                                    ; Pvar buf3_12
                                                                    ; Pvar offset_47
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_17) (Pvar AT_38)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_36.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_36) (Papp2 (Osub (Op_int)) (Pvar _RATE8_17) (Pvar AT_38))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_38.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_43.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_43 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_17.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_36) (Pvar _RATE8_17)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_26.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_26) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_17)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_43.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_47.(gv) ] A32____addstate_avx2x4 [:: Pvar st_43
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_12
                                                                    ; Pvar buf1_12
                                                                    ; Pvar buf2_12
                                                                    ; Pvar buf3_12
                                                                    ; Pvar offset_47
                                                                    ; Pvar _RATE8_17
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_43.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_43 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_26.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_26) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_36.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_36) (Pvar _RATE8_17))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_43.(gv)
                                    ; Lvar AT_38.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A32____addstate_avx2x4 [:: Pvar st_43
                                                                    ; Pvar AT_38
                                                                    ; Pvar buf0_12
                                                                    ; Pvar buf1_12
                                                                    ; Pvar buf2_12
                                                                    ; Pvar buf3_12
                                                                    ; Pvar offset_47
                                                                    ; Pvar _LEN_36
                                                                    ; Pvar _TRAILB_22 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_22) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_43.(gv) ] __addratebit_avx2x4 [:: Pvar st_43
                                                                    ; Pvar _RATE8_17 ]) ]
                              [::]) ].

Definition fd_A32____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____absorb_avx2x4;
    f_params := args_A32____absorb_avx2x4;
    f_body := body_A32____absorb_avx2x4;
    f_tyout := tyout_A32____absorb_avx2x4;
    f_res := res_A32____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
