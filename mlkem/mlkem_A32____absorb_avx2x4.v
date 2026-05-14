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
Definition st_17339 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 17339).
Definition AT_17340 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17340).
Definition buf0_17341 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17341).
Definition buf1_17342 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17342).
Definition buf2_17343 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17343).
Definition buf3_17344 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17344).
Definition _TRAILB_17345 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17345).
Definition _RATE8_17346 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17346).
Definition offset_17347 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17347).
Definition _LEN_17348 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17348).
Definition ITERS_17349 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17349).
Definition i_17350 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17350).

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
  [:: st_17339.(gv)
    ; AT_17340.(gv)
    ; buf0_17341.(gv)
    ; buf1_17342.(gv)
    ; buf2_17343.(gv)
    ; buf3_17344.(gv)
    ; _TRAILB_17345.(gv)
    ; _RATE8_17346.(gv) ].
Definition tyout_A32____absorb_avx2x4 : seq atype := [:: aarr U256 25; aint ].
Definition res_A32____absorb_avx2x4 : seq var_i :=
  [:: st_17339.(gv); AT_17340.(gv) ].

(* Body *)
Definition body_A32____absorb_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_17347.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_17348.(gv)) AT_none (aint) (Pconst (32)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_17340) (Pvar _LEN_17348)) (Pvar _RATE8_17346))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_17339.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_17347.(gv) ] A32____addstate_avx2x4 [:: Pvar st_17339
                                                                    ; Pvar AT_17340
                                                                    ; Pvar buf0_17341
                                                                    ; Pvar buf1_17342
                                                                    ; Pvar buf2_17343
                                                                    ; Pvar buf3_17344
                                                                    ; Pvar offset_17347
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_17346) (Pvar AT_17340)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_17348.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_17348) (Papp2 (Osub (Op_int)) (Pvar _RATE8_17346) (Pvar AT_17340))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_17340.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_17339.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_17339 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_17349.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17348) (Pvar _RATE8_17346)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_17350.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17350) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_17349)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_17339.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_17347.(gv) ] A32____addstate_avx2x4 [:: Pvar st_17339
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_17341
                                                                    ; Pvar buf1_17342
                                                                    ; Pvar buf2_17343
                                                                    ; Pvar buf3_17344
                                                                    ; Pvar offset_17347
                                                                    ; Pvar _RATE8_17346
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_17339.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_17339 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_17350.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17350) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_17348.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17348) (Pvar _RATE8_17346))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_17339.(gv)
                                    ; Lvar AT_17340.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A32____addstate_avx2x4 [:: Pvar st_17339
                                                                    ; Pvar AT_17340
                                                                    ; Pvar buf0_17341
                                                                    ; Pvar buf1_17342
                                                                    ; Pvar buf2_17343
                                                                    ; Pvar buf3_17344
                                                                    ; Pvar offset_17347
                                                                    ; Pvar _LEN_17348
                                                                    ; Pvar _TRAILB_17345 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17345) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_17339.(gv) ] __addratebit_avx2x4 [:: Pvar st_17339
                                                                    ; Pvar _RATE8_17346 ]) ]
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
