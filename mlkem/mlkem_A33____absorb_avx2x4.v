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

(* A33____absorb_avx2x4 *)
(* Local variables *)
Definition st_53 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 16957).
Definition AT_48 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16958).
Definition buf0_16 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 16959).
Definition buf1_16 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 16960).
Definition buf2_16 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 16961).
Definition buf3_16 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 16962).
Definition _TRAILB_28 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16963).
Definition _RATE8_22 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16964).
Definition offset_64 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16965).
Definition _LEN_46 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16966).
Definition ITERS_22 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16967).
Definition i_32 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16968).

(* Signature *)
Definition tyin_A33____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 33
    ; aarr U8 33
    ; aarr U8 33
    ; aarr U8 33
    ; aint
    ; aint ].
Definition args_A33____absorb_avx2x4 : seq var_i :=
  [:: st_53.(gv)
    ; AT_48.(gv)
    ; buf0_16.(gv)
    ; buf1_16.(gv)
    ; buf2_16.(gv)
    ; buf3_16.(gv)
    ; _TRAILB_28.(gv)
    ; _RATE8_22.(gv) ].
Definition tyout_A33____absorb_avx2x4 : seq atype := [:: aarr U256 25; aint ].
Definition res_A33____absorb_avx2x4 : seq var_i :=
  [:: st_53.(gv); AT_48.(gv) ].

(* Body *)
Definition body_A33____absorb_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_64.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_46.(gv)) AT_none (aint) (Pconst (33)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_48) (Pvar _LEN_46)) (Pvar _RATE8_22))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_53.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_64.(gv) ] A33____addstate_avx2x4 [:: Pvar st_53
                                                                    ; Pvar AT_48
                                                                    ; Pvar buf0_16
                                                                    ; Pvar buf1_16
                                                                    ; Pvar buf2_16
                                                                    ; Pvar buf3_16
                                                                    ; Pvar offset_64
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_22) (Pvar AT_48)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_46.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_46) (Papp2 (Osub (Op_int)) (Pvar _RATE8_22) (Pvar AT_48))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_48.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_53.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_53 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_22.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_46) (Pvar _RATE8_22)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_32.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_32) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_22)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_53.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_64.(gv) ] A33____addstate_avx2x4 [:: Pvar st_53
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_16
                                                                    ; Pvar buf1_16
                                                                    ; Pvar buf2_16
                                                                    ; Pvar buf3_16
                                                                    ; Pvar offset_64
                                                                    ; Pvar _RATE8_22
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_53.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_53 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_32.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_32) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_46.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_46) (Pvar _RATE8_22))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_53.(gv)
                                    ; Lvar AT_48.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A33____addstate_avx2x4 [:: Pvar st_53
                                                                    ; Pvar AT_48
                                                                    ; Pvar buf0_16
                                                                    ; Pvar buf1_16
                                                                    ; Pvar buf2_16
                                                                    ; Pvar buf3_16
                                                                    ; Pvar offset_64
                                                                    ; Pvar _LEN_46
                                                                    ; Pvar _TRAILB_28 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_28) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_53.(gv) ] __addratebit_avx2x4 [:: Pvar st_53
                                                                    ; Pvar _RATE8_22 ]) ]
                              [::]) ].

Definition fd_A33____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____absorb_avx2x4;
    f_params := args_A33____absorb_avx2x4;
    f_body := body_A33____absorb_avx2x4;
    f_tyout := tyout_A33____absorb_avx2x4;
    f_res := res_A33____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
