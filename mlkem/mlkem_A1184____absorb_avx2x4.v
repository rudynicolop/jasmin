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

(* A1184____absorb_avx2x4 *)
(* Local variables *)
Definition st_77 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 15946).
Definition AT_74 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15947).
Definition buf0_24 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15948).
Definition buf1_24 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15949).
Definition buf2_24 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15950).
Definition buf3_24 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15951).
Definition _TRAILB_42 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15952).
Definition _RATE8_34 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15953).
Definition offset_109 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15954).
Definition _LEN_70 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15955).
Definition ITERS_34 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15956).
Definition i_46 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15957).

(* Signature *)
Definition tyin_A1184____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 1184
    ; aarr U8 1184
    ; aarr U8 1184
    ; aarr U8 1184
    ; aint
    ; aint ].
Definition args_A1184____absorb_avx2x4 : seq var_i :=
  [:: st_77.(gv)
    ; AT_74.(gv)
    ; buf0_24.(gv)
    ; buf1_24.(gv)
    ; buf2_24.(gv)
    ; buf3_24.(gv)
    ; _TRAILB_42.(gv)
    ; _RATE8_34.(gv) ].
Definition tyout_A1184____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A1184____absorb_avx2x4 : seq var_i :=
  [:: st_77.(gv); AT_74.(gv) ].

(* Body *)
Definition body_A1184____absorb_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_109.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_70.(gv)) AT_none (aint) (Pconst (1184)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_74) (Pvar _LEN_70)) (Pvar _RATE8_34))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_77.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_109.(gv) ] A1184____addstate_avx2x4 [:: Pvar st_77
                                                                    ; Pvar AT_74
                                                                    ; Pvar buf0_24
                                                                    ; Pvar buf1_24
                                                                    ; Pvar buf2_24
                                                                    ; Pvar buf3_24
                                                                    ; Pvar offset_109
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_34) (Pvar AT_74)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_70.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_70) (Papp2 (Osub (Op_int)) (Pvar _RATE8_34) (Pvar AT_74))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_74.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_77.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_77 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_34.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_70) (Pvar _RATE8_34)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_46.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_46) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_34)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_77.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_109.(gv) ] A1184____addstate_avx2x4 [:: Pvar st_77
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_24
                                                                    ; Pvar buf1_24
                                                                    ; Pvar buf2_24
                                                                    ; Pvar buf3_24
                                                                    ; Pvar offset_109
                                                                    ; Pvar _RATE8_34
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_77.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_77 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_46.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_46) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_70.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_70) (Pvar _RATE8_34))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_77.(gv)
                                    ; Lvar AT_74.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1184____addstate_avx2x4 [:: Pvar st_77
                                                                    ; Pvar AT_74
                                                                    ; Pvar buf0_24
                                                                    ; Pvar buf1_24
                                                                    ; Pvar buf2_24
                                                                    ; Pvar buf3_24
                                                                    ; Pvar offset_109
                                                                    ; Pvar _LEN_70
                                                                    ; Pvar _TRAILB_42 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_42) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_77.(gv) ] __addratebit_avx2x4 [:: Pvar st_77
                                                                    ; Pvar _RATE8_34 ]) ]
                              [::]) ].

Definition fd_A1184____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____absorb_avx2x4;
    f_params := args_A1184____absorb_avx2x4;
    f_body := body_A1184____absorb_avx2x4;
    f_tyout := tyout_A1184____absorb_avx2x4;
    f_res := res_A1184____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
