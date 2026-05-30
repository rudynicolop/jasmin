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

(* A1120____absorb_avx2x4 *)
(* Local variables *)
Definition st_97 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 15182).
Definition AT_94 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15183).
Definition buf0_32 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15184).
Definition buf1_32 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15185).
Definition buf2_32 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15186).
Definition buf3_32 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15187).
Definition _TRAILB_54 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15188).
Definition _RATE8_44 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15189).
Definition offset_143 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15190).
Definition _LEN_90 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15191).
Definition ITERS_44 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15192).
Definition i_58 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15193).

(* Signature *)
Definition tyin_A1120____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 1120
    ; aarr U8 1120
    ; aarr U8 1120
    ; aarr U8 1120
    ; aint
    ; aint ].
Definition args_A1120____absorb_avx2x4 : seq var_i :=
  [:: st_97.(gv)
    ; AT_94.(gv)
    ; buf0_32.(gv)
    ; buf1_32.(gv)
    ; buf2_32.(gv)
    ; buf3_32.(gv)
    ; _TRAILB_54.(gv)
    ; _RATE8_44.(gv) ].
Definition tyout_A1120____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A1120____absorb_avx2x4 : seq var_i :=
  [:: st_97.(gv); AT_94.(gv) ].

(* Body *)
Definition body_A1120____absorb_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_143.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_90.(gv)) AT_none (aint) (Pconst (1120)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_94) (Pvar _LEN_90)) (Pvar _RATE8_44))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_97.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_143.(gv) ] A1120____addstate_avx2x4 [:: Pvar st_97
                                                                    ; Pvar AT_94
                                                                    ; Pvar buf0_32
                                                                    ; Pvar buf1_32
                                                                    ; Pvar buf2_32
                                                                    ; Pvar buf3_32
                                                                    ; Pvar offset_143
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_44) (Pvar AT_94)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_90.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_90) (Papp2 (Osub (Op_int)) (Pvar _RATE8_44) (Pvar AT_94))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_94.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_97.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_97 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_44.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_90) (Pvar _RATE8_44)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_58.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_58) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_44)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_97.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_143.(gv) ] A1120____addstate_avx2x4 [:: Pvar st_97
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_32
                                                                    ; Pvar buf1_32
                                                                    ; Pvar buf2_32
                                                                    ; Pvar buf3_32
                                                                    ; Pvar offset_143
                                                                    ; Pvar _RATE8_44
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_97.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_97 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_58.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_58) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_90.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_90) (Pvar _RATE8_44))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_97.(gv)
                                    ; Lvar AT_94.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1120____addstate_avx2x4 [:: Pvar st_97
                                                                    ; Pvar AT_94
                                                                    ; Pvar buf0_32
                                                                    ; Pvar buf1_32
                                                                    ; Pvar buf2_32
                                                                    ; Pvar buf3_32
                                                                    ; Pvar offset_143
                                                                    ; Pvar _LEN_90
                                                                    ; Pvar _TRAILB_54 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_54) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_97.(gv) ] __addratebit_avx2x4 [:: Pvar st_97
                                                                    ; Pvar _RATE8_44 ]) ]
                              [::]) ].

Definition fd_A1120____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____absorb_avx2x4;
    f_params := args_A1120____absorb_avx2x4;
    f_body := body_A1120____absorb_avx2x4;
    f_tyout := tyout_A1120____absorb_avx2x4;
    f_res := res_A1120____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
