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
Definition st_15182 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 15182).
Definition AT_15183 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15183).
Definition buf0_15184 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15184).
Definition buf1_15185 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15185).
Definition buf2_15186 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15186).
Definition buf3_15187 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15187).
Definition _TRAILB_15188 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15188).
Definition _RATE8_15189 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15189).
Definition offset_15190 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15190).
Definition _LEN_15191 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15191).
Definition ITERS_15192 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15192).
Definition i_15193 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15193).

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
  [:: st_15182.(gv)
    ; AT_15183.(gv)
    ; buf0_15184.(gv)
    ; buf1_15185.(gv)
    ; buf2_15186.(gv)
    ; buf3_15187.(gv)
    ; _TRAILB_15188.(gv)
    ; _RATE8_15189.(gv) ].
Definition tyout_A1120____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A1120____absorb_avx2x4 : seq var_i :=
  [:: st_15182.(gv); AT_15183.(gv) ].

(* Body *)
Definition body_A1120____absorb_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_15190.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15191.(gv)) AT_none (aint) (Pconst (1120)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_15183) (Pvar _LEN_15191)) (Pvar _RATE8_15189))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_15182.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_15190.(gv) ] A1120____addstate_avx2x4 [:: Pvar st_15182
                                                                    ; Pvar AT_15183
                                                                    ; Pvar buf0_15184
                                                                    ; Pvar buf1_15185
                                                                    ; Pvar buf2_15186
                                                                    ; Pvar buf3_15187
                                                                    ; Pvar offset_15190
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_15189) (Pvar AT_15183)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15191.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_15191) (Papp2 (Osub (Op_int)) (Pvar _RATE8_15189) (Pvar AT_15183))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_15183.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_15182.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_15182 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_15192.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15191) (Pvar _RATE8_15189)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_15193.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15193) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_15192)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_15182.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_15190.(gv) ] A1120____addstate_avx2x4 [:: Pvar st_15182
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_15184
                                                                    ; Pvar buf1_15185
                                                                    ; Pvar buf2_15186
                                                                    ; Pvar buf3_15187
                                                                    ; Pvar offset_15190
                                                                    ; Pvar _RATE8_15189
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_15182.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_15182 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_15193.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15193) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15191.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15191) (Pvar _RATE8_15189))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_15182.(gv)
                                    ; Lvar AT_15183.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1120____addstate_avx2x4 [:: Pvar st_15182
                                                                    ; Pvar AT_15183
                                                                    ; Pvar buf0_15184
                                                                    ; Pvar buf1_15185
                                                                    ; Pvar buf2_15186
                                                                    ; Pvar buf3_15187
                                                                    ; Pvar offset_15190
                                                                    ; Pvar _LEN_15191
                                                                    ; Pvar _TRAILB_15188 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_15188) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_15182.(gv) ] __addratebit_avx2x4 [:: Pvar st_15182
                                                                    ; Pvar _RATE8_15189 ]) ]
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
