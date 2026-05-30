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

(* A1600____absorb_avx2 *)
(* Local variables *)
Definition st_101 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14917).
Definition AT_100 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14918).
Definition buf_147 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14919).
Definition _TRAILB_56 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14920).
Definition _RATE8_46 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14921).
Definition offset_154 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14922).
Definition _LEN_94 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14923).
Definition ITERS_46 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14924).
Definition i_61 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14925).

(* Signature *)
Definition tyin_A1600____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1600; aint; aint ].
Definition args_A1600____absorb_avx2 : seq var_i :=
  [:: st_101.(gv)
    ; AT_100.(gv)
    ; buf_147.(gv)
    ; _TRAILB_56.(gv)
    ; _RATE8_46.(gv) ].
Definition tyout_A1600____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A1600____absorb_avx2 : seq var_i :=
  [:: st_101.(gv); AT_100.(gv) ].

(* Body *)
Definition body_A1600____absorb_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_154.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_94.(gv)) AT_none (aint) (Pconst (1600)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_100) (Pvar _LEN_94)) (Pvar _RATE8_46))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_101.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_154.(gv) ] A1600____addstate_avx2 [:: Pvar st_101
                                                                    ; Pvar AT_100
                                                                    ; Pvar buf_147
                                                                    ; Pvar offset_154
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_46) (Pvar AT_100)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_94.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_94) (Papp2 (Osub (Op_int)) (Pvar _RATE8_46) (Pvar AT_100))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_100.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_101.(gv) ] _keccakf1600_avx2 [:: Pvar st_101 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_46.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_94) (Pvar _RATE8_46)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_61.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_61) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_46)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_101.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_154.(gv) ] A1600____addstate_avx2 [:: Pvar st_101
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_147
                                                                    ; Pvar offset_154
                                                                    ; Pvar _RATE8_46
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_101.(gv) ] _keccakf1600_avx2 [:: Pvar st_101 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_61.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_61) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_94.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_94) (Pvar _RATE8_46))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_101.(gv)
                                    ; Lvar AT_100.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1600____addstate_avx2 [:: Pvar st_101
                                                                    ; Pvar AT_100
                                                                    ; Pvar buf_147
                                                                    ; Pvar offset_154
                                                                    ; Pvar _LEN_94
                                                                    ; Pvar _TRAILB_56 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_56) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_101.(gv) ] __addratebit_avx2 [:: Pvar st_101
                                                                    ; Pvar _RATE8_46 ]) ]
                              [::]) ].

Definition fd_A1600____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____absorb_avx2;
    f_params := args_A1600____absorb_avx2;
    f_body := body_A1600____absorb_avx2;
    f_tyout := tyout_A1600____absorb_avx2;
    f_res := res_A1600____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
