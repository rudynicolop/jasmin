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

(* A1120____absorb_avx2 *)
(* Local variables *)
Definition st_91 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 15299).
Definition AT_90 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15300).
Definition buf_133 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15301).
Definition _TRAILB_50 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15302).
Definition _RATE8_41 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15303).
Definition offset_137 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15304).
Definition _LEN_84 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15305).
Definition ITERS_41 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15306).
Definition i_55 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15307).

(* Signature *)
Definition tyin_A1120____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1120; aint; aint ].
Definition args_A1120____absorb_avx2 : seq var_i :=
  [:: st_91.(gv); AT_90.(gv); buf_133.(gv); _TRAILB_50.(gv); _RATE8_41.(gv) ].
Definition tyout_A1120____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A1120____absorb_avx2 : seq var_i :=
  [:: st_91.(gv); AT_90.(gv) ].

(* Body *)
Definition body_A1120____absorb_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_137.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_84.(gv)) AT_none (aint) (Pconst (1120)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_90) (Pvar _LEN_84)) (Pvar _RATE8_41))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_91.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_137.(gv) ] A1120____addstate_avx2 [:: Pvar st_91
                                                                    ; Pvar AT_90
                                                                    ; Pvar buf_133
                                                                    ; Pvar offset_137
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_41) (Pvar AT_90)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_84.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_84) (Papp2 (Osub (Op_int)) (Pvar _RATE8_41) (Pvar AT_90))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_90.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_91.(gv) ] _keccakf1600_avx2 [:: Pvar st_91 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_41.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_84) (Pvar _RATE8_41)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_55.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_55) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_41)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_91.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_137.(gv) ] A1120____addstate_avx2 [:: Pvar st_91
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_133
                                                                    ; Pvar offset_137
                                                                    ; Pvar _RATE8_41
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_91.(gv) ] _keccakf1600_avx2 [:: Pvar st_91 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_55.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_55) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_84.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_84) (Pvar _RATE8_41))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_91.(gv)
                                    ; Lvar AT_90.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1120____addstate_avx2 [:: Pvar st_91
                                                                    ; Pvar AT_90
                                                                    ; Pvar buf_133
                                                                    ; Pvar offset_137
                                                                    ; Pvar _LEN_84
                                                                    ; Pvar _TRAILB_50 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_50) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_91.(gv) ] __addratebit_avx2 [:: Pvar st_91
                                                                    ; Pvar _RATE8_41 ]) ]
                              [::]) ].

Definition fd_A1120____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____absorb_avx2;
    f_params := args_A1120____absorb_avx2;
    f_body := body_A1120____absorb_avx2;
    f_tyout := tyout_A1120____absorb_avx2;
    f_res := res_A1120____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
