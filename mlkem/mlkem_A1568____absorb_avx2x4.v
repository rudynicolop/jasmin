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

(* A1568____absorb_avx2x4 *)
(* Local variables *)
Definition st_87 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 15564).
Definition AT_84 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15565).
Definition buf0_28 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15566).
Definition buf1_28 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15567).
Definition buf2_28 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15568).
Definition buf3_28 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15569).
Definition _TRAILB_48 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15570).
Definition _RATE8_39 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15571).
Definition offset_126 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15572).
Definition _LEN_80 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15573).
Definition ITERS_39 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15574).
Definition i_52 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15575).

(* Signature *)
Definition tyin_A1568____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 1568
    ; aarr U8 1568
    ; aarr U8 1568
    ; aarr U8 1568
    ; aint
    ; aint ].
Definition args_A1568____absorb_avx2x4 : seq var_i :=
  [:: st_87.(gv)
    ; AT_84.(gv)
    ; buf0_28.(gv)
    ; buf1_28.(gv)
    ; buf2_28.(gv)
    ; buf3_28.(gv)
    ; _TRAILB_48.(gv)
    ; _RATE8_39.(gv) ].
Definition tyout_A1568____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A1568____absorb_avx2x4 : seq var_i :=
  [:: st_87.(gv); AT_84.(gv) ].

(* Body *)
Definition body_A1568____absorb_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_126.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_80.(gv)) AT_none (aint) (Pconst (1568)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_84) (Pvar _LEN_80)) (Pvar _RATE8_39))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_87.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_126.(gv) ] A1568____addstate_avx2x4 [:: Pvar st_87
                                                                    ; Pvar AT_84
                                                                    ; Pvar buf0_28
                                                                    ; Pvar buf1_28
                                                                    ; Pvar buf2_28
                                                                    ; Pvar buf3_28
                                                                    ; Pvar offset_126
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_39) (Pvar AT_84)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_80.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_80) (Papp2 (Osub (Op_int)) (Pvar _RATE8_39) (Pvar AT_84))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_84.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_87.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_87 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_39.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_80) (Pvar _RATE8_39)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_52.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_52) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_39)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_87.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_126.(gv) ] A1568____addstate_avx2x4 [:: Pvar st_87
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_28
                                                                    ; Pvar buf1_28
                                                                    ; Pvar buf2_28
                                                                    ; Pvar buf3_28
                                                                    ; Pvar offset_126
                                                                    ; Pvar _RATE8_39
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_87.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_87 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_52.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_52) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_80.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_80) (Pvar _RATE8_39))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_87.(gv)
                                    ; Lvar AT_84.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1568____addstate_avx2x4 [:: Pvar st_87
                                                                    ; Pvar AT_84
                                                                    ; Pvar buf0_28
                                                                    ; Pvar buf1_28
                                                                    ; Pvar buf2_28
                                                                    ; Pvar buf3_28
                                                                    ; Pvar offset_126
                                                                    ; Pvar _LEN_80
                                                                    ; Pvar _TRAILB_48 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_48) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_87.(gv) ] __addratebit_avx2x4 [:: Pvar st_87
                                                                    ; Pvar _RATE8_39 ]) ]
                              [::]) ].

Definition fd_A1568____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____absorb_avx2x4;
    f_params := args_A1568____absorb_avx2x4;
    f_body := body_A1568____absorb_avx2x4;
    f_tyout := tyout_A1568____absorb_avx2x4;
    f_res := res_A1568____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
