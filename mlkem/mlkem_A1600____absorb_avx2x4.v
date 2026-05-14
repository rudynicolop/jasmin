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

(* A1600____absorb_avx2x4 *)
(* Local variables *)
Definition st_14800 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14800).
Definition AT_14801 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14801).
Definition buf0_14802 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14802).
Definition buf1_14803 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14803).
Definition buf2_14804 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14804).
Definition buf3_14805 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14805).
Definition _TRAILB_14806 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14806).
Definition _RATE8_14807 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14807).
Definition offset_14808 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14808).
Definition _LEN_14809 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14809).
Definition ITERS_14810 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14810).
Definition i_14811 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14811).

(* Signature *)
Definition tyin_A1600____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 1600
    ; aarr U8 1600
    ; aarr U8 1600
    ; aarr U8 1600
    ; aint
    ; aint ].
Definition args_A1600____absorb_avx2x4 : seq var_i :=
  [:: st_14800.(gv)
    ; AT_14801.(gv)
    ; buf0_14802.(gv)
    ; buf1_14803.(gv)
    ; buf2_14804.(gv)
    ; buf3_14805.(gv)
    ; _TRAILB_14806.(gv)
    ; _RATE8_14807.(gv) ].
Definition tyout_A1600____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A1600____absorb_avx2x4 : seq var_i :=
  [:: st_14800.(gv); AT_14801.(gv) ].

(* Body *)
Definition body_A1600____absorb_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_14808.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14809.(gv)) AT_none (aint) (Pconst (1600)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_14801) (Pvar _LEN_14809)) (Pvar _RATE8_14807))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_14800.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_14808.(gv) ] A1600____addstate_avx2x4 [:: Pvar st_14800
                                                                    ; Pvar AT_14801
                                                                    ; Pvar buf0_14802
                                                                    ; Pvar buf1_14803
                                                                    ; Pvar buf2_14804
                                                                    ; Pvar buf3_14805
                                                                    ; Pvar offset_14808
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_14807) (Pvar AT_14801)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14809.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_14809) (Papp2 (Osub (Op_int)) (Pvar _RATE8_14807) (Pvar AT_14801))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_14801.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_14800.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_14800 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_14810.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14809) (Pvar _RATE8_14807)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_14811.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_14811) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_14810)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_14800.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_14808.(gv) ] A1600____addstate_avx2x4 [:: Pvar st_14800
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_14802
                                                                    ; Pvar buf1_14803
                                                                    ; Pvar buf2_14804
                                                                    ; Pvar buf3_14805
                                                                    ; Pvar offset_14808
                                                                    ; Pvar _RATE8_14807
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_14800.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_14800 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_14811.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_14811) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14809.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14809) (Pvar _RATE8_14807))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_14800.(gv)
                                    ; Lvar AT_14801.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1600____addstate_avx2x4 [:: Pvar st_14800
                                                                    ; Pvar AT_14801
                                                                    ; Pvar buf0_14802
                                                                    ; Pvar buf1_14803
                                                                    ; Pvar buf2_14804
                                                                    ; Pvar buf3_14805
                                                                    ; Pvar offset_14808
                                                                    ; Pvar _LEN_14809
                                                                    ; Pvar _TRAILB_14806 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_14806) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_14800.(gv) ] __addratebit_avx2x4 [:: Pvar st_14800
                                                                    ; Pvar _RATE8_14807 ]) ]
                              [::]) ].

Definition fd_A1600____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____absorb_avx2x4;
    f_params := args_A1600____absorb_avx2x4;
    f_body := body_A1600____absorb_avx2x4;
    f_tyout := tyout_A1600____absorb_avx2x4;
    f_res := res_A1600____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
