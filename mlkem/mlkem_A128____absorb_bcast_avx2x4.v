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

(* A128____absorb_bcast_avx2x4 *)
(* Local variables *)
Definition st_65 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 16378).
Definition AT_62 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16379).
Definition buf_95 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 16380).
Definition _TRAILB_34 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16381).
Definition _RATE8_28 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16382).
Definition offset_90 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16383).
Definition _LEN_58 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16384).
Definition ITERS_28 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16385).
Definition i_39 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16386).

(* Signature *)
Definition tyin_A128____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 128; aint; aint ].
Definition args_A128____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_65.(gv); AT_62.(gv); buf_95.(gv); _TRAILB_34.(gv); _RATE8_28.(gv) ].
Definition tyout_A128____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A128____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_65.(gv); AT_62.(gv) ].

(* Body *)
Definition body_A128____absorb_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_90.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_58.(gv)) AT_none (aint) (Pconst (128)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_62) (Pvar _LEN_58)) (Pvar _RATE8_28))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_65.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_90.(gv) ] A128____addstate_bcast_avx2x4 [:: Pvar st_65
                                                                    ; Pvar AT_62
                                                                    ; Pvar buf_95
                                                                    ; Pvar offset_90
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_28) (Pvar AT_62)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_58.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_58) (Papp2 (Osub (Op_int)) (Pvar _RATE8_28) (Pvar AT_62))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_62.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_65.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_65 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_28.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_58) (Pvar _RATE8_28)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_39.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_39) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_28)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_65.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_90.(gv) ] A128____addstate_bcast_avx2x4 [:: Pvar st_65
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_95
                                                                    ; Pvar offset_90
                                                                    ; Pvar _RATE8_28
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_65.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_65 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_39.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_39) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_58.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_58) (Pvar _RATE8_28))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_65.(gv)
                                    ; Lvar AT_62.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A128____addstate_bcast_avx2x4 [:: Pvar st_65
                                                                    ; Pvar AT_62
                                                                    ; Pvar buf_95
                                                                    ; Pvar offset_90
                                                                    ; Pvar _LEN_58
                                                                    ; Pvar _TRAILB_34 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_34) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_65.(gv) ] __addratebit_avx2x4 [:: Pvar st_65
                                                                    ; Pvar _RATE8_28 ]) ]
                              [::]) ].

Definition fd_A128____absorb_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____absorb_bcast_avx2x4;
    f_params := args_A128____absorb_bcast_avx2x4;
    f_body := body_A128____absorb_bcast_avx2x4;
    f_tyout := tyout_A128____absorb_bcast_avx2x4;
    f_res := res_A128____absorb_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
