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

(* A2____absorb_avx2x4 *)
(* Local variables *)
Definition st_33 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 17721).
Definition AT_28 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17722).
Definition buf0_8 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17723).
Definition buf1_8 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17724).
Definition buf2_8 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17725).
Definition buf3_8 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17726).
Definition _TRAILB_16 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17727).
Definition _RATE8_12 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17728).
Definition offset_30 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17729).
Definition _LEN_26 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17730).
Definition ITERS_12 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17731).
Definition i_20 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17732).

(* Signature *)
Definition tyin_A2____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 2
    ; aarr U8 2
    ; aarr U8 2
    ; aarr U8 2
    ; aint
    ; aint ].
Definition args_A2____absorb_avx2x4 : seq var_i :=
  [:: st_33.(gv)
    ; AT_28.(gv)
    ; buf0_8.(gv)
    ; buf1_8.(gv)
    ; buf2_8.(gv)
    ; buf3_8.(gv)
    ; _TRAILB_16.(gv)
    ; _RATE8_12.(gv) ].
Definition tyout_A2____absorb_avx2x4 : seq atype := [:: aarr U256 25; aint ].
Definition res_A2____absorb_avx2x4 : seq var_i :=
  [:: st_33.(gv); AT_28.(gv) ].

(* Body *)
Definition body_A2____absorb_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_30.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_26.(gv)) AT_none (aint) (Pconst (2)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_28) (Pvar _LEN_26)) (Pvar _RATE8_12))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_33.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_30.(gv) ] A2____addstate_avx2x4 [:: Pvar st_33
                                                                    ; Pvar AT_28
                                                                    ; Pvar buf0_8
                                                                    ; Pvar buf1_8
                                                                    ; Pvar buf2_8
                                                                    ; Pvar buf3_8
                                                                    ; Pvar offset_30
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_12) (Pvar AT_28)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_26.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_26) (Papp2 (Osub (Op_int)) (Pvar _RATE8_12) (Pvar AT_28))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_28.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_33.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_33 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_12.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_26) (Pvar _RATE8_12)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_20.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_12)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_33.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_30.(gv) ] A2____addstate_avx2x4 [:: Pvar st_33
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_8
                                                                    ; Pvar buf1_8
                                                                    ; Pvar buf2_8
                                                                    ; Pvar buf3_8
                                                                    ; Pvar offset_30
                                                                    ; Pvar _RATE8_12
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_33.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_33 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_20.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_26.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_26) (Pvar _RATE8_12))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_33.(gv)
                                    ; Lvar AT_28.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A2____addstate_avx2x4 [:: Pvar st_33
                                                                    ; Pvar AT_28
                                                                    ; Pvar buf0_8
                                                                    ; Pvar buf1_8
                                                                    ; Pvar buf2_8
                                                                    ; Pvar buf3_8
                                                                    ; Pvar offset_30
                                                                    ; Pvar _LEN_26
                                                                    ; Pvar _TRAILB_16 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_33.(gv) ] __addratebit_avx2x4 [:: Pvar st_33
                                                                    ; Pvar _RATE8_12 ]) ]
                              [::]) ].

Definition fd_A2____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____absorb_avx2x4;
    f_params := args_A2____absorb_avx2x4;
    f_body := body_A2____absorb_avx2x4;
    f_tyout := tyout_A2____absorb_avx2x4;
    f_res := res_A2____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
