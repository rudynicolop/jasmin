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

(* A32____absorb_bcast_avx2x4 *)
(* Local variables *)
Definition st_41 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 17389).
Definition AT_36 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17390).
Definition buf_55 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17391).
Definition _TRAILB_20 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17392).
Definition _RATE8_16 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17393).
Definition offset_45 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17394).
Definition _LEN_34 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17395).
Definition ITERS_16 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17396).
Definition i_25 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17397).

(* Signature *)
Definition tyin_A32____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 32; aint; aint ].
Definition args_A32____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_41.(gv); AT_36.(gv); buf_55.(gv); _TRAILB_20.(gv); _RATE8_16.(gv) ].
Definition tyout_A32____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A32____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_41.(gv); AT_36.(gv) ].

(* Body *)
Definition body_A32____absorb_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_45.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_34.(gv)) AT_none (aint) (Pconst (32)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_36) (Pvar _LEN_34)) (Pvar _RATE8_16))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_41.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_45.(gv) ] A32____addstate_bcast_avx2x4 [:: Pvar st_41
                                                                    ; Pvar AT_36
                                                                    ; Pvar buf_55
                                                                    ; Pvar offset_45
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_16) (Pvar AT_36)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_34.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_34) (Papp2 (Osub (Op_int)) (Pvar _RATE8_16) (Pvar AT_36))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_36.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_41.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_41 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_16.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_34) (Pvar _RATE8_16)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_25.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_25) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_16)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_41.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_45.(gv) ] A32____addstate_bcast_avx2x4 [:: Pvar st_41
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_55
                                                                    ; Pvar offset_45
                                                                    ; Pvar _RATE8_16
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_41.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_41 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_25.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_25) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_34.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_34) (Pvar _RATE8_16))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_41.(gv)
                                    ; Lvar AT_36.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A32____addstate_bcast_avx2x4 [:: Pvar st_41
                                                                    ; Pvar AT_36
                                                                    ; Pvar buf_55
                                                                    ; Pvar offset_45
                                                                    ; Pvar _LEN_34
                                                                    ; Pvar _TRAILB_20 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_20) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_41.(gv) ] __addratebit_avx2x4 [:: Pvar st_41
                                                                    ; Pvar _RATE8_16 ]) ]
                              [::]) ].

Definition fd_A32____absorb_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____absorb_bcast_avx2x4;
    f_params := args_A32____absorb_bcast_avx2x4;
    f_body := body_A32____absorb_bcast_avx2x4;
    f_tyout := tyout_A32____absorb_bcast_avx2x4;
    f_res := res_A32____absorb_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
