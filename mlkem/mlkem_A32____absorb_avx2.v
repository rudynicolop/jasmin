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

(* A32____absorb_avx2 *)
(* Local variables *)
Definition st_37 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 17456).
Definition AT_34 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17457).
Definition buf_51 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17458).
Definition _TRAILB_18 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17459).
Definition _RATE8_14 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17460).
Definition offset_41 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17461).
Definition _LEN_30 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17462).
Definition ITERS_14 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17463).
Definition i_23 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17464).

(* Signature *)
Definition tyin_A32____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 32; aint; aint ].
Definition args_A32____absorb_avx2 : seq var_i :=
  [:: st_37.(gv); AT_34.(gv); buf_51.(gv); _TRAILB_18.(gv); _RATE8_14.(gv) ].
Definition tyout_A32____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A32____absorb_avx2 : seq var_i := [:: st_37.(gv); AT_34.(gv) ].

(* Body *)
Definition body_A32____absorb_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_41.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_30.(gv)) AT_none (aint) (Pconst (32)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_34) (Pvar _LEN_30)) (Pvar _RATE8_14))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_37.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_41.(gv) ] A32____addstate_avx2 [:: Pvar st_37
                                                                    ; Pvar AT_34
                                                                    ; Pvar buf_51
                                                                    ; Pvar offset_41
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_14) (Pvar AT_34)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_30.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_30) (Papp2 (Osub (Op_int)) (Pvar _RATE8_14) (Pvar AT_34))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_34.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_37.(gv) ] _keccakf1600_avx2 [:: Pvar st_37 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_14.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_30) (Pvar _RATE8_14)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_23.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_23) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_14)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_37.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_41.(gv) ] A32____addstate_avx2 [:: Pvar st_37
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_51
                                                                    ; Pvar offset_41
                                                                    ; Pvar _RATE8_14
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_37.(gv) ] _keccakf1600_avx2 [:: Pvar st_37 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_23.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_23) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_30.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_30) (Pvar _RATE8_14))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_37.(gv)
                                    ; Lvar AT_34.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A32____addstate_avx2 [:: Pvar st_37
                                                                    ; Pvar AT_34
                                                                    ; Pvar buf_51
                                                                    ; Pvar offset_41
                                                                    ; Pvar _LEN_30
                                                                    ; Pvar _TRAILB_18 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_18) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_37.(gv) ] __addratebit_avx2 [:: Pvar st_37
                                                                    ; Pvar _RATE8_14 ]) ]
                              [::]) ].

Definition fd_A32____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____absorb_avx2;
    f_params := args_A32____absorb_avx2;
    f_body := body_A32____absorb_avx2;
    f_tyout := tyout_A32____absorb_avx2;
    f_res := res_A32____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
