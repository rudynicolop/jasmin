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

(* A1____absorb_avx2x4 *)
(* Local variables *)
Definition st_18103 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 18103).
Definition AT_18104 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18104).
Definition buf0_18105 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18105).
Definition buf1_18106 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18106).
Definition buf2_18107 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18107).
Definition buf3_18108 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18108).
Definition _TRAILB_18109 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18109).
Definition _RATE8_18110 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18110).
Definition offset_18111 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18111).
Definition _LEN_18112 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18112).
Definition ITERS_18113 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18113).
Definition i_18114 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18114).

(* Signature *)
Definition tyin_A1____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 1
    ; aarr U8 1
    ; aarr U8 1
    ; aarr U8 1
    ; aint
    ; aint ].
Definition args_A1____absorb_avx2x4 : seq var_i :=
  [:: st_18103.(gv)
    ; AT_18104.(gv)
    ; buf0_18105.(gv)
    ; buf1_18106.(gv)
    ; buf2_18107.(gv)
    ; buf3_18108.(gv)
    ; _TRAILB_18109.(gv)
    ; _RATE8_18110.(gv) ].
Definition tyout_A1____absorb_avx2x4 : seq atype := [:: aarr U256 25; aint ].
Definition res_A1____absorb_avx2x4 : seq var_i :=
  [:: st_18103.(gv); AT_18104.(gv) ].

(* Body *)
Definition body_A1____absorb_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_18111.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_18112.(gv)) AT_none (aint) (Pconst (1)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_18104) (Pvar _LEN_18112)) (Pvar _RATE8_18110))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_18103.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_18111.(gv) ] A1____addstate_avx2x4 [:: Pvar st_18103
                                                                    ; Pvar AT_18104
                                                                    ; Pvar buf0_18105
                                                                    ; Pvar buf1_18106
                                                                    ; Pvar buf2_18107
                                                                    ; Pvar buf3_18108
                                                                    ; Pvar offset_18111
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_18110) (Pvar AT_18104)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_18112.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_18112) (Papp2 (Osub (Op_int)) (Pvar _RATE8_18110) (Pvar AT_18104))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_18104.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_18103.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_18103 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_18113.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18112) (Pvar _RATE8_18110)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_18114.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_18114) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_18113)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_18103.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_18111.(gv) ] A1____addstate_avx2x4 [:: Pvar st_18103
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_18105
                                                                    ; Pvar buf1_18106
                                                                    ; Pvar buf2_18107
                                                                    ; Pvar buf3_18108
                                                                    ; Pvar offset_18111
                                                                    ; Pvar _RATE8_18110
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_18103.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_18103 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_18114.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_18114) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_18112.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18112) (Pvar _RATE8_18110))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_18103.(gv)
                                    ; Lvar AT_18104.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1____addstate_avx2x4 [:: Pvar st_18103
                                                                    ; Pvar AT_18104
                                                                    ; Pvar buf0_18105
                                                                    ; Pvar buf1_18106
                                                                    ; Pvar buf2_18107
                                                                    ; Pvar buf3_18108
                                                                    ; Pvar offset_18111
                                                                    ; Pvar _LEN_18112
                                                                    ; Pvar _TRAILB_18109 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_18109) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_18103.(gv) ] __addratebit_avx2x4 [:: Pvar st_18103
                                                                    ; Pvar _RATE8_18110 ]) ]
                              [::]) ].

Definition fd_A1____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____absorb_avx2x4;
    f_params := args_A1____absorb_avx2x4;
    f_body := body_A1____absorb_avx2x4;
    f_tyout := tyout_A1____absorb_avx2x4;
    f_res := res_A1____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
