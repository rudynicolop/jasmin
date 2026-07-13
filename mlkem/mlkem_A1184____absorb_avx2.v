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

(* A1184____absorb_avx2 *)
(* Local variables *)
Definition st_71 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 16063).
Definition AT_70 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16064).
Definition buf_105 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16065).
Definition _TRAILB_38 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16066).
Definition _RATE8_31 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16067).
Definition offset_103 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16068).
Definition _LEN_64 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16069).
Definition ITERS_31 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16070).
Definition i_43 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16071).

(* Signature *)
Definition tyin_A1184____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1184; aint; aint ].
Definition args_A1184____absorb_avx2 : seq var_i :=
  [:: st_71.(gv); AT_70.(gv); buf_105.(gv); _TRAILB_38.(gv); _RATE8_31.(gv) ].
Definition tyout_A1184____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A1184____absorb_avx2 : seq var_i :=
  [:: st_71.(gv); AT_70.(gv) ].

(* Body *)
Definition body_A1184____absorb_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_103.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_64.(gv)) AT_none (aint) (Pconst (1184)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_70) (Pvar _LEN_64)) (Pvar _RATE8_31))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_71.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_103.(gv) ] A1184____addstate_avx2 [:: Pvar st_71
                                                                    ; Pvar AT_70
                                                                    ; Pvar buf_105
                                                                    ; Pvar offset_103
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_31) (Pvar AT_70)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_64.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_64) (Papp2 (Osub (Op_int)) (Pvar _RATE8_31) (Pvar AT_70))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_70.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_71.(gv) ] _keccakf1600_avx2 [:: Pvar st_71 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_31.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_64) (Pvar _RATE8_31)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_43.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_43) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_31)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_71.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_103.(gv) ] A1184____addstate_avx2 [:: Pvar st_71
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_105
                                                                    ; Pvar offset_103
                                                                    ; Pvar _RATE8_31
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_71.(gv) ] _keccakf1600_avx2 [:: Pvar st_71 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_43.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_43) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_64.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_64) (Pvar _RATE8_31))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_71.(gv)
                                    ; Lvar AT_70.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1184____addstate_avx2 [:: Pvar st_71
                                                                    ; Pvar AT_70
                                                                    ; Pvar buf_105
                                                                    ; Pvar offset_103
                                                                    ; Pvar _LEN_64
                                                                    ; Pvar _TRAILB_38 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_38) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_71.(gv) ] __addratebit_avx2 [:: Pvar st_71
                                                                    ; Pvar _RATE8_31 ]) ]
                              [::]) ].

Definition fd_A1184____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____absorb_avx2;
    f_params := args_A1184____absorb_avx2;
    f_body := body_A1184____absorb_avx2;
    f_tyout := tyout_A1184____absorb_avx2;
    f_res := res_A1184____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
