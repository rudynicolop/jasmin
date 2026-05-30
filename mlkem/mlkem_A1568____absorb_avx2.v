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

(* A1568____absorb_avx2 *)
(* Local variables *)
Definition st_81 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 15681).
Definition AT_80 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15682).
Definition buf_119 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15683).
Definition _TRAILB_44 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15684).
Definition _RATE8_36 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15685).
Definition offset_120 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15686).
Definition _LEN_74 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15687).
Definition ITERS_36 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15688).
Definition i_49 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15689).

(* Signature *)
Definition tyin_A1568____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1568; aint; aint ].
Definition args_A1568____absorb_avx2 : seq var_i :=
  [:: st_81.(gv); AT_80.(gv); buf_119.(gv); _TRAILB_44.(gv); _RATE8_36.(gv) ].
Definition tyout_A1568____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A1568____absorb_avx2 : seq var_i :=
  [:: st_81.(gv); AT_80.(gv) ].

(* Body *)
Definition body_A1568____absorb_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_120.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_74.(gv)) AT_none (aint) (Pconst (1568)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_80) (Pvar _LEN_74)) (Pvar _RATE8_36))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_81.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_120.(gv) ] A1568____addstate_avx2 [:: Pvar st_81
                                                                    ; Pvar AT_80
                                                                    ; Pvar buf_119
                                                                    ; Pvar offset_120
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_36) (Pvar AT_80)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_74.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_74) (Papp2 (Osub (Op_int)) (Pvar _RATE8_36) (Pvar AT_80))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_80.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_81.(gv) ] _keccakf1600_avx2 [:: Pvar st_81 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_36.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_74) (Pvar _RATE8_36)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_49.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_49) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_36)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_81.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_120.(gv) ] A1568____addstate_avx2 [:: Pvar st_81
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_119
                                                                    ; Pvar offset_120
                                                                    ; Pvar _RATE8_36
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_81.(gv) ] _keccakf1600_avx2 [:: Pvar st_81 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_49.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_49) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_74.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_74) (Pvar _RATE8_36))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_81.(gv)
                                    ; Lvar AT_80.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1568____addstate_avx2 [:: Pvar st_81
                                                                    ; Pvar AT_80
                                                                    ; Pvar buf_119
                                                                    ; Pvar offset_120
                                                                    ; Pvar _LEN_74
                                                                    ; Pvar _TRAILB_44 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_44) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_81.(gv) ] __addratebit_avx2 [:: Pvar st_81
                                                                    ; Pvar _RATE8_36 ]) ]
                              [::]) ].

Definition fd_A1568____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____absorb_avx2;
    f_params := args_A1568____absorb_avx2;
    f_body := body_A1568____absorb_avx2;
    f_tyout := tyout_A1568____absorb_avx2;
    f_res := res_A1568____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
