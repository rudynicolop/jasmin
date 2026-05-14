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
Definition st_15681 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 15681).
Definition AT_15682 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15682).
Definition buf_15683 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15683).
Definition _TRAILB_15684 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15684).
Definition _RATE8_15685 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15685).
Definition offset_15686 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15686).
Definition _LEN_15687 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15687).
Definition ITERS_15688 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15688).
Definition i_15689 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15689).

(* Signature *)
Definition tyin_A1568____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1568; aint; aint ].
Definition args_A1568____absorb_avx2 : seq var_i :=
  [:: st_15681.(gv)
    ; AT_15682.(gv)
    ; buf_15683.(gv)
    ; _TRAILB_15684.(gv)
    ; _RATE8_15685.(gv) ].
Definition tyout_A1568____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A1568____absorb_avx2 : seq var_i :=
  [:: st_15681.(gv); AT_15682.(gv) ].

(* Body *)
Definition body_A1568____absorb_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_15686.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15687.(gv)) AT_none (aint) (Pconst (1568)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_15682) (Pvar _LEN_15687)) (Pvar _RATE8_15685))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_15681.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_15686.(gv) ] A1568____addstate_avx2 [:: Pvar st_15681
                                                                    ; Pvar AT_15682
                                                                    ; Pvar buf_15683
                                                                    ; Pvar offset_15686
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_15685) (Pvar AT_15682)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15687.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_15687) (Papp2 (Osub (Op_int)) (Pvar _RATE8_15685) (Pvar AT_15682))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_15682.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_15681.(gv) ] _keccakf1600_avx2 [:: Pvar st_15681 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_15688.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15687) (Pvar _RATE8_15685)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_15689.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15689) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_15688)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_15681.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_15686.(gv) ] A1568____addstate_avx2 [:: Pvar st_15681
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_15683
                                                                    ; Pvar offset_15686
                                                                    ; Pvar _RATE8_15685
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_15681.(gv) ] _keccakf1600_avx2 [:: Pvar st_15681 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_15689.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15689) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15687.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15687) (Pvar _RATE8_15685))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_15681.(gv)
                                    ; Lvar AT_15682.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1568____addstate_avx2 [:: Pvar st_15681
                                                                    ; Pvar AT_15682
                                                                    ; Pvar buf_15683
                                                                    ; Pvar offset_15686
                                                                    ; Pvar _LEN_15687
                                                                    ; Pvar _TRAILB_15684 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_15684) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_15681.(gv) ] __addratebit_avx2 [:: Pvar st_15681
                                                                    ; Pvar _RATE8_15685 ]) ]
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
