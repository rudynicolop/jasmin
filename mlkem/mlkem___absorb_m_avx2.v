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

(* __absorb_m_avx2 *)
(* Local variables *)
Definition st_5 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 18779).
Definition AT_4 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18780).
Definition buf_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18781).
Definition _LEN_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18782).
Definition _TRAILB_0 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18783).
Definition _RATE8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18784).
Definition ITERS : gvar := mk_rocq_gvar Slocal (aint) (mkident 18785).
Definition i_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18786).

(* Signature *)
Definition tyin___absorb_m_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64; aint; aint; aint ].
Definition args___absorb_m_avx2 : seq var_i :=
  [:: st_5.(gv)
    ; AT_4.(gv)
    ; buf_9.(gv)
    ; _LEN_0.(gv)
    ; _TRAILB_0.(gv)
    ; _RATE8.(gv) ].
Definition tyout___absorb_m_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res___absorb_m_avx2 : seq var_i := [:: st_5.(gv); AT_4.(gv) ].

(* Body *)
Definition body___absorb_m_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_4) (Pvar _LEN_0)) (Pvar _RATE8))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_5.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar buf_9.(gv) ] __addstate_m_avx2 [:: Pvar st_5
                                                                    ; Pvar AT_4
                                                                    ; Pvar buf_9
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8) (Pvar AT_4)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_0.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_0) (Papp2 (Osub (Op_int)) (Pvar _RATE8) (Pvar AT_4))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_4.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_5.(gv) ] _keccakf1600_avx2 [:: Pvar st_5 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_0) (Pvar _RATE8)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_2.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_5.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar buf_9.(gv) ] __addstate_m_avx2 [:: Pvar st_5
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_9
                                                                    ; Pvar _RATE8
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_5.(gv) ] _keccakf1600_avx2 [:: Pvar st_5 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_2.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_0.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_0) (Pvar _RATE8))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_5.(gv)
                                    ; Lvar AT_4.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] __addstate_m_avx2 [:: Pvar st_5
                                                                    ; Pvar AT_4
                                                                    ; Pvar buf_9
                                                                    ; Pvar _LEN_0
                                                                    ; Pvar _TRAILB_0 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_0) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_5.(gv) ] __addratebit_avx2 [:: Pvar st_5
                                                                    ; Pvar _RATE8 ]) ]
                              [::]) ].

Definition fd___absorb_m_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___absorb_m_avx2;
    f_params := args___absorb_m_avx2;
    f_body := body___absorb_m_avx2;
    f_tyout := tyout___absorb_m_avx2;
    f_res := res___absorb_m_avx2;
    f_extra := tt;
  |}.

End IDO.
