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

(* A1600____absorb_bcast_avx2x4 *)
(* Local variables *)
Definition st_14850 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14850).
Definition AT_14851 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14851).
Definition buf_14852 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14852).
Definition _TRAILB_14853 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14853).
Definition _RATE8_14854 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14854).
Definition offset_14855 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14855).
Definition _LEN_14856 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14856).
Definition ITERS_14857 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14857).
Definition i_14858 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14858).

(* Signature *)
Definition tyin_A1600____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 1600; aint; aint ].
Definition args_A1600____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_14850.(gv)
    ; AT_14851.(gv)
    ; buf_14852.(gv)
    ; _TRAILB_14853.(gv)
    ; _RATE8_14854.(gv) ].
Definition tyout_A1600____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A1600____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_14850.(gv); AT_14851.(gv) ].

(* Body *)
Definition body_A1600____absorb_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_14855.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14856.(gv)) AT_none (aint) (Pconst (1600)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_14851) (Pvar _LEN_14856)) (Pvar _RATE8_14854))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_14850.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_14855.(gv) ] A1600____addstate_bcast_avx2x4 [:: Pvar st_14850
                                                                    ; Pvar AT_14851
                                                                    ; Pvar buf_14852
                                                                    ; Pvar offset_14855
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_14854) (Pvar AT_14851)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14856.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_14856) (Papp2 (Osub (Op_int)) (Pvar _RATE8_14854) (Pvar AT_14851))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_14851.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_14850.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_14850 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_14857.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14856) (Pvar _RATE8_14854)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_14858.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_14858) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_14857)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_14850.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_14855.(gv) ] A1600____addstate_bcast_avx2x4 [:: Pvar st_14850
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_14852
                                                                    ; Pvar offset_14855
                                                                    ; Pvar _RATE8_14854
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_14850.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_14850 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_14858.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_14858) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14856.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14856) (Pvar _RATE8_14854))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_14850.(gv)
                                    ; Lvar AT_14851.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1600____addstate_bcast_avx2x4 [:: Pvar st_14850
                                                                    ; Pvar AT_14851
                                                                    ; Pvar buf_14852
                                                                    ; Pvar offset_14855
                                                                    ; Pvar _LEN_14856
                                                                    ; Pvar _TRAILB_14853 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_14853) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_14850.(gv) ] __addratebit_avx2x4 [:: Pvar st_14850
                                                                    ; Pvar _RATE8_14854 ]) ]
                              [::]) ].

Definition fd_A1600____absorb_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____absorb_bcast_avx2x4;
    f_params := args_A1600____absorb_bcast_avx2x4;
    f_body := body_A1600____absorb_bcast_avx2x4;
    f_tyout := tyout_A1600____absorb_bcast_avx2x4;
    f_res := res_A1600____absorb_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
