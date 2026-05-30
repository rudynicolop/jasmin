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

(* A1120____absorb_bcast_avx2x4 *)
(* Local variables *)
Definition st_95 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 15232).
Definition AT_92 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15233).
Definition buf_137 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15234).
Definition _TRAILB_52 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15235).
Definition _RATE8_43 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15236).
Definition offset_141 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15237).
Definition _LEN_88 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15238).
Definition ITERS_43 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15239).
Definition i_57 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15240).

(* Signature *)
Definition tyin_A1120____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 1120; aint; aint ].
Definition args_A1120____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_95.(gv); AT_92.(gv); buf_137.(gv); _TRAILB_52.(gv); _RATE8_43.(gv) ].
Definition tyout_A1120____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A1120____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_95.(gv); AT_92.(gv) ].

(* Body *)
Definition body_A1120____absorb_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_141.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_88.(gv)) AT_none (aint) (Pconst (1120)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_92) (Pvar _LEN_88)) (Pvar _RATE8_43))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_95.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_141.(gv) ] A1120____addstate_bcast_avx2x4 [:: Pvar st_95
                                                                    ; Pvar AT_92
                                                                    ; Pvar buf_137
                                                                    ; Pvar offset_141
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_43) (Pvar AT_92)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_88.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_88) (Papp2 (Osub (Op_int)) (Pvar _RATE8_43) (Pvar AT_92))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_92.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_95.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_95 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_43.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_88) (Pvar _RATE8_43)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_57.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_57) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_43)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_95.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_141.(gv) ] A1120____addstate_bcast_avx2x4 [:: Pvar st_95
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_137
                                                                    ; Pvar offset_141
                                                                    ; Pvar _RATE8_43
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_95.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_95 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_57.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_57) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_88.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_88) (Pvar _RATE8_43))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_95.(gv)
                                    ; Lvar AT_92.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1120____addstate_bcast_avx2x4 [:: Pvar st_95
                                                                    ; Pvar AT_92
                                                                    ; Pvar buf_137
                                                                    ; Pvar offset_141
                                                                    ; Pvar _LEN_88
                                                                    ; Pvar _TRAILB_52 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_52) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_95.(gv) ] __addratebit_avx2x4 [:: Pvar st_95
                                                                    ; Pvar _RATE8_43 ]) ]
                              [::]) ].

Definition fd_A1120____absorb_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____absorb_bcast_avx2x4;
    f_params := args_A1120____absorb_bcast_avx2x4;
    f_body := body_A1120____absorb_bcast_avx2x4;
    f_tyout := tyout_A1120____absorb_bcast_avx2x4;
    f_res := res_A1120____absorb_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
