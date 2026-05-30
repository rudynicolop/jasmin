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
Definition st_105 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14850).
Definition AT_102 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14851).
Definition buf_151 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14852).
Definition _TRAILB_58 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14853).
Definition _RATE8_48 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14854).
Definition offset_158 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14855).
Definition _LEN_98 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14856).
Definition ITERS_48 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14857).
Definition i_63 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14858).

(* Signature *)
Definition tyin_A1600____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 1600; aint; aint ].
Definition args_A1600____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_105.(gv)
    ; AT_102.(gv)
    ; buf_151.(gv)
    ; _TRAILB_58.(gv)
    ; _RATE8_48.(gv) ].
Definition tyout_A1600____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A1600____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_105.(gv); AT_102.(gv) ].

(* Body *)
Definition body_A1600____absorb_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_158.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_98.(gv)) AT_none (aint) (Pconst (1600)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_102) (Pvar _LEN_98)) (Pvar _RATE8_48))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_105.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_158.(gv) ] A1600____addstate_bcast_avx2x4 [:: Pvar st_105
                                                                    ; Pvar AT_102
                                                                    ; Pvar buf_151
                                                                    ; Pvar offset_158
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_48) (Pvar AT_102)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_98.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_98) (Papp2 (Osub (Op_int)) (Pvar _RATE8_48) (Pvar AT_102))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_102.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_105.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_105 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_48.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_98) (Pvar _RATE8_48)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_63.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_63) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_48)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_105.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_158.(gv) ] A1600____addstate_bcast_avx2x4 [:: Pvar st_105
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_151
                                                                    ; Pvar offset_158
                                                                    ; Pvar _RATE8_48
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_105.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_105 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_63.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_63) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_98.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_98) (Pvar _RATE8_48))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_105.(gv)
                                    ; Lvar AT_102.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1600____addstate_bcast_avx2x4 [:: Pvar st_105
                                                                    ; Pvar AT_102
                                                                    ; Pvar buf_151
                                                                    ; Pvar offset_158
                                                                    ; Pvar _LEN_98
                                                                    ; Pvar _TRAILB_58 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_58) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_105.(gv) ] __addratebit_avx2x4 [:: Pvar st_105
                                                                    ; Pvar _RATE8_48 ]) ]
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
