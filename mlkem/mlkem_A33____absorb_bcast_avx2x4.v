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

(* A33____absorb_bcast_avx2x4 *)
(* Local variables *)
Definition st_51 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 17007).
Definition AT_46 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17008).
Definition buf_69 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 17009).
Definition _TRAILB_26 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17010).
Definition _RATE8_21 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17011).
Definition offset_62 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17012).
Definition _LEN_44 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17013).
Definition ITERS_21 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17014).
Definition i_31 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17015).

(* Signature *)
Definition tyin_A33____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 33; aint; aint ].
Definition args_A33____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_51.(gv); AT_46.(gv); buf_69.(gv); _TRAILB_26.(gv); _RATE8_21.(gv) ].
Definition tyout_A33____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A33____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_51.(gv); AT_46.(gv) ].

(* Body *)
Definition body_A33____absorb_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_62.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_44.(gv)) AT_none (aint) (Pconst (33)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_46) (Pvar _LEN_44)) (Pvar _RATE8_21))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_51.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_62.(gv) ] A33____addstate_bcast_avx2x4 [:: Pvar st_51
                                                                    ; Pvar AT_46
                                                                    ; Pvar buf_69
                                                                    ; Pvar offset_62
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_21) (Pvar AT_46)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_44.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_44) (Papp2 (Osub (Op_int)) (Pvar _RATE8_21) (Pvar AT_46))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_46.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_51.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_51 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_21.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_44) (Pvar _RATE8_21)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_31.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_31) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_21)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_51.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_62.(gv) ] A33____addstate_bcast_avx2x4 [:: Pvar st_51
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_69
                                                                    ; Pvar offset_62
                                                                    ; Pvar _RATE8_21
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_51.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_51 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_31.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_31) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_44.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_44) (Pvar _RATE8_21))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_51.(gv)
                                    ; Lvar AT_46.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A33____addstate_bcast_avx2x4 [:: Pvar st_51
                                                                    ; Pvar AT_46
                                                                    ; Pvar buf_69
                                                                    ; Pvar offset_62
                                                                    ; Pvar _LEN_44
                                                                    ; Pvar _TRAILB_26 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_26) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_51.(gv) ] __addratebit_avx2x4 [:: Pvar st_51
                                                                    ; Pvar _RATE8_21 ]) ]
                              [::]) ].

Definition fd_A33____absorb_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____absorb_bcast_avx2x4;
    f_params := args_A33____absorb_bcast_avx2x4;
    f_body := body_A33____absorb_bcast_avx2x4;
    f_tyout := tyout_A33____absorb_bcast_avx2x4;
    f_res := res_A33____absorb_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
