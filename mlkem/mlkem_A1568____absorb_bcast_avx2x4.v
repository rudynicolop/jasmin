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

(* A1568____absorb_bcast_avx2x4 *)
(* Local variables *)
Definition st_85 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 15614).
Definition AT_82 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15615).
Definition buf_123 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15616).
Definition _TRAILB_46 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15617).
Definition _RATE8_38 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15618).
Definition offset_124 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15619).
Definition _LEN_78 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15620).
Definition ITERS_38 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15621).
Definition i_51 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15622).

(* Signature *)
Definition tyin_A1568____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 1568; aint; aint ].
Definition args_A1568____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_85.(gv); AT_82.(gv); buf_123.(gv); _TRAILB_46.(gv); _RATE8_38.(gv) ].
Definition tyout_A1568____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A1568____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_85.(gv); AT_82.(gv) ].

(* Body *)
Definition body_A1568____absorb_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_124.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_78.(gv)) AT_none (aint) (Pconst (1568)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_82) (Pvar _LEN_78)) (Pvar _RATE8_38))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_85.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_124.(gv) ] A1568____addstate_bcast_avx2x4 [:: Pvar st_85
                                                                    ; Pvar AT_82
                                                                    ; Pvar buf_123
                                                                    ; Pvar offset_124
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_38) (Pvar AT_82)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_78.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_78) (Papp2 (Osub (Op_int)) (Pvar _RATE8_38) (Pvar AT_82))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_82.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_85.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_85 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_38.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_78) (Pvar _RATE8_38)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_51.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_51) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_38)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_85.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_124.(gv) ] A1568____addstate_bcast_avx2x4 [:: Pvar st_85
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_123
                                                                    ; Pvar offset_124
                                                                    ; Pvar _RATE8_38
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_85.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_85 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_51.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_51) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_78.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_78) (Pvar _RATE8_38))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_85.(gv)
                                    ; Lvar AT_82.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1568____addstate_bcast_avx2x4 [:: Pvar st_85
                                                                    ; Pvar AT_82
                                                                    ; Pvar buf_123
                                                                    ; Pvar offset_124
                                                                    ; Pvar _LEN_78
                                                                    ; Pvar _TRAILB_46 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_46) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_85.(gv) ] __addratebit_avx2x4 [:: Pvar st_85
                                                                    ; Pvar _RATE8_38 ]) ]
                              [::]) ].

Definition fd_A1568____absorb_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____absorb_bcast_avx2x4;
    f_params := args_A1568____absorb_bcast_avx2x4;
    f_body := body_A1568____absorb_bcast_avx2x4;
    f_tyout := tyout_A1568____absorb_bcast_avx2x4;
    f_res := res_A1568____absorb_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
