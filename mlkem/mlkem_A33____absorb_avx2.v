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

(* A33____absorb_avx2 *)
(* Local variables *)
Definition st_47 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 17074).
Definition AT_44 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17075).
Definition buf_65 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 17076).
Definition _TRAILB_24 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17077).
Definition _RATE8_19 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17078).
Definition offset_58 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17079).
Definition _LEN_40 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17080).
Definition ITERS_19 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17081).
Definition i_29 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17082).

(* Signature *)
Definition tyin_A33____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 33; aint; aint ].
Definition args_A33____absorb_avx2 : seq var_i :=
  [:: st_47.(gv); AT_44.(gv); buf_65.(gv); _TRAILB_24.(gv); _RATE8_19.(gv) ].
Definition tyout_A33____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A33____absorb_avx2 : seq var_i := [:: st_47.(gv); AT_44.(gv) ].

(* Body *)
Definition body_A33____absorb_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_58.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_40.(gv)) AT_none (aint) (Pconst (33)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_44) (Pvar _LEN_40)) (Pvar _RATE8_19))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_47.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_58.(gv) ] A33____addstate_avx2 [:: Pvar st_47
                                                                    ; Pvar AT_44
                                                                    ; Pvar buf_65
                                                                    ; Pvar offset_58
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_19) (Pvar AT_44)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_40.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_40) (Papp2 (Osub (Op_int)) (Pvar _RATE8_19) (Pvar AT_44))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_44.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_47.(gv) ] _keccakf1600_avx2 [:: Pvar st_47 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_19.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_40) (Pvar _RATE8_19)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_29.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_29) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_19)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_47.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_58.(gv) ] A33____addstate_avx2 [:: Pvar st_47
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_65
                                                                    ; Pvar offset_58
                                                                    ; Pvar _RATE8_19
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_47.(gv) ] _keccakf1600_avx2 [:: Pvar st_47 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_29.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_29) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_40.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_40) (Pvar _RATE8_19))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_47.(gv)
                                    ; Lvar AT_44.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A33____addstate_avx2 [:: Pvar st_47
                                                                    ; Pvar AT_44
                                                                    ; Pvar buf_65
                                                                    ; Pvar offset_58
                                                                    ; Pvar _LEN_40
                                                                    ; Pvar _TRAILB_24 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_24) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_47.(gv) ] __addratebit_avx2 [:: Pvar st_47
                                                                    ; Pvar _RATE8_19 ]) ]
                              [::]) ].

Definition fd_A33____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____absorb_avx2;
    f_params := args_A33____absorb_avx2;
    f_body := body_A33____absorb_avx2;
    f_tyout := tyout_A33____absorb_avx2;
    f_res := res_A33____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
