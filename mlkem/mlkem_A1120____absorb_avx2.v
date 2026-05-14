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

(* A1120____absorb_avx2 *)
(* Local variables *)
Definition st_15299 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 15299).
Definition AT_15300 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15300).
Definition buf_15301 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15301).
Definition _TRAILB_15302 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15302).
Definition _RATE8_15303 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15303).
Definition offset_15304 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15304).
Definition _LEN_15305 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15305).
Definition ITERS_15306 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15306).
Definition i_15307 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15307).

(* Signature *)
Definition tyin_A1120____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1120; aint; aint ].
Definition args_A1120____absorb_avx2 : seq var_i :=
  [:: st_15299.(gv)
    ; AT_15300.(gv)
    ; buf_15301.(gv)
    ; _TRAILB_15302.(gv)
    ; _RATE8_15303.(gv) ].
Definition tyout_A1120____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A1120____absorb_avx2 : seq var_i :=
  [:: st_15299.(gv); AT_15300.(gv) ].

(* Body *)
Definition body_A1120____absorb_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_15304.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15305.(gv)) AT_none (aint) (Pconst (1120)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_15300) (Pvar _LEN_15305)) (Pvar _RATE8_15303))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_15299.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_15304.(gv) ] A1120____addstate_avx2 [:: Pvar st_15299
                                                                    ; Pvar AT_15300
                                                                    ; Pvar buf_15301
                                                                    ; Pvar offset_15304
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_15303) (Pvar AT_15300)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15305.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_15305) (Papp2 (Osub (Op_int)) (Pvar _RATE8_15303) (Pvar AT_15300))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_15300.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_15299.(gv) ] _keccakf1600_avx2 [:: Pvar st_15299 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_15306.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15305) (Pvar _RATE8_15303)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_15307.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15307) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_15306)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_15299.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_15304.(gv) ] A1120____addstate_avx2 [:: Pvar st_15299
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_15301
                                                                    ; Pvar offset_15304
                                                                    ; Pvar _RATE8_15303
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_15299.(gv) ] _keccakf1600_avx2 [:: Pvar st_15299 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_15307.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15307) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15305.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15305) (Pvar _RATE8_15303))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_15299.(gv)
                                    ; Lvar AT_15300.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1120____addstate_avx2 [:: Pvar st_15299
                                                                    ; Pvar AT_15300
                                                                    ; Pvar buf_15301
                                                                    ; Pvar offset_15304
                                                                    ; Pvar _LEN_15305
                                                                    ; Pvar _TRAILB_15302 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_15302) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_15299.(gv) ] __addratebit_avx2 [:: Pvar st_15299
                                                                    ; Pvar _RATE8_15303 ]) ]
                              [::]) ].

Definition fd_A1120____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____absorb_avx2;
    f_params := args_A1120____absorb_avx2;
    f_body := body_A1120____absorb_avx2;
    f_tyout := tyout_A1120____absorb_avx2;
    f_res := res_A1120____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
