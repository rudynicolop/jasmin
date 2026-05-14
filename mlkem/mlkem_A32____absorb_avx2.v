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

(* A32____absorb_avx2 *)
(* Local variables *)
Definition st_17456 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 17456).
Definition AT_17457 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17457).
Definition buf_17458 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17458).
Definition _TRAILB_17459 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17459).
Definition _RATE8_17460 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17460).
Definition offset_17461 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17461).
Definition _LEN_17462 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17462).
Definition ITERS_17463 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17463).
Definition i_17464 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17464).

(* Signature *)
Definition tyin_A32____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 32; aint; aint ].
Definition args_A32____absorb_avx2 : seq var_i :=
  [:: st_17456.(gv)
    ; AT_17457.(gv)
    ; buf_17458.(gv)
    ; _TRAILB_17459.(gv)
    ; _RATE8_17460.(gv) ].
Definition tyout_A32____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A32____absorb_avx2 : seq var_i :=
  [:: st_17456.(gv); AT_17457.(gv) ].

(* Body *)
Definition body_A32____absorb_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_17461.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_17462.(gv)) AT_none (aint) (Pconst (32)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_17457) (Pvar _LEN_17462)) (Pvar _RATE8_17460))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_17456.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_17461.(gv) ] A32____addstate_avx2 [:: Pvar st_17456
                                                                    ; Pvar AT_17457
                                                                    ; Pvar buf_17458
                                                                    ; Pvar offset_17461
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_17460) (Pvar AT_17457)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_17462.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_17462) (Papp2 (Osub (Op_int)) (Pvar _RATE8_17460) (Pvar AT_17457))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_17457.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_17456.(gv) ] _keccakf1600_avx2 [:: Pvar st_17456 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_17463.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17462) (Pvar _RATE8_17460)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_17464.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_17464) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_17463)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_17456.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_17461.(gv) ] A32____addstate_avx2 [:: Pvar st_17456
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_17458
                                                                    ; Pvar offset_17461
                                                                    ; Pvar _RATE8_17460
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_17456.(gv) ] _keccakf1600_avx2 [:: Pvar st_17456 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_17464.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_17464) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_17462.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17462) (Pvar _RATE8_17460))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_17456.(gv)
                                    ; Lvar AT_17457.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A32____addstate_avx2 [:: Pvar st_17456
                                                                    ; Pvar AT_17457
                                                                    ; Pvar buf_17458
                                                                    ; Pvar offset_17461
                                                                    ; Pvar _LEN_17462
                                                                    ; Pvar _TRAILB_17459 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_17459) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_17456.(gv) ] __addratebit_avx2 [:: Pvar st_17456
                                                                    ; Pvar _RATE8_17460 ]) ]
                              [::]) ].

Definition fd_A32____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____absorb_avx2;
    f_params := args_A32____absorb_avx2;
    f_body := body_A32____absorb_avx2;
    f_tyout := tyout_A32____absorb_avx2;
    f_res := res_A32____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
