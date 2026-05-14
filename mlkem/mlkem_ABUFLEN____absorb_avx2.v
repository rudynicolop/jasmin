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

(* ABUFLEN____absorb_avx2 *)
(* Local variables *)
Definition st_14535 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 14535).
Definition AT_14536 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14536).
Definition buf_14537 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14537).
Definition _TRAILB_14538 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14538).
Definition _RATE8_14539 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14539).
Definition offset_14540 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14540).
Definition _LEN_14541 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14541).
Definition ITERS_14542 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14542).
Definition i_14543 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14543).

(* Signature *)
Definition tyin_ABUFLEN____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 536; aint; aint ].
Definition args_ABUFLEN____absorb_avx2 : seq var_i :=
  [:: st_14535.(gv)
    ; AT_14536.(gv)
    ; buf_14537.(gv)
    ; _TRAILB_14538.(gv)
    ; _RATE8_14539.(gv) ].
Definition tyout_ABUFLEN____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint ].
Definition res_ABUFLEN____absorb_avx2 : seq var_i :=
  [:: st_14535.(gv); AT_14536.(gv) ].

(* Body *)
Definition body_ABUFLEN____absorb_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_14540.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14541.(gv)) AT_none (aint) (Pconst (536)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_14536) (Pvar _LEN_14541)) (Pvar _RATE8_14539))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_14535.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_14540.(gv) ] ABUFLEN____addstate_avx2 [:: Pvar st_14535
                                                                    ; Pvar AT_14536
                                                                    ; Pvar buf_14537
                                                                    ; Pvar offset_14540
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_14539) (Pvar AT_14536)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14541.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_14541) (Papp2 (Osub (Op_int)) (Pvar _RATE8_14539) (Pvar AT_14536))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_14536.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_14535.(gv) ] _keccakf1600_avx2 [:: Pvar st_14535 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_14542.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14541) (Pvar _RATE8_14539)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_14543.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_14543) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_14542)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_14535.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_14540.(gv) ] ABUFLEN____addstate_avx2 [:: Pvar st_14535
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_14537
                                                                    ; Pvar offset_14540
                                                                    ; Pvar _RATE8_14539
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_14535.(gv) ] _keccakf1600_avx2 [:: Pvar st_14535 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_14543.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_14543) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_14541.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14541) (Pvar _RATE8_14539))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_14535.(gv)
                                    ; Lvar AT_14536.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] ABUFLEN____addstate_avx2 [:: Pvar st_14535
                                                                    ; Pvar AT_14536
                                                                    ; Pvar buf_14537
                                                                    ; Pvar offset_14540
                                                                    ; Pvar _LEN_14541
                                                                    ; Pvar _TRAILB_14538 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_14538) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_14535.(gv) ] __addratebit_avx2 [:: Pvar st_14535
                                                                    ; Pvar _RATE8_14539 ]) ]
                              [::]) ].

Definition fd_ABUFLEN____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____absorb_avx2;
    f_params := args_ABUFLEN____absorb_avx2;
    f_body := body_ABUFLEN____absorb_avx2;
    f_tyout := tyout_ABUFLEN____absorb_avx2;
    f_res := res_ABUFLEN____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
