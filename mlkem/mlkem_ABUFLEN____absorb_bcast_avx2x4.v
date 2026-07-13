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

(* ABUFLEN____absorb_bcast_avx2x4 *)
(* Local variables *)
Definition st_115 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14468).
Definition AT_112 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14469).
Definition buf_165 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14470).
Definition _TRAILB_64 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14471).
Definition _RATE8_53 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14472).
Definition offset_175 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14473).
Definition _LEN_108 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14474).
Definition ITERS_53 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14475).
Definition i_69 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14476).

(* Signature *)
Definition tyin_ABUFLEN____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 536; aint; aint ].
Definition args_ABUFLEN____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_115.(gv)
    ; AT_112.(gv)
    ; buf_165.(gv)
    ; _TRAILB_64.(gv)
    ; _RATE8_53.(gv) ].
Definition tyout_ABUFLEN____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_ABUFLEN____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_115.(gv); AT_112.(gv) ].

(* Body *)
Definition body_ABUFLEN____absorb_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_175.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_108.(gv)) AT_none (aint) (Pconst (536)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_112) (Pvar _LEN_108)) (Pvar _RATE8_53))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_115.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_175.(gv) ] ABUFLEN____addstate_bcast_avx2x4 [:: Pvar st_115
                                                                    ; Pvar AT_112
                                                                    ; Pvar buf_165
                                                                    ; Pvar offset_175
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_53) (Pvar AT_112)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_108.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_108) (Papp2 (Osub (Op_int)) (Pvar _RATE8_53) (Pvar AT_112))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_112.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_115.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_115 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_53.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_108) (Pvar _RATE8_53)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_69.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_69) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_53)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_115.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_175.(gv) ] ABUFLEN____addstate_bcast_avx2x4 [:: Pvar st_115
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_165
                                                                    ; Pvar offset_175
                                                                    ; Pvar _RATE8_53
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_115.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_115 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_69.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_69) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_108.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_108) (Pvar _RATE8_53))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_115.(gv)
                                    ; Lvar AT_112.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] ABUFLEN____addstate_bcast_avx2x4 [:: Pvar st_115
                                                                    ; Pvar AT_112
                                                                    ; Pvar buf_165
                                                                    ; Pvar offset_175
                                                                    ; Pvar _LEN_108
                                                                    ; Pvar _TRAILB_64 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_64) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_115.(gv) ] __addratebit_avx2x4 [:: Pvar st_115
                                                                    ; Pvar _RATE8_53 ]) ]
                              [::]) ].

Definition fd_ABUFLEN____absorb_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____absorb_bcast_avx2x4;
    f_params := args_ABUFLEN____absorb_bcast_avx2x4;
    f_body := body_ABUFLEN____absorb_bcast_avx2x4;
    f_tyout := tyout_ABUFLEN____absorb_bcast_avx2x4;
    f_res := res_ABUFLEN____absorb_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
