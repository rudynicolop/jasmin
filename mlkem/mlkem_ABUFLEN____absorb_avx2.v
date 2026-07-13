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
Definition st_111 : gvar := mk_rocq_gvar Slocal (aarr U256 7) (mkident 14535).
Definition AT_110 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14536).
Definition buf_161 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14537).
Definition _TRAILB_62 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14538).
Definition _RATE8_51 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14539).
Definition offset_171 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14540).
Definition _LEN_104 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14541).
Definition ITERS_51 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14542).
Definition i_67 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14543).

(* Signature *)
Definition tyin_ABUFLEN____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 536; aint; aint ].
Definition args_ABUFLEN____absorb_avx2 : seq var_i :=
  [:: st_111.(gv)
    ; AT_110.(gv)
    ; buf_161.(gv)
    ; _TRAILB_62.(gv)
    ; _RATE8_51.(gv) ].
Definition tyout_ABUFLEN____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint ].
Definition res_ABUFLEN____absorb_avx2 : seq var_i :=
  [:: st_111.(gv); AT_110.(gv) ].

(* Body *)
Definition body_ABUFLEN____absorb_avx2 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_171.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_104.(gv)) AT_none (aint) (Pconst (536)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_110) (Pvar _LEN_104)) (Pvar _RATE8_51))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_111.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_171.(gv) ] ABUFLEN____addstate_avx2 [:: Pvar st_111
                                                                    ; Pvar AT_110
                                                                    ; Pvar buf_161
                                                                    ; Pvar offset_171
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_51) (Pvar AT_110)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_104.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_104) (Papp2 (Osub (Op_int)) (Pvar _RATE8_51) (Pvar AT_110))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_110.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_111.(gv) ] _keccakf1600_avx2 [:: Pvar st_111 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_51.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_104) (Pvar _RATE8_51)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_67.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_67) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_51)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_111.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_171.(gv) ] ABUFLEN____addstate_avx2 [:: Pvar st_111
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_161
                                                                    ; Pvar offset_171
                                                                    ; Pvar _RATE8_51
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_111.(gv) ] _keccakf1600_avx2 [:: Pvar st_111 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_67.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_67) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_104.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_104) (Pvar _RATE8_51))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_111.(gv)
                                    ; Lvar AT_110.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] ABUFLEN____addstate_avx2 [:: Pvar st_111
                                                                    ; Pvar AT_110
                                                                    ; Pvar buf_161
                                                                    ; Pvar offset_171
                                                                    ; Pvar _LEN_104
                                                                    ; Pvar _TRAILB_62 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_62) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_111.(gv) ] __addratebit_avx2 [:: Pvar st_111
                                                                    ; Pvar _RATE8_51 ]) ]
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
