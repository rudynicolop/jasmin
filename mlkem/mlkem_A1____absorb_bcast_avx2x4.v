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

(* A1____absorb_bcast_avx2x4 *)
(* Local variables *)
Definition st_18153 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 18153).
Definition AT_18154 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18154).
Definition buf_18155 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18155).
Definition _TRAILB_18156 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18156).
Definition _RATE8_18157 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18157).
Definition offset_18158 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18158).
Definition _LEN_18159 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18159).
Definition ITERS_18160 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18160).
Definition i_18161 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18161).

(* Signature *)
Definition tyin_A1____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 1; aint; aint ].
Definition args_A1____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_18153.(gv)
    ; AT_18154.(gv)
    ; buf_18155.(gv)
    ; _TRAILB_18156.(gv)
    ; _RATE8_18157.(gv) ].
Definition tyout_A1____absorb_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A1____absorb_bcast_avx2x4 : seq var_i :=
  [:: st_18153.(gv); AT_18154.(gv) ].

(* Body *)
Definition body_A1____absorb_bcast_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar offset_18158.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_18159.(gv)) AT_none (aint) (Pconst (1)%Z))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_18154) (Pvar _LEN_18159)) (Pvar _RATE8_18157))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_18153.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar offset_18158.(gv) ] A1____addstate_bcast_avx2x4 [:: Pvar st_18153
                                                                    ; Pvar AT_18154
                                                                    ; Pvar buf_18155
                                                                    ; Pvar offset_18158
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_18157) (Pvar AT_18154)
                                                                    ; Pconst (0)%Z ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_18159.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_18159) (Papp2 (Osub (Op_int)) (Pvar _RATE8_18157) (Pvar AT_18154))))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_18154.(gv)) AT_none (aint) (Pconst (0)%Z))
                                ; MkI dummy_instr_info (Ccall [:: Lvar st_18153.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_18153 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar ITERS_18160.(gv)) AT_none (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18159) (Pvar _RATE8_18157)))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_18161.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
                                ; MkI dummy_instr_info (Cwhile Align
                                                          [::]
                                                          (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_18161) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_18160)))
                                                          dummy_instr_info
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_18153.(gv)
                                                                  ; Lnone dummy_var_info (aint)
                                                                  ; Lvar offset_18158.(gv) ] A1____addstate_bcast_avx2x4 [:: Pvar st_18153
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_18155
                                                                    ; Pvar offset_18158
                                                                    ; Pvar _RATE8_18157
                                                                    ; Pconst (0)%Z ])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar st_18153.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_18153 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar i_18161.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_18161) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z)))) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar _LEN_18159.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18159) (Pvar _RATE8_18157))) ]
                              [::])
    ; MkI dummy_instr_info (Ccall [:: Lvar st_18153.(gv)
                                    ; Lvar AT_18154.(gv)
                                    ; Lnone dummy_var_info (aword U64) ] A1____addstate_bcast_avx2x4 [:: Pvar st_18153
                                                                    ; Pvar AT_18154
                                                                    ; Pvar buf_18155
                                                                    ; Pvar offset_18158
                                                                    ; Pvar _LEN_18159
                                                                    ; Pvar _TRAILB_18156 ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_18156) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar st_18153.(gv) ] __addratebit_avx2x4 [:: Pvar st_18153
                                                                    ; Pvar _RATE8_18157 ]) ]
                              [::]) ].

Definition fd_A1____absorb_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____absorb_bcast_avx2x4;
    f_params := args_A1____absorb_bcast_avx2x4;
    f_body := body_A1____absorb_bcast_avx2x4;
    f_tyout := tyout_A1____absorb_bcast_avx2x4;
    f_res := res_A1____absorb_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
