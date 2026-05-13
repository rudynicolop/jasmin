From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi syntax data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* A33____squeeze_avx2x4 *)
(* Local variables *)
Definition st_16907 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 16907).
Definition buf0_16908 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16908).
Definition buf1_16909 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16909).
Definition buf2_16910 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16910).
Definition buf3_16911 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16911).
Definition _RATE8_16912 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16912).
Definition offset_16913 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16913).
Definition _LEN_16914 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16914).
Definition ITERS_16915 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16915).
Definition LO_16916 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16916).
Definition i_16917 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16917).

(* Signature *)
Definition tyin_A33____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 33; aarr U8 33; aarr U8 33; aarr U8 33; aint ].
Definition args_A33____squeeze_avx2x4 : seq var_i :=
  [:: st_16907.(gv)
    ; buf0_16908.(gv)
    ; buf1_16909.(gv)
    ; buf2_16910.(gv)
    ; buf3_16911.(gv)
    ; _RATE8_16912.(gv) ].
Definition tyout_A33____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 33; aarr U8 33; aarr U8 33; aarr U8 33 ].
Definition res_A33____squeeze_avx2x4 : seq var_i :=
  [:: st_16907.(gv)
    ; buf0_16908.(gv)
    ; buf1_16909.(gv)
    ; buf2_16910.(gv)
    ; buf3_16911.(gv) ].

(* Body *)
Definition body_A33____squeeze_avx2x4 : cmd :=
  [:: cassgn (Lvar offset_16913.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_16914.(gv)) (aint) (Pconst (33)%Z)
    ; cassgn (Lvar ITERS_16915.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16914) (Pvar _RATE8_16912))
    ; cassgn (Lvar LO_16916.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16914) (Pvar _RATE8_16912))
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_16915))
        [:: cassgn (Lvar i_16917.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16917) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_16915)))
              [:: ccall [:: Lvar st_16907.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_16907 ]
                ; ccall [:: Lvar buf0_16908.(gv)
                          ; Lvar buf1_16909.(gv)
                          ; Lvar buf2_16910.(gv)
                          ; Lvar buf3_16911.(gv)
                          ; Lvar offset_16913.(gv) ] A33____dumpstate_avx2x4 [:: Pvar buf0_16908
                                                                    ; Pvar buf1_16909
                                                                    ; Pvar buf2_16910
                                                                    ; Pvar buf3_16911
                                                                    ; Pvar offset_16913
                                                                    ; Pvar _RATE8_16912
                                                                    ; Pvar st_16907 ]
                ; cassgn (Lvar i_16917.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16917) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ] ]
        [::]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_16916))
        [:: ccall [:: Lvar st_16907.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_16907 ]
          ; ccall [:: Lvar buf0_16908.(gv)
                    ; Lvar buf1_16909.(gv)
                    ; Lvar buf2_16910.(gv)
                    ; Lvar buf3_16911.(gv)
                    ; Lvar offset_16913.(gv) ] A33____dumpstate_avx2x4 [:: Pvar buf0_16908
                                                                    ; Pvar buf1_16909
                                                                    ; Pvar buf2_16910
                                                                    ; Pvar buf3_16911
                                                                    ; Pvar offset_16913
                                                                    ; Pvar LO_16916
                                                                    ; Pvar st_16907 ] ]
        [::] ].

Definition fd_A33____squeeze_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____squeeze_avx2x4;
    f_params := args_A33____squeeze_avx2x4;
    f_body := body_A33____squeeze_avx2x4;
    f_tyout := tyout_A33____squeeze_avx2x4;
    f_res := res_A33____squeeze_avx2x4;
    f_extra := tt;
  |}.

End IDO.
