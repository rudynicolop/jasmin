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

(* A1600____squeeze_avx2x4 *)
(* Local variables *)
Definition st_14750 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14750).
Definition buf0_14751 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14751).
Definition buf1_14752 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14752).
Definition buf2_14753 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14753).
Definition buf3_14754 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14754).
Definition _RATE8_14755 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14755).
Definition offset_14756 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14756).
Definition _LEN_14757 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14757).
Definition ITERS_14758 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14758).
Definition LO_14759 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14759).
Definition i_14760 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14760).

(* Signature *)
Definition tyin_A1600____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aarr U8 1600
    ; aarr U8 1600
    ; aarr U8 1600
    ; aarr U8 1600
    ; aint ].
Definition args_A1600____squeeze_avx2x4 : seq var_i :=
  [:: st_14750.(gv)
    ; buf0_14751.(gv)
    ; buf1_14752.(gv)
    ; buf2_14753.(gv)
    ; buf3_14754.(gv)
    ; _RATE8_14755.(gv) ].
Definition tyout_A1600____squeeze_avx2x4 : seq atype :=
  [:: aarr U256 25; aarr U8 1600; aarr U8 1600; aarr U8 1600; aarr U8 1600 ].
Definition res_A1600____squeeze_avx2x4 : seq var_i :=
  [:: st_14750.(gv)
    ; buf0_14751.(gv)
    ; buf1_14752.(gv)
    ; buf2_14753.(gv)
    ; buf3_14754.(gv) ].

(* Body *)
Definition body_A1600____squeeze_avx2x4 : cmd :=
  [:: cassgn (Lvar offset_14756.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_14757.(gv)) (aint) (Pconst (1600)%Z)
    ; cassgn (Lvar ITERS_14758.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14757) (Pvar _RATE8_14755))
    ; cassgn (Lvar LO_14759.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14757) (Pvar _RATE8_14755))
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar ITERS_14758))
        [:: cassgn (Lvar i_14760.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_14760) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_14758)))
              [:: ccall [:: Lvar st_14750.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_14750 ]
                ; ccall [:: Lvar buf0_14751.(gv)
                          ; Lvar buf1_14752.(gv)
                          ; Lvar buf2_14753.(gv)
                          ; Lvar buf3_14754.(gv)
                          ; Lvar offset_14756.(gv) ] A1600____dumpstate_avx2x4 [:: Pvar buf0_14751
                                                                    ; Pvar buf1_14752
                                                                    ; Pvar buf2_14753
                                                                    ; Pvar buf3_14754
                                                                    ; Pvar offset_14756
                                                                    ; Pvar _RATE8_14755
                                                                    ; Pvar st_14750 ]
                ; cassgn (Lvar i_14760.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_14760) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ] ]
        [::]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_14759))
        [:: ccall [:: Lvar st_14750.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_14750 ]
          ; ccall [:: Lvar buf0_14751.(gv)
                    ; Lvar buf1_14752.(gv)
                    ; Lvar buf2_14753.(gv)
                    ; Lvar buf3_14754.(gv)
                    ; Lvar offset_14756.(gv) ] A1600____dumpstate_avx2x4 [:: Pvar buf0_14751
                                                                    ; Pvar buf1_14752
                                                                    ; Pvar buf2_14753
                                                                    ; Pvar buf3_14754
                                                                    ; Pvar offset_14756
                                                                    ; Pvar LO_14759
                                                                    ; Pvar st_14750 ] ]
        [::] ].

Definition fd_A1600____squeeze_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____squeeze_avx2x4;
    f_params := args_A1600____squeeze_avx2x4;
    f_body := body_A1600____squeeze_avx2x4;
    f_tyout := tyout_A1600____squeeze_avx2x4;
    f_res := res_A1600____squeeze_avx2x4;
    f_extra := tt;
  |}.

End IDO.
