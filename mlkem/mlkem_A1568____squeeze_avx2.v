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

(* A1568____squeeze_avx2 *)
(* Local variables *)
Definition st_15649 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 15649).
Definition buf_15650 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15650).
Definition _RATE8_15651 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15651).
Definition offset_15652 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15652).
Definition _LEN_15653 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15653).
Definition ITERS_15654 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15654).
Definition LO_15655 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15655).
Definition i_15656 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15656).

(* Signature *)
Definition tyin_A1568____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1568; aint ].
Definition args_A1568____squeeze_avx2 : seq var_i :=
  [:: st_15649.(gv); buf_15650.(gv); _RATE8_15651.(gv) ].
Definition tyout_A1568____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1568 ].
Definition res_A1568____squeeze_avx2 : seq var_i :=
  [:: st_15649.(gv); buf_15650.(gv) ].

(* Body *)
Definition body_A1568____squeeze_avx2 : cmd :=
  [:: cassgn (Lvar offset_15652.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_15653.(gv)) (aint) (Pconst (1568)%Z)
    ; cassgn (Lvar ITERS_15654.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15653) (Pvar _RATE8_15651))
    ; cassgn (Lvar LO_15655.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15653) (Pvar _RATE8_15651))
    ; cassgn (Lvar i_15656.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15656) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_15654)))
        [:: ccall [:: Lvar st_15649.(gv) ] _keccakf1600_avx2 [:: Pvar st_15649 ]
          ; ccall [:: Lvar buf_15650.(gv); Lvar offset_15652.(gv) ] A1568____dumpstate_avx2 [:: Pvar buf_15650
                                                                    ; Pvar offset_15652
                                                                    ; Pvar _RATE8_15651
                                                                    ; Pvar st_15649 ]
          ; cassgn (Lvar i_15656.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15656) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_15655))
        [:: ccall [:: Lvar st_15649.(gv) ] _keccakf1600_avx2 [:: Pvar st_15649 ]
          ; ccall [:: Lvar buf_15650.(gv); Lvar offset_15652.(gv) ] A1568____dumpstate_avx2 [:: Pvar buf_15650
                                                                    ; Pvar offset_15652
                                                                    ; Pvar LO_15655
                                                                    ; Pvar st_15649 ] ]
        [::] ].

Definition fd_A1568____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____squeeze_avx2;
    f_params := args_A1568____squeeze_avx2;
    f_body := body_A1568____squeeze_avx2;
    f_tyout := tyout_A1568____squeeze_avx2;
    f_res := res_A1568____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
