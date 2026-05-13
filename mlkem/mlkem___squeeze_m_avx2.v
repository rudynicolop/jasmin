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

(* __squeeze_m_avx2 *)
(* Local variables *)
Definition st_18752 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 18752).
Definition buf_18753 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18753).
Definition _LEN_18754 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18754).
Definition _RATE8_18755 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18755).
Definition ITERS_18756 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18756).
Definition LO : gvar := mk_rocq_gvar Slocal (aint) (mkident 18757).
Definition i_18758 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18758).

(* Signature *)
Definition tyin___squeeze_m_avx2 : seq atype :=
  [:: aarr U256 7; aword U64; aint; aint ].
Definition args___squeeze_m_avx2 : seq var_i :=
  [:: st_18752.(gv); buf_18753.(gv); _LEN_18754.(gv); _RATE8_18755.(gv) ].
Definition tyout___squeeze_m_avx2 : seq atype := [:: aarr U256 7 ].
Definition res___squeeze_m_avx2 : seq var_i := [:: st_18752.(gv) ].

(* Body *)
Definition body___squeeze_m_avx2 : cmd :=
  [:: cassgn (Lvar ITERS_18756.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18754) (Pvar _RATE8_18755))
    ; cassgn (Lvar LO.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18754) (Pvar _RATE8_18755))
    ; cassgn (Lvar i_18758.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_18758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_18756)))
        [:: ccall [:: Lvar st_18752.(gv) ] _keccakf1600_avx2 [:: Pvar st_18752 ]
          ; ccall [:: Lvar buf_18753.(gv) ] __dumpstate_m_avx2 [:: Pvar buf_18753
                                                                 ; Pvar _RATE8_18755
                                                                 ; Pvar st_18752 ]
          ; cassgn (Lvar i_18758.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_18758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO))
        [:: ccall [:: Lvar st_18752.(gv) ] _keccakf1600_avx2 [:: Pvar st_18752 ]
          ; ccall [:: Lvar buf_18753.(gv) ] __dumpstate_m_avx2 [:: Pvar buf_18753
                                                                 ; Pvar LO
                                                                 ; Pvar st_18752 ] ]
        [::] ].

Definition fd___squeeze_m_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___squeeze_m_avx2;
    f_params := args___squeeze_m_avx2;
    f_body := body___squeeze_m_avx2;
    f_tyout := tyout___squeeze_m_avx2;
    f_res := res___squeeze_m_avx2;
    f_extra := tt;
  |}.

End IDO.
