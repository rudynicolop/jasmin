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

(* __absorb_m_avx2 *)
(* Local variables *)
Definition st_18779 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 18779).
Definition AT_18780 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18780).
Definition buf_18781 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18781).
Definition _LEN_18782 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18782).
Definition _TRAILB_18783 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18783).
Definition _RATE8 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18784).
Definition ITERS : gvar := mk_rocq_gvar Slocal (aint) (mkident 18785).
Definition i_18786 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18786).

(* Signature *)
Definition tyin___absorb_m_avx2 : seq atype :=
  [:: aarr U256 7; aint; aword U64; aint; aint; aint ].
Definition args___absorb_m_avx2 : seq var_i :=
  [:: st_18779.(gv)
    ; AT_18780.(gv)
    ; buf_18781.(gv)
    ; _LEN_18782.(gv)
    ; _TRAILB_18783.(gv)
    ; _RATE8.(gv) ].
Definition tyout___absorb_m_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res___absorb_m_avx2 : seq var_i :=
  [:: st_18779.(gv); AT_18780.(gv) ].

(* Body *)
Definition body___absorb_m_avx2 : cmd :=
  [:: cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_18780) (Pvar _LEN_18782)) (Pvar _RATE8))
        [:: ccall [:: Lvar st_18779.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar buf_18781.(gv) ] __addstate_m_avx2 [:: Pvar st_18779
                                                                ; Pvar AT_18780
                                                                ; Pvar buf_18781
                                                                ; Papp2 (Osub (Op_int)) (Pvar _RATE8) (Pvar AT_18780)
                                                                ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_18782.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_18782) (Papp2 (Osub (Op_int)) (Pvar _RATE8) (Pvar AT_18780)))
          ; cassgn (Lvar AT_18780.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_18779.(gv) ] _keccakf1600_avx2 [:: Pvar st_18779 ]
          ; cassgn (Lvar ITERS.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18782) (Pvar _RATE8))
          ; cassgn (Lvar i_18786.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_18786) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS)))
              [:: ccall [:: Lvar st_18779.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar buf_18781.(gv) ] __addstate_m_avx2 [:: Pvar st_18779
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_18781
                                                                    ; Pvar _RATE8
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_18779.(gv) ] _keccakf1600_avx2 [:: Pvar st_18779 ]
                ; cassgn (Lvar i_18786.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_18786) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_18782.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18782) (Pvar _RATE8)) ]
        [::]
    ; ccall [:: Lvar st_18779.(gv)
              ; Lvar AT_18780.(gv)
              ; Lnone dummy_var_info (aword U64) ] __addstate_m_avx2 [:: Pvar st_18779
                                                                    ; Pvar AT_18780
                                                                    ; Pvar buf_18781
                                                                    ; Pvar _LEN_18782
                                                                    ; Pvar _TRAILB_18783 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_18783) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_18779.(gv) ] __addratebit_avx2 [:: Pvar st_18779
                                                               ; Pvar _RATE8 ] ]
        [::] ].

Definition fd___absorb_m_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___absorb_m_avx2;
    f_params := args___absorb_m_avx2;
    f_body := body___absorb_m_avx2;
    f_tyout := tyout___absorb_m_avx2;
    f_res := res___absorb_m_avx2;
    f_extra := tt;
  |}.

End IDO.
