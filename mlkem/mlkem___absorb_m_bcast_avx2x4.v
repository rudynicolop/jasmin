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

(* __absorb_m_bcast_avx2x4 *)
(* Local variables *)
Definition st_18528 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 18528).
Definition AT_18529 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18529).
Definition buf_18530 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18530).
Definition _LEN_18531 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18531).
Definition _TRAILB_18532 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18532).
Definition _RATE8_18533 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18533).
Definition ITERS_18534 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18534).
Definition i_18535 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18535).

(* Signature *)
Definition tyin___absorb_m_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64; aint; aint; aint ].
Definition args___absorb_m_bcast_avx2x4 : seq var_i :=
  [:: st_18528.(gv)
    ; AT_18529.(gv)
    ; buf_18530.(gv)
    ; _LEN_18531.(gv)
    ; _TRAILB_18532.(gv)
    ; _RATE8_18533.(gv) ].
Definition tyout___absorb_m_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res___absorb_m_bcast_avx2x4 : seq var_i :=
  [:: st_18528.(gv); AT_18529.(gv) ].

(* Body *)
Definition body___absorb_m_bcast_avx2x4 : cmd :=
  [:: cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_18529) (Pvar _LEN_18531)) (Pvar _RATE8_18533))
        [:: ccall [:: Lvar st_18528.(gv); Lnone dummy_var_info (aint) ] __addstate_m_bcast_avx2x4 [:: Pvar st_18528
                                                                    ; Pvar AT_18529
                                                                    ; Pvar buf_18530
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_18533) (Pvar AT_18529)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_18531.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_18531) (Papp2 (Osub (Op_int)) (Pvar _RATE8_18533) (Pvar AT_18529)))
          ; cassgn (Lvar AT_18529.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_18528.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_18528 ]
          ; cassgn (Lvar ITERS_18534.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18531) (Pvar _RATE8_18533))
          ; cassgn (Lvar i_18535.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_18535) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_18534)))
              [:: ccall [:: Lvar st_18528.(gv); Lnone dummy_var_info (aint) ] __addstate_m_bcast_avx2x4 [:: Pvar st_18528
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_18530
                                                                    ; Pvar _RATE8_18533
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_18528.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_18528 ]
                ; cassgn (Lvar i_18535.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_18535) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_18531.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18531) (Pvar _RATE8_18533)) ]
        [::]
    ; ccall [:: Lvar st_18528.(gv); Lvar AT_18529.(gv) ] __addstate_m_bcast_avx2x4 [:: Pvar st_18528
                                                                    ; Pvar AT_18529
                                                                    ; Pvar buf_18530
                                                                    ; Pvar _LEN_18531
                                                                    ; Pvar _TRAILB_18532 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_18532) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_18528.(gv) ] __addratebit_avx2x4 [:: Pvar st_18528
                                                                 ; Pvar _RATE8_18533 ] ]
        [::] ].

Definition fd___absorb_m_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___absorb_m_bcast_avx2x4;
    f_params := args___absorb_m_bcast_avx2x4;
    f_body := body___absorb_m_bcast_avx2x4;
    f_tyout := tyout___absorb_m_bcast_avx2x4;
    f_res := res___absorb_m_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
