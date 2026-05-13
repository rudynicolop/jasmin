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

(* A1184____squeeze_avx2 *)
(* Local variables *)
Definition st_16031 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 16031).
Definition buf_16032 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16032).
Definition _RATE8_16033 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16033).
Definition offset_16034 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16034).
Definition _LEN_16035 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16035).
Definition ITERS_16036 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16036).
Definition LO_16037 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16037).
Definition i_16038 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16038).

(* Signature *)
Definition tyin_A1184____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1184; aint ].
Definition args_A1184____squeeze_avx2 : seq var_i :=
  [:: st_16031.(gv); buf_16032.(gv); _RATE8_16033.(gv) ].
Definition tyout_A1184____squeeze_avx2 : seq atype :=
  [:: aarr U256 7; aarr U8 1184 ].
Definition res_A1184____squeeze_avx2 : seq var_i :=
  [:: st_16031.(gv); buf_16032.(gv) ].

(* Body *)
Definition body_A1184____squeeze_avx2 : cmd :=
  [:: cassgn (Lvar offset_16034.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_16035.(gv)) (aint) (Pconst (1184)%Z)
    ; cassgn (Lvar ITERS_16036.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16035) (Pvar _RATE8_16033))
    ; cassgn (Lvar LO_16037.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16035) (Pvar _RATE8_16033))
    ; cassgn (Lvar i_16038.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16038) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_16036)))
        [:: ccall [:: Lvar st_16031.(gv) ] _keccakf1600_avx2 [:: Pvar st_16031 ]
          ; ccall [:: Lvar buf_16032.(gv); Lvar offset_16034.(gv) ] A1184____dumpstate_avx2 [:: Pvar buf_16032
                                                                    ; Pvar offset_16034
                                                                    ; Pvar _RATE8_16033
                                                                    ; Pvar st_16031 ]
          ; cassgn (Lvar i_16038.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16038) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LO_16037))
        [:: ccall [:: Lvar st_16031.(gv) ] _keccakf1600_avx2 [:: Pvar st_16031 ]
          ; ccall [:: Lvar buf_16032.(gv); Lvar offset_16034.(gv) ] A1184____dumpstate_avx2 [:: Pvar buf_16032
                                                                    ; Pvar offset_16034
                                                                    ; Pvar LO_16037
                                                                    ; Pvar st_16031 ] ]
        [::] ].

Definition fd_A1184____squeeze_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____squeeze_avx2;
    f_params := args_A1184____squeeze_avx2;
    f_body := body_A1184____squeeze_avx2;
    f_tyout := tyout_A1184____squeeze_avx2;
    f_res := res_A1184____squeeze_avx2;
    f_extra := tt;
  |}.

End IDO.
