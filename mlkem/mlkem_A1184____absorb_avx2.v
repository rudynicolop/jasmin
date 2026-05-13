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

(* A1184____absorb_avx2 *)
(* Local variables *)
Definition st_16063 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 16063).
Definition AT_16064 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16064).
Definition buf_16065 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16065).
Definition _TRAILB_16066 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16066).
Definition _RATE8_16067 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16067).
Definition offset_16068 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16068).
Definition _LEN_16069 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16069).
Definition ITERS_16070 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16070).
Definition i_16071 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16071).

(* Signature *)
Definition tyin_A1184____absorb_avx2 : seq atype :=
  [:: aarr U256 7; aint; aarr U8 1184; aint; aint ].
Definition args_A1184____absorb_avx2 : seq var_i :=
  [:: st_16063.(gv)
    ; AT_16064.(gv)
    ; buf_16065.(gv)
    ; _TRAILB_16066.(gv)
    ; _RATE8_16067.(gv) ].
Definition tyout_A1184____absorb_avx2 : seq atype := [:: aarr U256 7; aint ].
Definition res_A1184____absorb_avx2 : seq var_i :=
  [:: st_16063.(gv); AT_16064.(gv) ].

(* Body *)
Definition body_A1184____absorb_avx2 : cmd :=
  [:: cassgn (Lvar offset_16068.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_16069.(gv)) (aint) (Pconst (1184)%Z)
    ; cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_16064) (Pvar _LEN_16069)) (Pvar _RATE8_16067))
        [:: ccall [:: Lvar st_16063.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar offset_16068.(gv) ] A1184____addstate_avx2 [:: Pvar st_16063
                                                                    ; Pvar AT_16064
                                                                    ; Pvar buf_16065
                                                                    ; Pvar offset_16068
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_16067) (Pvar AT_16064)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_16069.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_16069) (Papp2 (Osub (Op_int)) (Pvar _RATE8_16067) (Pvar AT_16064)))
          ; cassgn (Lvar AT_16064.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_16063.(gv) ] _keccakf1600_avx2 [:: Pvar st_16063 ]
          ; cassgn (Lvar ITERS_16070.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16069) (Pvar _RATE8_16067))
          ; cassgn (Lvar i_16071.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16071) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_16070)))
              [:: ccall [:: Lvar st_16063.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar offset_16068.(gv) ] A1184____addstate_avx2 [:: Pvar st_16063
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf_16065
                                                                    ; Pvar offset_16068
                                                                    ; Pvar _RATE8_16067
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_16063.(gv) ] _keccakf1600_avx2 [:: Pvar st_16063 ]
                ; cassgn (Lvar i_16071.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16071) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_16069.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16069) (Pvar _RATE8_16067)) ]
        [::]
    ; ccall [:: Lvar st_16063.(gv)
              ; Lvar AT_16064.(gv)
              ; Lnone dummy_var_info (aword U64) ] A1184____addstate_avx2 [:: Pvar st_16063
                                                                    ; Pvar AT_16064
                                                                    ; Pvar buf_16065
                                                                    ; Pvar offset_16068
                                                                    ; Pvar _LEN_16069
                                                                    ; Pvar _TRAILB_16066 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_16066) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_16063.(gv) ] __addratebit_avx2 [:: Pvar st_16063
                                                               ; Pvar _RATE8_16067 ] ]
        [::] ].

Definition fd_A1184____absorb_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____absorb_avx2;
    f_params := args_A1184____absorb_avx2;
    f_body := body_A1184____absorb_avx2;
    f_tyout := tyout_A1184____absorb_avx2;
    f_res := res_A1184____absorb_avx2;
    f_extra := tt;
  |}.

End IDO.
