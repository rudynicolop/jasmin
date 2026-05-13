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

(* A1184____absorb_avx2x4 *)
(* Local variables *)
Definition st_15946 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 15946).
Definition AT_15947 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15947).
Definition buf0_15948 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15948).
Definition buf1_15949 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15949).
Definition buf2_15950 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15950).
Definition buf3_15951 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15951).
Definition _TRAILB_15952 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15952).
Definition _RATE8_15953 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15953).
Definition offset_15954 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15954).
Definition _LEN_15955 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15955).
Definition ITERS_15956 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15956).
Definition i_15957 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15957).

(* Signature *)
Definition tyin_A1184____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 1184
    ; aarr U8 1184
    ; aarr U8 1184
    ; aarr U8 1184
    ; aint
    ; aint ].
Definition args_A1184____absorb_avx2x4 : seq var_i :=
  [:: st_15946.(gv)
    ; AT_15947.(gv)
    ; buf0_15948.(gv)
    ; buf1_15949.(gv)
    ; buf2_15950.(gv)
    ; buf3_15951.(gv)
    ; _TRAILB_15952.(gv)
    ; _RATE8_15953.(gv) ].
Definition tyout_A1184____absorb_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res_A1184____absorb_avx2x4 : seq var_i :=
  [:: st_15946.(gv); AT_15947.(gv) ].

(* Body *)
Definition body_A1184____absorb_avx2x4 : cmd :=
  [:: cassgn (Lvar offset_15954.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cassgn (Lvar _LEN_15955.(gv)) (aint) (Pconst (1184)%Z)
    ; cif
        (Papp2 (Oge (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar AT_15947) (Pvar _LEN_15955)) (Pvar _RATE8_15953))
        [:: ccall [:: Lvar st_15946.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar offset_15954.(gv) ] A1184____addstate_avx2x4 [:: Pvar st_15946
                                                                    ; Pvar AT_15947
                                                                    ; Pvar buf0_15948
                                                                    ; Pvar buf1_15949
                                                                    ; Pvar buf2_15950
                                                                    ; Pvar buf3_15951
                                                                    ; Pvar offset_15954
                                                                    ; Papp2 (Osub (Op_int)) (Pvar _RATE8_15953) (Pvar AT_15947)
                                                                    ; Pconst (0)%Z ]
          ; cassgn (Lvar _LEN_15955.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_15955) (Papp2 (Osub (Op_int)) (Pvar _RATE8_15953) (Pvar AT_15947)))
          ; cassgn (Lvar AT_15947.(gv)) (aint) (Pconst (0)%Z)
          ; ccall [:: Lvar st_15946.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_15946 ]
          ; cassgn (Lvar ITERS_15956.(gv)) (aint) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15955) (Pvar _RATE8_15953))
          ; cassgn (Lvar i_15957.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
          ; cwhile
              [::]
              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15957) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar ITERS_15956)))
              [:: ccall [:: Lvar st_15946.(gv)
                          ; Lnone dummy_var_info (aint)
                          ; Lvar offset_15954.(gv) ] A1184____addstate_avx2x4 [:: Pvar st_15946
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar buf0_15948
                                                                    ; Pvar buf1_15949
                                                                    ; Pvar buf2_15950
                                                                    ; Pvar buf3_15951
                                                                    ; Pvar offset_15954
                                                                    ; Pvar _RATE8_15953
                                                                    ; Pconst (0)%Z ]
                ; ccall [:: Lvar st_15946.(gv) ] _keccakf1600_avx2x4 [:: Pvar st_15946 ]
                ; cassgn (Lvar i_15957.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15957) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))) ]
          ; cassgn (Lvar _LEN_15955.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15955) (Pvar _RATE8_15953)) ]
        [::]
    ; ccall [:: Lvar st_15946.(gv)
              ; Lvar AT_15947.(gv)
              ; Lnone dummy_var_info (aword U64) ] A1184____addstate_avx2x4 [:: Pvar st_15946
                                                                    ; Pvar AT_15947
                                                                    ; Pvar buf0_15948
                                                                    ; Pvar buf1_15949
                                                                    ; Pvar buf2_15950
                                                                    ; Pvar buf3_15951
                                                                    ; Pvar offset_15954
                                                                    ; Pvar _LEN_15955
                                                                    ; Pvar _TRAILB_15952 ]
    ; cif
        (Papp2 (Oneq (Op_int)) (Pvar _TRAILB_15952) (Pconst (0)%Z))
        [:: ccall [:: Lvar st_15946.(gv) ] __addratebit_avx2x4 [:: Pvar st_15946
                                                                 ; Pvar _RATE8_15953 ] ]
        [::] ].

Definition fd_A1184____absorb_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____absorb_avx2x4;
    f_params := args_A1184____absorb_avx2x4;
    f_body := body_A1184____absorb_avx2x4;
    f_tyout := tyout_A1184____absorb_avx2x4;
    f_res := res_A1184____absorb_avx2x4;
    f_extra := tt;
  |}.

End IDO.
