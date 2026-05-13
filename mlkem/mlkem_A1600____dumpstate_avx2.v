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

(* A1600____dumpstate_avx2 *)
(* Local variables *)
Definition buf_14898 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14898).
Definition offset_14899 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14899).
Definition _LEN_14900 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14900).
Definition st_14901 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 14901).
Definition DELTA_14902 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14902).
Definition t128_0_14903 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14903).
Definition t128_1_14904 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14904).
Definition t_14905 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14905).
Definition t256_0_14906 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14906).
Definition t256_1_14907 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14907).
Definition t256_2_14908 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14908).
Definition t256_3_14909 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14909).
Definition t256_4_14910 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14910).

(* Signature *)
Definition tyin_A1600____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1600; aword U64; aint; aarr U256 7 ].
Definition args_A1600____dumpstate_avx2 : seq var_i :=
  [:: buf_14898.(gv); offset_14899.(gv); _LEN_14900.(gv); st_14901.(gv) ].
Definition tyout_A1600____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1600; aword U64 ].
Definition res_A1600____dumpstate_avx2 : seq var_i :=
  [:: buf_14898.(gv); offset_14899.(gv) ].

(* Body *)
Definition body_A1600____dumpstate_avx2 : cmd :=
  [:: cassgn (Lvar DELTA_14902.(gv)) (aint) (Pconst (0)%Z)
    ; cif
        (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_14900))
        [:: ccall [:: Lvar buf_14898.(gv)
                    ; Lvar DELTA_14902.(gv)
                    ; Lnone dummy_var_info (aint) ] A1600____a_ilen_write_upto32 [:: Pvar buf_14898
                                                                    ; Pvar offset_14899
                                                                    ; Pvar DELTA_14902
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_14901 (Pconst (0)%Z) ]
          ; cassgn (Lvar _LEN_14900.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_14900) (Pconst (8)%Z)) ]
        [:: ccall [:: Lvar buf_14898.(gv)
                    ; Lvar DELTA_14902.(gv)
                    ; Lvar _LEN_14900.(gv) ] A1600____a_ilen_write_upto32 [:: Pvar buf_14898
                                                                    ; Pvar offset_14899
                                                                    ; Pvar DELTA_14902
                                                                    ; Pvar _LEN_14900
                                                                    ; Pget Aligned AAscale U256 st_14901 (Pconst (0)%Z) ] ]
    ; ccall [:: Lvar buf_14898.(gv)
              ; Lvar DELTA_14902.(gv)
              ; Lvar _LEN_14900.(gv) ] A1600____a_ilen_write_upto32 [:: Pvar buf_14898
                                                                    ; Pvar offset_14899
                                                                    ; Pvar DELTA_14902
                                                                    ; Pvar _LEN_14900
                                                                    ; Pget Aligned AAscale U256 st_14901 (Pconst (1)%Z) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14900))
        [:: cassgn (Lvar t128_0_14903.(gv)) (aword U128) (Pget Aligned AAscale U256 st_14901 (Pconst (2)%Z))
          ; copn [:: Lvar t128_1_14904.(gv) ] (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_14901 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
          ; cassgn (Lvar t_14905.(gv)) (aword U64) (Pvar t128_1_14904)
          ; ccall [:: Lvar buf_14898.(gv)
                    ; Lvar DELTA_14902.(gv)
                    ; Lvar _LEN_14900.(gv) ] A1600____a_ilen_write_upto8 [:: Pvar buf_14898
                                                                    ; Pvar offset_14899
                                                                    ; Pvar DELTA_14902
                                                                    ; Pvar _LEN_14900
                                                                    ; Pvar t_14905 ]
          ; copn [:: Lvar t128_1_14904.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_14904
                                                                    ; Pvar t128_1_14904 ]
          ; cif
              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14900))
              [:: copn [:: Lvar t256_0_14906.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_14901 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_14901 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_1_14907.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_14901 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_14901 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_2_14908.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_14901 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_14901 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_3_14909.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_14901 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_14901 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_4_14910.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_14906
                                                                    ; Pvar t256_3_14909
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                ; ccall [:: Lvar buf_14898.(gv)
                          ; Lvar DELTA_14902.(gv)
                          ; Lvar _LEN_14900.(gv) ] A1600____a_ilen_write_upto32 [:: Pvar buf_14898
                                                                    ; Pvar offset_14899
                                                                    ; Pvar DELTA_14902
                                                                    ; Pvar _LEN_14900
                                                                    ; Pvar t256_4_14910 ]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14900))
                    [:: cassgn (Lvar t_14905.(gv)) (aword U64) (Pvar t128_0_14903)
                      ; ccall [:: Lvar buf_14898.(gv)
                                ; Lvar DELTA_14902.(gv)
                                ; Lvar _LEN_14900.(gv) ] A1600____a_ilen_write_upto8 [:: Pvar buf_14898
                                                                    ; Pvar offset_14899
                                                                    ; Pvar DELTA_14902
                                                                    ; Pvar _LEN_14900
                                                                    ; Pvar t_14905 ]
                      ; copn [:: Lvar t128_0_14903.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_14903
                                                                    ; Pvar t128_0_14903 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14900))
                    [:: copn [:: Lvar t256_4_14910.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_14909
                                                                    ; Pvar t256_1_14907
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                      ; ccall [:: Lvar buf_14898.(gv)
                                ; Lvar DELTA_14902.(gv)
                                ; Lvar _LEN_14900.(gv) ] A1600____a_ilen_write_upto32 [:: Pvar buf_14898
                                                                    ; Pvar offset_14899
                                                                    ; Pvar DELTA_14902
                                                                    ; Pvar _LEN_14900
                                                                    ; Pvar t256_4_14910 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14900))
                    [:: cassgn (Lvar t_14905.(gv)) (aword U64) (Pvar t128_1_14904)
                      ; ccall [:: Lvar buf_14898.(gv)
                                ; Lvar DELTA_14902.(gv)
                                ; Lvar _LEN_14900.(gv) ] A1600____a_ilen_write_upto8 [:: Pvar buf_14898
                                                                    ; Pvar offset_14899
                                                                    ; Pvar DELTA_14902
                                                                    ; Pvar _LEN_14900
                                                                    ; Pvar t_14905 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14900))
                    [:: copn [:: Lvar t256_4_14910.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_14908
                                                                    ; Pvar t256_0_14906
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                      ; ccall [:: Lvar buf_14898.(gv)
                                ; Lvar DELTA_14902.(gv)
                                ; Lvar _LEN_14900.(gv) ] A1600____a_ilen_write_upto32 [:: Pvar buf_14898
                                                                    ; Pvar offset_14899
                                                                    ; Pvar DELTA_14902
                                                                    ; Pvar _LEN_14900
                                                                    ; Pvar t256_4_14910 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14900))
                    [:: cassgn (Lvar t_14905.(gv)) (aword U64) (Pvar t128_0_14903)
                      ; ccall [:: Lvar buf_14898.(gv)
                                ; Lvar DELTA_14902.(gv)
                                ; Lvar _LEN_14900.(gv) ] A1600____a_ilen_write_upto8 [:: Pvar buf_14898
                                                                    ; Pvar offset_14899
                                                                    ; Pvar DELTA_14902
                                                                    ; Pvar _LEN_14900
                                                                    ; Pvar t_14905 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14900))
                    [:: copn [:: Lvar t256_4_14910.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_14907
                                                                    ; Pvar t256_2_14908
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                      ; ccall [:: Lvar buf_14898.(gv)
                                ; Lvar DELTA_14902.(gv)
                                ; Lvar _LEN_14900.(gv) ] A1600____a_ilen_write_upto32 [:: Pvar buf_14898
                                                                    ; Pvar offset_14899
                                                                    ; Pvar DELTA_14902
                                                                    ; Pvar _LEN_14900
                                                                    ; Pvar t256_4_14910 ] ]
                    [::] ]
              [::] ]
        [::]
    ; cassgn (Lvar offset_14899.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14899) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14902))) ].

Definition fd_A1600____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____dumpstate_avx2;
    f_params := args_A1600____dumpstate_avx2;
    f_body := body_A1600____dumpstate_avx2;
    f_tyout := tyout_A1600____dumpstate_avx2;
    f_res := res_A1600____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
