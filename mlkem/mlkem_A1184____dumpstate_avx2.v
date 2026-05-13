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

(* A1184____dumpstate_avx2 *)
(* Local variables *)
Definition buf_16044 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16044).
Definition offset_16045 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16045).
Definition _LEN_16046 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16046).
Definition st_16047 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 16047).
Definition DELTA_16048 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16048).
Definition t128_0_16049 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16049).
Definition t128_1_16050 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16050).
Definition t_16051 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16051).
Definition t256_0_16052 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16052).
Definition t256_1_16053 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16053).
Definition t256_2_16054 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16054).
Definition t256_3_16055 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16055).
Definition t256_4_16056 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16056).

(* Signature *)
Definition tyin_A1184____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1184; aword U64; aint; aarr U256 7 ].
Definition args_A1184____dumpstate_avx2 : seq var_i :=
  [:: buf_16044.(gv); offset_16045.(gv); _LEN_16046.(gv); st_16047.(gv) ].
Definition tyout_A1184____dumpstate_avx2 : seq atype :=
  [:: aarr U8 1184; aword U64 ].
Definition res_A1184____dumpstate_avx2 : seq var_i :=
  [:: buf_16044.(gv); offset_16045.(gv) ].

(* Body *)
Definition body_A1184____dumpstate_avx2 : cmd :=
  [:: cassgn (Lvar DELTA_16048.(gv)) (aint) (Pconst (0)%Z)
    ; cif
        (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_16046))
        [:: ccall [:: Lvar buf_16044.(gv)
                    ; Lvar DELTA_16048.(gv)
                    ; Lnone dummy_var_info (aint) ] A1184____a_ilen_write_upto32 [:: Pvar buf_16044
                                                                    ; Pvar offset_16045
                                                                    ; Pvar DELTA_16048
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_16047 (Pconst (0)%Z) ]
          ; cassgn (Lvar _LEN_16046.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_16046) (Pconst (8)%Z)) ]
        [:: ccall [:: Lvar buf_16044.(gv)
                    ; Lvar DELTA_16048.(gv)
                    ; Lvar _LEN_16046.(gv) ] A1184____a_ilen_write_upto32 [:: Pvar buf_16044
                                                                    ; Pvar offset_16045
                                                                    ; Pvar DELTA_16048
                                                                    ; Pvar _LEN_16046
                                                                    ; Pget Aligned AAscale U256 st_16047 (Pconst (0)%Z) ] ]
    ; ccall [:: Lvar buf_16044.(gv)
              ; Lvar DELTA_16048.(gv)
              ; Lvar _LEN_16046.(gv) ] A1184____a_ilen_write_upto32 [:: Pvar buf_16044
                                                                    ; Pvar offset_16045
                                                                    ; Pvar DELTA_16048
                                                                    ; Pvar _LEN_16046
                                                                    ; Pget Aligned AAscale U256 st_16047 (Pconst (1)%Z) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16046))
        [:: cassgn (Lvar t128_0_16049.(gv)) (aword U128) (Pget Aligned AAscale U256 st_16047 (Pconst (2)%Z))
          ; copn [:: Lvar t128_1_16050.(gv) ] (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_16047 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
          ; cassgn (Lvar t_16051.(gv)) (aword U64) (Pvar t128_1_16050)
          ; ccall [:: Lvar buf_16044.(gv)
                    ; Lvar DELTA_16048.(gv)
                    ; Lvar _LEN_16046.(gv) ] A1184____a_ilen_write_upto8 [:: Pvar buf_16044
                                                                    ; Pvar offset_16045
                                                                    ; Pvar DELTA_16048
                                                                    ; Pvar _LEN_16046
                                                                    ; Pvar t_16051 ]
          ; copn [:: Lvar t128_1_16050.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_16050
                                                                    ; Pvar t128_1_16050 ]
          ; cif
              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16046))
              [:: copn [:: Lvar t256_0_16052.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_16047 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_16047 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_1_16053.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_16047 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_16047 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_2_16054.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_16047 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_16047 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_3_16055.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_16047 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_16047 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_4_16056.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_16052
                                                                    ; Pvar t256_3_16055
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                ; ccall [:: Lvar buf_16044.(gv)
                          ; Lvar DELTA_16048.(gv)
                          ; Lvar _LEN_16046.(gv) ] A1184____a_ilen_write_upto32 [:: Pvar buf_16044
                                                                    ; Pvar offset_16045
                                                                    ; Pvar DELTA_16048
                                                                    ; Pvar _LEN_16046
                                                                    ; Pvar t256_4_16056 ]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16046))
                    [:: cassgn (Lvar t_16051.(gv)) (aword U64) (Pvar t128_0_16049)
                      ; ccall [:: Lvar buf_16044.(gv)
                                ; Lvar DELTA_16048.(gv)
                                ; Lvar _LEN_16046.(gv) ] A1184____a_ilen_write_upto8 [:: Pvar buf_16044
                                                                    ; Pvar offset_16045
                                                                    ; Pvar DELTA_16048
                                                                    ; Pvar _LEN_16046
                                                                    ; Pvar t_16051 ]
                      ; copn [:: Lvar t128_0_16049.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_16049
                                                                    ; Pvar t128_0_16049 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16046))
                    [:: copn [:: Lvar t256_4_16056.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_16055
                                                                    ; Pvar t256_1_16053
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                      ; ccall [:: Lvar buf_16044.(gv)
                                ; Lvar DELTA_16048.(gv)
                                ; Lvar _LEN_16046.(gv) ] A1184____a_ilen_write_upto32 [:: Pvar buf_16044
                                                                    ; Pvar offset_16045
                                                                    ; Pvar DELTA_16048
                                                                    ; Pvar _LEN_16046
                                                                    ; Pvar t256_4_16056 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16046))
                    [:: cassgn (Lvar t_16051.(gv)) (aword U64) (Pvar t128_1_16050)
                      ; ccall [:: Lvar buf_16044.(gv)
                                ; Lvar DELTA_16048.(gv)
                                ; Lvar _LEN_16046.(gv) ] A1184____a_ilen_write_upto8 [:: Pvar buf_16044
                                                                    ; Pvar offset_16045
                                                                    ; Pvar DELTA_16048
                                                                    ; Pvar _LEN_16046
                                                                    ; Pvar t_16051 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16046))
                    [:: copn [:: Lvar t256_4_16056.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_16054
                                                                    ; Pvar t256_0_16052
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                      ; ccall [:: Lvar buf_16044.(gv)
                                ; Lvar DELTA_16048.(gv)
                                ; Lvar _LEN_16046.(gv) ] A1184____a_ilen_write_upto32 [:: Pvar buf_16044
                                                                    ; Pvar offset_16045
                                                                    ; Pvar DELTA_16048
                                                                    ; Pvar _LEN_16046
                                                                    ; Pvar t256_4_16056 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16046))
                    [:: cassgn (Lvar t_16051.(gv)) (aword U64) (Pvar t128_0_16049)
                      ; ccall [:: Lvar buf_16044.(gv)
                                ; Lvar DELTA_16048.(gv)
                                ; Lvar _LEN_16046.(gv) ] A1184____a_ilen_write_upto8 [:: Pvar buf_16044
                                                                    ; Pvar offset_16045
                                                                    ; Pvar DELTA_16048
                                                                    ; Pvar _LEN_16046
                                                                    ; Pvar t_16051 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16046))
                    [:: copn [:: Lvar t256_4_16056.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_16053
                                                                    ; Pvar t256_2_16054
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                      ; ccall [:: Lvar buf_16044.(gv)
                                ; Lvar DELTA_16048.(gv)
                                ; Lvar _LEN_16046.(gv) ] A1184____a_ilen_write_upto32 [:: Pvar buf_16044
                                                                    ; Pvar offset_16045
                                                                    ; Pvar DELTA_16048
                                                                    ; Pvar _LEN_16046
                                                                    ; Pvar t256_4_16056 ] ]
                    [::] ]
              [::] ]
        [::]
    ; cassgn (Lvar offset_16045.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16045) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16048))) ].

Definition fd_A1184____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____dumpstate_avx2;
    f_params := args_A1184____dumpstate_avx2;
    f_body := body_A1184____dumpstate_avx2;
    f_tyout := tyout_A1184____dumpstate_avx2;
    f_res := res_A1184____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
