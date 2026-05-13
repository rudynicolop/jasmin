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

(* A128____dumpstate_avx2 *)
(* Local variables *)
Definition buf_16426 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16426).
Definition offset_16427 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16427).
Definition _LEN_16428 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16428).
Definition st_16429 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 16429).
Definition DELTA_16430 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16430).
Definition t128_0_16431 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16431).
Definition t128_1_16432 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16432).
Definition t_16433 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16433).
Definition t256_0_16434 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16434).
Definition t256_1_16435 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16435).
Definition t256_2_16436 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16436).
Definition t256_3_16437 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16437).
Definition t256_4_16438 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16438).

(* Signature *)
Definition tyin_A128____dumpstate_avx2 : seq atype :=
  [:: aarr U8 128; aword U64; aint; aarr U256 7 ].
Definition args_A128____dumpstate_avx2 : seq var_i :=
  [:: buf_16426.(gv); offset_16427.(gv); _LEN_16428.(gv); st_16429.(gv) ].
Definition tyout_A128____dumpstate_avx2 : seq atype :=
  [:: aarr U8 128; aword U64 ].
Definition res_A128____dumpstate_avx2 : seq var_i :=
  [:: buf_16426.(gv); offset_16427.(gv) ].

(* Body *)
Definition body_A128____dumpstate_avx2 : cmd :=
  [:: cassgn (Lvar DELTA_16430.(gv)) (aint) (Pconst (0)%Z)
    ; cif
        (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_16428))
        [:: ccall [:: Lvar buf_16426.(gv)
                    ; Lvar DELTA_16430.(gv)
                    ; Lnone dummy_var_info (aint) ] A128____a_ilen_write_upto32 [:: Pvar buf_16426
                                                                    ; Pvar offset_16427
                                                                    ; Pvar DELTA_16430
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_16429 (Pconst (0)%Z) ]
          ; cassgn (Lvar _LEN_16428.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_16428) (Pconst (8)%Z)) ]
        [:: ccall [:: Lvar buf_16426.(gv)
                    ; Lvar DELTA_16430.(gv)
                    ; Lvar _LEN_16428.(gv) ] A128____a_ilen_write_upto32 [:: Pvar buf_16426
                                                                    ; Pvar offset_16427
                                                                    ; Pvar DELTA_16430
                                                                    ; Pvar _LEN_16428
                                                                    ; Pget Aligned AAscale U256 st_16429 (Pconst (0)%Z) ] ]
    ; ccall [:: Lvar buf_16426.(gv)
              ; Lvar DELTA_16430.(gv)
              ; Lvar _LEN_16428.(gv) ] A128____a_ilen_write_upto32 [:: Pvar buf_16426
                                                                    ; Pvar offset_16427
                                                                    ; Pvar DELTA_16430
                                                                    ; Pvar _LEN_16428
                                                                    ; Pget Aligned AAscale U256 st_16429 (Pconst (1)%Z) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16428))
        [:: cassgn (Lvar t128_0_16431.(gv)) (aword U128) (Pget Aligned AAscale U256 st_16429 (Pconst (2)%Z))
          ; copn [:: Lvar t128_1_16432.(gv) ] (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_16429 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
          ; cassgn (Lvar t_16433.(gv)) (aword U64) (Pvar t128_1_16432)
          ; ccall [:: Lvar buf_16426.(gv)
                    ; Lvar DELTA_16430.(gv)
                    ; Lvar _LEN_16428.(gv) ] A128____a_ilen_write_upto8 [:: Pvar buf_16426
                                                                    ; Pvar offset_16427
                                                                    ; Pvar DELTA_16430
                                                                    ; Pvar _LEN_16428
                                                                    ; Pvar t_16433 ]
          ; copn [:: Lvar t128_1_16432.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_16432
                                                                    ; Pvar t128_1_16432 ]
          ; cif
              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16428))
              [:: copn [:: Lvar t256_0_16434.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_16429 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_16429 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_1_16435.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_16429 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_16429 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_2_16436.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_16429 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_16429 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_3_16437.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_16429 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_16429 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_4_16438.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_16434
                                                                    ; Pvar t256_3_16437
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                ; ccall [:: Lvar buf_16426.(gv)
                          ; Lvar DELTA_16430.(gv)
                          ; Lvar _LEN_16428.(gv) ] A128____a_ilen_write_upto32 [:: Pvar buf_16426
                                                                    ; Pvar offset_16427
                                                                    ; Pvar DELTA_16430
                                                                    ; Pvar _LEN_16428
                                                                    ; Pvar t256_4_16438 ]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16428))
                    [:: cassgn (Lvar t_16433.(gv)) (aword U64) (Pvar t128_0_16431)
                      ; ccall [:: Lvar buf_16426.(gv)
                                ; Lvar DELTA_16430.(gv)
                                ; Lvar _LEN_16428.(gv) ] A128____a_ilen_write_upto8 [:: Pvar buf_16426
                                                                    ; Pvar offset_16427
                                                                    ; Pvar DELTA_16430
                                                                    ; Pvar _LEN_16428
                                                                    ; Pvar t_16433 ]
                      ; copn [:: Lvar t128_0_16431.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_16431
                                                                    ; Pvar t128_0_16431 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16428))
                    [:: copn [:: Lvar t256_4_16438.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_16437
                                                                    ; Pvar t256_1_16435
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                      ; ccall [:: Lvar buf_16426.(gv)
                                ; Lvar DELTA_16430.(gv)
                                ; Lvar _LEN_16428.(gv) ] A128____a_ilen_write_upto32 [:: Pvar buf_16426
                                                                    ; Pvar offset_16427
                                                                    ; Pvar DELTA_16430
                                                                    ; Pvar _LEN_16428
                                                                    ; Pvar t256_4_16438 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16428))
                    [:: cassgn (Lvar t_16433.(gv)) (aword U64) (Pvar t128_1_16432)
                      ; ccall [:: Lvar buf_16426.(gv)
                                ; Lvar DELTA_16430.(gv)
                                ; Lvar _LEN_16428.(gv) ] A128____a_ilen_write_upto8 [:: Pvar buf_16426
                                                                    ; Pvar offset_16427
                                                                    ; Pvar DELTA_16430
                                                                    ; Pvar _LEN_16428
                                                                    ; Pvar t_16433 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16428))
                    [:: copn [:: Lvar t256_4_16438.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_16436
                                                                    ; Pvar t256_0_16434
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                      ; ccall [:: Lvar buf_16426.(gv)
                                ; Lvar DELTA_16430.(gv)
                                ; Lvar _LEN_16428.(gv) ] A128____a_ilen_write_upto32 [:: Pvar buf_16426
                                                                    ; Pvar offset_16427
                                                                    ; Pvar DELTA_16430
                                                                    ; Pvar _LEN_16428
                                                                    ; Pvar t256_4_16438 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16428))
                    [:: cassgn (Lvar t_16433.(gv)) (aword U64) (Pvar t128_0_16431)
                      ; ccall [:: Lvar buf_16426.(gv)
                                ; Lvar DELTA_16430.(gv)
                                ; Lvar _LEN_16428.(gv) ] A128____a_ilen_write_upto8 [:: Pvar buf_16426
                                                                    ; Pvar offset_16427
                                                                    ; Pvar DELTA_16430
                                                                    ; Pvar _LEN_16428
                                                                    ; Pvar t_16433 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16428))
                    [:: copn [:: Lvar t256_4_16438.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_16435
                                                                    ; Pvar t256_2_16436
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                      ; ccall [:: Lvar buf_16426.(gv)
                                ; Lvar DELTA_16430.(gv)
                                ; Lvar _LEN_16428.(gv) ] A128____a_ilen_write_upto32 [:: Pvar buf_16426
                                                                    ; Pvar offset_16427
                                                                    ; Pvar DELTA_16430
                                                                    ; Pvar _LEN_16428
                                                                    ; Pvar t256_4_16438 ] ]
                    [::] ]
              [::] ]
        [::]
    ; cassgn (Lvar offset_16427.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16427) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16430))) ].

Definition fd_A128____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____dumpstate_avx2;
    f_params := args_A128____dumpstate_avx2;
    f_body := body_A128____dumpstate_avx2;
    f_tyout := tyout_A128____dumpstate_avx2;
    f_res := res_A128____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
