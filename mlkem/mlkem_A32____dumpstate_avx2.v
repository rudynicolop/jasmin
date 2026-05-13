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

(* A32____dumpstate_avx2 *)
(* Local variables *)
Definition buf_17437 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17437).
Definition offset_17438 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17438).
Definition _LEN_17439 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17439).
Definition st_17440 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 17440).
Definition DELTA_17441 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17441).
Definition t128_0_17442 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17442).
Definition t128_1_17443 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17443).
Definition t_17444 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17444).
Definition t256_0_17445 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17445).
Definition t256_1_17446 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17446).
Definition t256_2_17447 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17447).
Definition t256_3_17448 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17448).
Definition t256_4_17449 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17449).

(* Signature *)
Definition tyin_A32____dumpstate_avx2 : seq atype :=
  [:: aarr U8 32; aword U64; aint; aarr U256 7 ].
Definition args_A32____dumpstate_avx2 : seq var_i :=
  [:: buf_17437.(gv); offset_17438.(gv); _LEN_17439.(gv); st_17440.(gv) ].
Definition tyout_A32____dumpstate_avx2 : seq atype :=
  [:: aarr U8 32; aword U64 ].
Definition res_A32____dumpstate_avx2 : seq var_i :=
  [:: buf_17437.(gv); offset_17438.(gv) ].

(* Body *)
Definition body_A32____dumpstate_avx2 : cmd :=
  [:: cassgn (Lvar DELTA_17441.(gv)) (aint) (Pconst (0)%Z)
    ; cif
        (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_17439))
        [:: ccall [:: Lvar buf_17437.(gv)
                    ; Lvar DELTA_17441.(gv)
                    ; Lnone dummy_var_info (aint) ] A32____a_ilen_write_upto32 [:: Pvar buf_17437
                                                                    ; Pvar offset_17438
                                                                    ; Pvar DELTA_17441
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_17440 (Pconst (0)%Z) ]
          ; cassgn (Lvar _LEN_17439.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_17439) (Pconst (8)%Z)) ]
        [:: ccall [:: Lvar buf_17437.(gv)
                    ; Lvar DELTA_17441.(gv)
                    ; Lvar _LEN_17439.(gv) ] A32____a_ilen_write_upto32 [:: Pvar buf_17437
                                                                    ; Pvar offset_17438
                                                                    ; Pvar DELTA_17441
                                                                    ; Pvar _LEN_17439
                                                                    ; Pget Aligned AAscale U256 st_17440 (Pconst (0)%Z) ] ]
    ; ccall [:: Lvar buf_17437.(gv)
              ; Lvar DELTA_17441.(gv)
              ; Lvar _LEN_17439.(gv) ] A32____a_ilen_write_upto32 [:: Pvar buf_17437
                                                                    ; Pvar offset_17438
                                                                    ; Pvar DELTA_17441
                                                                    ; Pvar _LEN_17439
                                                                    ; Pget Aligned AAscale U256 st_17440 (Pconst (1)%Z) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17439))
        [:: cassgn (Lvar t128_0_17442.(gv)) (aword U128) (Pget Aligned AAscale U256 st_17440 (Pconst (2)%Z))
          ; copn [:: Lvar t128_1_17443.(gv) ] (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_17440 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
          ; cassgn (Lvar t_17444.(gv)) (aword U64) (Pvar t128_1_17443)
          ; ccall [:: Lvar buf_17437.(gv)
                    ; Lvar DELTA_17441.(gv)
                    ; Lvar _LEN_17439.(gv) ] A32____a_ilen_write_upto8 [:: Pvar buf_17437
                                                                    ; Pvar offset_17438
                                                                    ; Pvar DELTA_17441
                                                                    ; Pvar _LEN_17439
                                                                    ; Pvar t_17444 ]
          ; copn [:: Lvar t128_1_17443.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_17443
                                                                    ; Pvar t128_1_17443 ]
          ; cif
              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17439))
              [:: copn [:: Lvar t256_0_17445.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_17440 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_17440 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_1_17446.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_17440 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_17440 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_2_17447.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_17440 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_17440 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_3_17448.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_17440 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_17440 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_4_17449.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_17445
                                                                    ; Pvar t256_3_17448
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                ; ccall [:: Lvar buf_17437.(gv)
                          ; Lvar DELTA_17441.(gv)
                          ; Lvar _LEN_17439.(gv) ] A32____a_ilen_write_upto32 [:: Pvar buf_17437
                                                                    ; Pvar offset_17438
                                                                    ; Pvar DELTA_17441
                                                                    ; Pvar _LEN_17439
                                                                    ; Pvar t256_4_17449 ]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17439))
                    [:: cassgn (Lvar t_17444.(gv)) (aword U64) (Pvar t128_0_17442)
                      ; ccall [:: Lvar buf_17437.(gv)
                                ; Lvar DELTA_17441.(gv)
                                ; Lvar _LEN_17439.(gv) ] A32____a_ilen_write_upto8 [:: Pvar buf_17437
                                                                    ; Pvar offset_17438
                                                                    ; Pvar DELTA_17441
                                                                    ; Pvar _LEN_17439
                                                                    ; Pvar t_17444 ]
                      ; copn [:: Lvar t128_0_17442.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_17442
                                                                    ; Pvar t128_0_17442 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17439))
                    [:: copn [:: Lvar t256_4_17449.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_17448
                                                                    ; Pvar t256_1_17446
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                      ; ccall [:: Lvar buf_17437.(gv)
                                ; Lvar DELTA_17441.(gv)
                                ; Lvar _LEN_17439.(gv) ] A32____a_ilen_write_upto32 [:: Pvar buf_17437
                                                                    ; Pvar offset_17438
                                                                    ; Pvar DELTA_17441
                                                                    ; Pvar _LEN_17439
                                                                    ; Pvar t256_4_17449 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17439))
                    [:: cassgn (Lvar t_17444.(gv)) (aword U64) (Pvar t128_1_17443)
                      ; ccall [:: Lvar buf_17437.(gv)
                                ; Lvar DELTA_17441.(gv)
                                ; Lvar _LEN_17439.(gv) ] A32____a_ilen_write_upto8 [:: Pvar buf_17437
                                                                    ; Pvar offset_17438
                                                                    ; Pvar DELTA_17441
                                                                    ; Pvar _LEN_17439
                                                                    ; Pvar t_17444 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17439))
                    [:: copn [:: Lvar t256_4_17449.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_17447
                                                                    ; Pvar t256_0_17445
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                      ; ccall [:: Lvar buf_17437.(gv)
                                ; Lvar DELTA_17441.(gv)
                                ; Lvar _LEN_17439.(gv) ] A32____a_ilen_write_upto32 [:: Pvar buf_17437
                                                                    ; Pvar offset_17438
                                                                    ; Pvar DELTA_17441
                                                                    ; Pvar _LEN_17439
                                                                    ; Pvar t256_4_17449 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17439))
                    [:: cassgn (Lvar t_17444.(gv)) (aword U64) (Pvar t128_0_17442)
                      ; ccall [:: Lvar buf_17437.(gv)
                                ; Lvar DELTA_17441.(gv)
                                ; Lvar _LEN_17439.(gv) ] A32____a_ilen_write_upto8 [:: Pvar buf_17437
                                                                    ; Pvar offset_17438
                                                                    ; Pvar DELTA_17441
                                                                    ; Pvar _LEN_17439
                                                                    ; Pvar t_17444 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17439))
                    [:: copn [:: Lvar t256_4_17449.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_17446
                                                                    ; Pvar t256_2_17447
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                      ; ccall [:: Lvar buf_17437.(gv)
                                ; Lvar DELTA_17441.(gv)
                                ; Lvar _LEN_17439.(gv) ] A32____a_ilen_write_upto32 [:: Pvar buf_17437
                                                                    ; Pvar offset_17438
                                                                    ; Pvar DELTA_17441
                                                                    ; Pvar _LEN_17439
                                                                    ; Pvar t256_4_17449 ] ]
                    [::] ]
              [::] ]
        [::]
    ; cassgn (Lvar offset_17438.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17438) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17441))) ].

Definition fd_A32____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____dumpstate_avx2;
    f_params := args_A32____dumpstate_avx2;
    f_body := body_A32____dumpstate_avx2;
    f_tyout := tyout_A32____dumpstate_avx2;
    f_res := res_A32____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
