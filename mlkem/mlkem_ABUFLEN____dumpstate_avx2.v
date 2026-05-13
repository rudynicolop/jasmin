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

(* ABUFLEN____dumpstate_avx2 *)
(* Local variables *)
Definition buf_14516 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14516).
Definition offset_14517 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14517).
Definition _LEN_14518 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14518).
Definition st_14519 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 7) (mkident 14519).
Definition DELTA_14520 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14520).
Definition t128_0_14521 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14521).
Definition t128_1_14522 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14522).
Definition t_14523 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14523).
Definition t256_0_14524 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14524).
Definition t256_1_14525 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14525).
Definition t256_2_14526 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14526).
Definition t256_3_14527 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14527).
Definition t256_4_14528 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14528).

(* Signature *)
Definition tyin_ABUFLEN____dumpstate_avx2 : seq atype :=
  [:: aarr U8 536; aword U64; aint; aarr U256 7 ].
Definition args_ABUFLEN____dumpstate_avx2 : seq var_i :=
  [:: buf_14516.(gv); offset_14517.(gv); _LEN_14518.(gv); st_14519.(gv) ].
Definition tyout_ABUFLEN____dumpstate_avx2 : seq atype :=
  [:: aarr U8 536; aword U64 ].
Definition res_ABUFLEN____dumpstate_avx2 : seq var_i :=
  [:: buf_14516.(gv); offset_14517.(gv) ].

(* Body *)
Definition body_ABUFLEN____dumpstate_avx2 : cmd :=
  [:: cassgn (Lvar DELTA_14520.(gv)) (aint) (Pconst (0)%Z)
    ; cif
        (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar _LEN_14518))
        [:: ccall [:: Lvar buf_14516.(gv)
                    ; Lvar DELTA_14520.(gv)
                    ; Lnone dummy_var_info (aint) ] ABUFLEN____a_ilen_write_upto32 [:: Pvar buf_14516
                                                                    ; Pvar offset_14517
                                                                    ; Pvar DELTA_14520
                                                                    ; Pconst (8)%Z
                                                                    ; Pget Aligned AAscale U256 st_14519 (Pconst (0)%Z) ]
          ; cassgn (Lvar _LEN_14518.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar _LEN_14518) (Pconst (8)%Z)) ]
        [:: ccall [:: Lvar buf_14516.(gv)
                    ; Lvar DELTA_14520.(gv)
                    ; Lvar _LEN_14518.(gv) ] ABUFLEN____a_ilen_write_upto32 [:: Pvar buf_14516
                                                                    ; Pvar offset_14517
                                                                    ; Pvar DELTA_14520
                                                                    ; Pvar _LEN_14518
                                                                    ; Pget Aligned AAscale U256 st_14519 (Pconst (0)%Z) ] ]
    ; ccall [:: Lvar buf_14516.(gv)
              ; Lvar DELTA_14520.(gv)
              ; Lvar _LEN_14518.(gv) ] ABUFLEN____a_ilen_write_upto32 [:: Pvar buf_14516
                                                                    ; Pvar offset_14517
                                                                    ; Pvar DELTA_14520
                                                                    ; Pvar _LEN_14518
                                                                    ; Pget Aligned AAscale U256 st_14519 (Pconst (1)%Z) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14518))
        [:: cassgn (Lvar t128_0_14521.(gv)) (aword U128) (Pget Aligned AAscale U256 st_14519 (Pconst (2)%Z))
          ; copn [:: Lvar t128_1_14522.(gv) ] (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pget Aligned AAscale U256 st_14519 (Pconst (2)%Z)
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]
          ; cassgn (Lvar t_14523.(gv)) (aword U64) (Pvar t128_1_14522)
          ; ccall [:: Lvar buf_14516.(gv)
                    ; Lvar DELTA_14520.(gv)
                    ; Lvar _LEN_14518.(gv) ] ABUFLEN____a_ilen_write_upto8 [:: Pvar buf_14516
                                                                    ; Pvar offset_14517
                                                                    ; Pvar DELTA_14520
                                                                    ; Pvar _LEN_14518
                                                                    ; Pvar t_14523 ]
          ; copn [:: Lvar t128_1_14522.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_1_14522
                                                                    ; Pvar t128_1_14522 ]
          ; cif
              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14518))
              [:: copn [:: Lvar t256_0_14524.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_14519 (Pconst (3)%Z)
                                                                    ; Pget Aligned AAscale U256 st_14519 (Pconst (4)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_1_14525.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_14519 (Pconst (4)%Z)
                                                                    ; Pget Aligned AAscale U256 st_14519 (Pconst (3)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_2_14526.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_14519 (Pconst (5)%Z)
                                                                    ; Pget Aligned AAscale U256 st_14519 (Pconst (6)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_3_14527.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pget Aligned AAscale U256 st_14519 (Pconst (6)%Z)
                                                                    ; Pget Aligned AAscale U256 st_14519 (Pconst (5)%Z)
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z ] ]
                ; copn [:: Lvar t256_4_14528.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_0_14524
                                                                    ; Pvar t256_3_14527
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                ; ccall [:: Lvar buf_14516.(gv)
                          ; Lvar DELTA_14520.(gv)
                          ; Lvar _LEN_14518.(gv) ] ABUFLEN____a_ilen_write_upto32 [:: Pvar buf_14516
                                                                    ; Pvar offset_14517
                                                                    ; Pvar DELTA_14520
                                                                    ; Pvar _LEN_14518
                                                                    ; Pvar t256_4_14528 ]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14518))
                    [:: cassgn (Lvar t_14523.(gv)) (aword U64) (Pvar t128_0_14521)
                      ; ccall [:: Lvar buf_14516.(gv)
                                ; Lvar DELTA_14520.(gv)
                                ; Lvar _LEN_14518.(gv) ] ABUFLEN____a_ilen_write_upto8 [:: Pvar buf_14516
                                                                    ; Pvar offset_14517
                                                                    ; Pvar DELTA_14520
                                                                    ; Pvar _LEN_14518
                                                                    ; Pvar t_14523 ]
                      ; copn [:: Lvar t128_0_14521.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar t128_0_14521
                                                                    ; Pvar t128_0_14521 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14518))
                    [:: copn [:: Lvar t256_4_14528.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_3_14527
                                                                    ; Pvar t256_1_14525
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                      ; ccall [:: Lvar buf_14516.(gv)
                                ; Lvar DELTA_14520.(gv)
                                ; Lvar _LEN_14518.(gv) ] ABUFLEN____a_ilen_write_upto32 [:: Pvar buf_14516
                                                                    ; Pvar offset_14517
                                                                    ; Pvar DELTA_14520
                                                                    ; Pvar _LEN_14518
                                                                    ; Pvar t256_4_14528 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14518))
                    [:: cassgn (Lvar t_14523.(gv)) (aword U64) (Pvar t128_1_14522)
                      ; ccall [:: Lvar buf_14516.(gv)
                                ; Lvar DELTA_14520.(gv)
                                ; Lvar _LEN_14518.(gv) ] ABUFLEN____a_ilen_write_upto8 [:: Pvar buf_14516
                                                                    ; Pvar offset_14517
                                                                    ; Pvar DELTA_14520
                                                                    ; Pvar _LEN_14518
                                                                    ; Pvar t_14523 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14518))
                    [:: copn [:: Lvar t256_4_14528.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_2_14526
                                                                    ; Pvar t256_0_14524
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                      ; ccall [:: Lvar buf_14516.(gv)
                                ; Lvar DELTA_14520.(gv)
                                ; Lvar _LEN_14518.(gv) ] ABUFLEN____a_ilen_write_upto32 [:: Pvar buf_14516
                                                                    ; Pvar offset_14517
                                                                    ; Pvar DELTA_14520
                                                                    ; Pvar _LEN_14518
                                                                    ; Pvar t256_4_14528 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14518))
                    [:: cassgn (Lvar t_14523.(gv)) (aword U64) (Pvar t128_0_14521)
                      ; ccall [:: Lvar buf_14516.(gv)
                                ; Lvar DELTA_14520.(gv)
                                ; Lvar _LEN_14518.(gv) ] ABUFLEN____a_ilen_write_upto8 [:: Pvar buf_14516
                                                                    ; Pvar offset_14517
                                                                    ; Pvar DELTA_14520
                                                                    ; Pvar _LEN_14518
                                                                    ; Pvar t_14523 ] ]
                    [::]
                ; cif
                    (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14518))
                    [:: copn [:: Lvar t256_4_14528.(gv) ] (Oasm ((BaseOp ((None), (VPBLEND VE32 U256))))) [:: Pvar t256_1_14525
                                                                    ; Pvar t256_2_14526
                                                                    ; PappN (Opack U8 PE1) [:: Pconst (1)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (0)%Z
                                                                    ; Pconst (1)%Z
                                                                    ; Pconst (1)%Z ] ]
                      ; ccall [:: Lvar buf_14516.(gv)
                                ; Lvar DELTA_14520.(gv)
                                ; Lvar _LEN_14518.(gv) ] ABUFLEN____a_ilen_write_upto32 [:: Pvar buf_14516
                                                                    ; Pvar offset_14517
                                                                    ; Pvar DELTA_14520
                                                                    ; Pvar _LEN_14518
                                                                    ; Pvar t256_4_14528 ] ]
                    [::] ]
              [::] ]
        [::]
    ; cassgn (Lvar offset_14517.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14517) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14520))) ].

Definition fd_ABUFLEN____dumpstate_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____dumpstate_avx2;
    f_params := args_ABUFLEN____dumpstate_avx2;
    f_body := body_ABUFLEN____dumpstate_avx2;
    f_tyout := tyout_ABUFLEN____dumpstate_avx2;
    f_res := res_ABUFLEN____dumpstate_avx2;
    f_extra := tt;
  |}.

End IDO.
