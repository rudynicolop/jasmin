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

(* A128____addstate_bcast_avx2x4 *)
(* Local variables *)
Definition st_16394 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 16394).
Definition AT_16395 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16395).
Definition buf_16396 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16396).
Definition offset_16397 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16397).
Definition _LEN_16398 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16398).
Definition _TRAILB_16399 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16399).
Definition DELTA_16400 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16400).
Definition AT8_16401 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16401).
Definition w_16402 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16402).
Definition j_at_16403 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16403).

(* Signature *)
Definition tyin_A128____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 128; aword U64; aint; aint ].
Definition args_A128____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_16394.(gv)
    ; AT_16395.(gv)
    ; buf_16396.(gv)
    ; offset_16397.(gv)
    ; _LEN_16398.(gv)
    ; _TRAILB_16399.(gv) ].
Definition tyout_A128____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A128____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_16394.(gv); AT_16395.(gv); offset_16397.(gv) ].

(* Body *)
Definition body_A128____addstate_bcast_avx2x4 : cmd :=
  [:: cassgn (Lvar DELTA_16400.(gv)) (aint) (Pconst (0)%Z)
    ; cassgn (Lvar AT8_16401.(gv)) (aint) (Pvar AT_16395)
    ; cassgn (Lvar AT_16395.(gv)) (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16395) (Pconst (8)%Z)))
    ; cif
        (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_16401) (Pconst (8)%Z)) (Pconst (0)%Z))
        [:: ccall [:: Lvar DELTA_16400.(gv)
                    ; Lvar _LEN_16398.(gv)
                    ; Lvar _TRAILB_16399.(gv)
                    ; Lvar AT8_16401.(gv)
                    ; Lvar w_16402.(gv) ] A128____a_ilen_read_bcast_upto8_at [:: Pvar buf_16396
                                                                    ; Pvar offset_16397
                                                                    ; Pvar DELTA_16400
                                                                    ; Pvar _LEN_16398
                                                                    ; Pvar _TRAILB_16399
                                                                    ; Pvar AT_16395
                                                                    ; Pvar AT8_16401 ]
          ; cassgn (Lvar w_16402.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_16402) (Pget Aligned AAscale U256 st_16394 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16395) (Pconst (8)%Z))))
          ; cassgn (Laset Aligned AAscale U256 st_16394.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16395) (Pconst (8)%Z))) (aword U256) (Pvar w_16402)
          ; cassgn (Lvar AT_16395.(gv)) (aint) (Pvar AT8_16401) ]
        [::]
    ; cassgn (Lvar offset_16397.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16397) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16400)))
    ; cassgn (Lvar j_at_16403.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16395) (Pconst (8)%Z))))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_16403) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16395) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16398) (Pconst (8)%Z))))))
        [:: copn [:: Lvar w_16402.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_16396 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16397)) ]
          ; cassgn (Lvar offset_16397.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16397) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Lvar w_16402.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_16402) (Pget Unaligned AAdirect U256 st_16394 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_16403))))
          ; cassgn (Laset Unaligned AAdirect U256 st_16394.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_16403))) (aword U256) (Pvar w_16402)
          ; cassgn (Lvar j_at_16403.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16403) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))) ]
    ; cassgn (Lvar AT_16395.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_16395) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16398) (Pconst (8)%Z))))
    ; cassgn (Lvar _LEN_16398.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16398) (Pconst (8)%Z))
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16398)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_16399) (Pconst (256)%Z)) (Pconst (0)%Z)))
        [:: ccall [:: Lvar DELTA_16400.(gv)
                    ; Lvar _LEN_16398.(gv)
                    ; Lvar _TRAILB_16399.(gv)
                    ; Lvar AT_16395.(gv)
                    ; Lvar w_16402.(gv) ] A128____a_ilen_read_bcast_upto8_at [:: Pvar buf_16396
                                                                    ; Pvar offset_16397
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_16398
                                                                    ; Pvar _TRAILB_16399
                                                                    ; Pvar AT_16395
                                                                    ; Pvar AT_16395 ]
          ; cassgn (Lvar w_16402.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_16402) (Pget Unaligned AAdirect U256 st_16394 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_16403))))
          ; cassgn (Laset Unaligned AAdirect U256 st_16394.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_16403))) (aword U256) (Pvar w_16402)
          ; cassgn (Lvar offset_16397.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16397) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16400))) ]
        [::] ].

Definition fd_A128____addstate_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____addstate_bcast_avx2x4;
    f_params := args_A128____addstate_bcast_avx2x4;
    f_body := body_A128____addstate_bcast_avx2x4;
    f_tyout := tyout_A128____addstate_bcast_avx2x4;
    f_res := res_A128____addstate_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
