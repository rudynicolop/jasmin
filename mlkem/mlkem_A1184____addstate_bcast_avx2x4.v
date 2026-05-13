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

(* A1184____addstate_bcast_avx2x4 *)
(* Local variables *)
Definition st_16012 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 16012).
Definition AT_16013 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16013).
Definition buf_16014 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16014).
Definition offset_16015 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16015).
Definition _LEN_16016 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16016).
Definition _TRAILB_16017 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16017).
Definition DELTA_16018 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16018).
Definition AT8_16019 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16019).
Definition w_16020 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16020).
Definition j_at_16021 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16021).

(* Signature *)
Definition tyin_A1184____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 1184; aword U64; aint; aint ].
Definition args_A1184____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_16012.(gv)
    ; AT_16013.(gv)
    ; buf_16014.(gv)
    ; offset_16015.(gv)
    ; _LEN_16016.(gv)
    ; _TRAILB_16017.(gv) ].
Definition tyout_A1184____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1184____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_16012.(gv); AT_16013.(gv); offset_16015.(gv) ].

(* Body *)
Definition body_A1184____addstate_bcast_avx2x4 : cmd :=
  [:: cassgn (Lvar DELTA_16018.(gv)) (aint) (Pconst (0)%Z)
    ; cassgn (Lvar AT8_16019.(gv)) (aint) (Pvar AT_16013)
    ; cassgn (Lvar AT_16013.(gv)) (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16013) (Pconst (8)%Z)))
    ; cif
        (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_16019) (Pconst (8)%Z)) (Pconst (0)%Z))
        [:: ccall [:: Lvar DELTA_16018.(gv)
                    ; Lvar _LEN_16016.(gv)
                    ; Lvar _TRAILB_16017.(gv)
                    ; Lvar AT8_16019.(gv)
                    ; Lvar w_16020.(gv) ] A1184____a_ilen_read_bcast_upto8_at [:: Pvar buf_16014
                                                                    ; Pvar offset_16015
                                                                    ; Pvar DELTA_16018
                                                                    ; Pvar _LEN_16016
                                                                    ; Pvar _TRAILB_16017
                                                                    ; Pvar AT_16013
                                                                    ; Pvar AT8_16019 ]
          ; cassgn (Lvar w_16020.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_16020) (Pget Aligned AAscale U256 st_16012 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16013) (Pconst (8)%Z))))
          ; cassgn (Laset Aligned AAscale U256 st_16012.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16013) (Pconst (8)%Z))) (aword U256) (Pvar w_16020)
          ; cassgn (Lvar AT_16013.(gv)) (aint) (Pvar AT8_16019) ]
        [::]
    ; cassgn (Lvar offset_16015.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16015) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16018)))
    ; cassgn (Lvar j_at_16021.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16013) (Pconst (8)%Z))))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_16021) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16013) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16016) (Pconst (8)%Z))))))
        [:: copn [:: Lvar w_16020.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_16014 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16015)) ]
          ; cassgn (Lvar offset_16015.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16015) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Lvar w_16020.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_16020) (Pget Unaligned AAdirect U256 st_16012 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_16021))))
          ; cassgn (Laset Unaligned AAdirect U256 st_16012.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_16021))) (aword U256) (Pvar w_16020)
          ; cassgn (Lvar j_at_16021.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16021) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))) ]
    ; cassgn (Lvar AT_16013.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_16013) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16016) (Pconst (8)%Z))))
    ; cassgn (Lvar _LEN_16016.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16016) (Pconst (8)%Z))
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16016)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_16017) (Pconst (256)%Z)) (Pconst (0)%Z)))
        [:: ccall [:: Lvar DELTA_16018.(gv)
                    ; Lvar _LEN_16016.(gv)
                    ; Lvar _TRAILB_16017.(gv)
                    ; Lvar AT_16013.(gv)
                    ; Lvar w_16020.(gv) ] A1184____a_ilen_read_bcast_upto8_at [:: Pvar buf_16014
                                                                    ; Pvar offset_16015
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_16016
                                                                    ; Pvar _TRAILB_16017
                                                                    ; Pvar AT_16013
                                                                    ; Pvar AT_16013 ]
          ; cassgn (Lvar w_16020.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_16020) (Pget Unaligned AAdirect U256 st_16012 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_16021))))
          ; cassgn (Laset Unaligned AAdirect U256 st_16012.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_16021))) (aword U256) (Pvar w_16020)
          ; cassgn (Lvar offset_16015.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16015) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16018))) ]
        [::] ].

Definition fd_A1184____addstate_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____addstate_bcast_avx2x4;
    f_params := args_A1184____addstate_bcast_avx2x4;
    f_body := body_A1184____addstate_bcast_avx2x4;
    f_tyout := tyout_A1184____addstate_bcast_avx2x4;
    f_res := res_A1184____addstate_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
