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

(* A33____addstate_bcast_avx2x4 *)
(* Local variables *)
Definition st_17023 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 17023).
Definition AT_17024 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17024).
Definition buf_17025 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 17025).
Definition offset_17026 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17026).
Definition _LEN_17027 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17027).
Definition _TRAILB_17028 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17028).
Definition DELTA_17029 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17029).
Definition AT8_17030 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17030).
Definition w_17031 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17031).
Definition j_at_17032 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17032).

(* Signature *)
Definition tyin_A33____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 33; aword U64; aint; aint ].
Definition args_A33____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_17023.(gv)
    ; AT_17024.(gv)
    ; buf_17025.(gv)
    ; offset_17026.(gv)
    ; _LEN_17027.(gv)
    ; _TRAILB_17028.(gv) ].
Definition tyout_A33____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A33____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_17023.(gv); AT_17024.(gv); offset_17026.(gv) ].

(* Body *)
Definition body_A33____addstate_bcast_avx2x4 : cmd :=
  [:: cassgn (Lvar DELTA_17029.(gv)) (aint) (Pconst (0)%Z)
    ; cassgn (Lvar AT8_17030.(gv)) (aint) (Pvar AT_17024)
    ; cassgn (Lvar AT_17024.(gv)) (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17024) (Pconst (8)%Z)))
    ; cif
        (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_17030) (Pconst (8)%Z)) (Pconst (0)%Z))
        [:: ccall [:: Lvar DELTA_17029.(gv)
                    ; Lvar _LEN_17027.(gv)
                    ; Lvar _TRAILB_17028.(gv)
                    ; Lvar AT8_17030.(gv)
                    ; Lvar w_17031.(gv) ] A33____a_ilen_read_bcast_upto8_at [:: Pvar buf_17025
                                                                    ; Pvar offset_17026
                                                                    ; Pvar DELTA_17029
                                                                    ; Pvar _LEN_17027
                                                                    ; Pvar _TRAILB_17028
                                                                    ; Pvar AT_17024
                                                                    ; Pvar AT8_17030 ]
          ; cassgn (Lvar w_17031.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_17031) (Pget Aligned AAscale U256 st_17023 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17024) (Pconst (8)%Z))))
          ; cassgn (Laset Aligned AAscale U256 st_17023.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17024) (Pconst (8)%Z))) (aword U256) (Pvar w_17031)
          ; cassgn (Lvar AT_17024.(gv)) (aint) (Pvar AT8_17030) ]
        [::]
    ; cassgn (Lvar offset_17026.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17026) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17029)))
    ; cassgn (Lvar j_at_17032.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17024) (Pconst (8)%Z))))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_17032) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17024) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17027) (Pconst (8)%Z))))))
        [:: copn [:: Lvar w_17031.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_17025 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17026)) ]
          ; cassgn (Lvar offset_17026.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17026) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Lvar w_17031.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_17031) (Pget Unaligned AAdirect U256 st_17023 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17032))))
          ; cassgn (Laset Unaligned AAdirect U256 st_17023.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17032))) (aword U256) (Pvar w_17031)
          ; cassgn (Lvar j_at_17032.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17032) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))) ]
    ; cassgn (Lvar AT_17024.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_17024) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17027) (Pconst (8)%Z))))
    ; cassgn (Lvar _LEN_17027.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17027) (Pconst (8)%Z))
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17027)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_17028) (Pconst (256)%Z)) (Pconst (0)%Z)))
        [:: ccall [:: Lvar DELTA_17029.(gv)
                    ; Lvar _LEN_17027.(gv)
                    ; Lvar _TRAILB_17028.(gv)
                    ; Lvar AT_17024.(gv)
                    ; Lvar w_17031.(gv) ] A33____a_ilen_read_bcast_upto8_at [:: Pvar buf_17025
                                                                    ; Pvar offset_17026
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_17027
                                                                    ; Pvar _TRAILB_17028
                                                                    ; Pvar AT_17024
                                                                    ; Pvar AT_17024 ]
          ; cassgn (Lvar w_17031.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_17031) (Pget Unaligned AAdirect U256 st_17023 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17032))))
          ; cassgn (Laset Unaligned AAdirect U256 st_17023.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_17032))) (aword U256) (Pvar w_17031)
          ; cassgn (Lvar offset_17026.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17026) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17029))) ]
        [::] ].

Definition fd_A33____addstate_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____addstate_bcast_avx2x4;
    f_params := args_A33____addstate_bcast_avx2x4;
    f_body := body_A33____addstate_bcast_avx2x4;
    f_tyout := tyout_A33____addstate_bcast_avx2x4;
    f_res := res_A33____addstate_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
