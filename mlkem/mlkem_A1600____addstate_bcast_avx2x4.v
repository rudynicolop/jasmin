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

(* A1600____addstate_bcast_avx2x4 *)
(* Local variables *)
Definition st_14866 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14866).
Definition AT_14867 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14867).
Definition buf_14868 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14868).
Definition offset_14869 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14869).
Definition _LEN_14870 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14870).
Definition _TRAILB_14871 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14871).
Definition DELTA_14872 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14872).
Definition AT8_14873 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14873).
Definition w_14874 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14874).
Definition j_at_14875 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14875).

(* Signature *)
Definition tyin_A1600____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aarr U8 1600; aword U64; aint; aint ].
Definition args_A1600____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_14866.(gv)
    ; AT_14867.(gv)
    ; buf_14868.(gv)
    ; offset_14869.(gv)
    ; _LEN_14870.(gv)
    ; _TRAILB_14871.(gv) ].
Definition tyout_A1600____addstate_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1600____addstate_bcast_avx2x4 : seq var_i :=
  [:: st_14866.(gv); AT_14867.(gv); offset_14869.(gv) ].

(* Body *)
Definition body_A1600____addstate_bcast_avx2x4 : cmd :=
  [:: cassgn (Lvar DELTA_14872.(gv)) (aint) (Pconst (0)%Z)
    ; cassgn (Lvar AT8_14873.(gv)) (aint) (Pvar AT_14867)
    ; cassgn (Lvar AT_14867.(gv)) (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14867) (Pconst (8)%Z)))
    ; cif
        (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_14873) (Pconst (8)%Z)) (Pconst (0)%Z))
        [:: ccall [:: Lvar DELTA_14872.(gv)
                    ; Lvar _LEN_14870.(gv)
                    ; Lvar _TRAILB_14871.(gv)
                    ; Lvar AT8_14873.(gv)
                    ; Lvar w_14874.(gv) ] A1600____a_ilen_read_bcast_upto8_at [:: Pvar buf_14868
                                                                    ; Pvar offset_14869
                                                                    ; Pvar DELTA_14872
                                                                    ; Pvar _LEN_14870
                                                                    ; Pvar _TRAILB_14871
                                                                    ; Pvar AT_14867
                                                                    ; Pvar AT8_14873 ]
          ; cassgn (Lvar w_14874.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_14874) (Pget Aligned AAscale U256 st_14866 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14867) (Pconst (8)%Z))))
          ; cassgn (Laset Aligned AAscale U256 st_14866.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14867) (Pconst (8)%Z))) (aword U256) (Pvar w_14874)
          ; cassgn (Lvar AT_14867.(gv)) (aint) (Pvar AT8_14873) ]
        [::]
    ; cassgn (Lvar offset_14869.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14869) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14872)))
    ; cassgn (Lvar j_at_14875.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14867) (Pconst (8)%Z))))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_14875) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14867) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14870) (Pconst (8)%Z))))))
        [:: copn [:: Lvar w_14874.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_14868 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14869)) ]
          ; cassgn (Lvar offset_14869.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14869) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Lvar w_14874.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_14874) (Pget Unaligned AAdirect U256 st_14866 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_14875))))
          ; cassgn (Laset Unaligned AAdirect U256 st_14866.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_14875))) (aword U256) (Pvar w_14874)
          ; cassgn (Lvar j_at_14875.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14875) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))) ]
    ; cassgn (Lvar AT_14867.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_14867) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14870) (Pconst (8)%Z))))
    ; cassgn (Lvar _LEN_14870.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14870) (Pconst (8)%Z))
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14870)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_14871) (Pconst (256)%Z)) (Pconst (0)%Z)))
        [:: ccall [:: Lvar DELTA_14872.(gv)
                    ; Lvar _LEN_14870.(gv)
                    ; Lvar _TRAILB_14871.(gv)
                    ; Lvar AT_14867.(gv)
                    ; Lvar w_14874.(gv) ] A1600____a_ilen_read_bcast_upto8_at [:: Pvar buf_14868
                                                                    ; Pvar offset_14869
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_14870
                                                                    ; Pvar _TRAILB_14871
                                                                    ; Pvar AT_14867
                                                                    ; Pvar AT_14867 ]
          ; cassgn (Lvar w_14874.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_14874) (Pget Unaligned AAdirect U256 st_14866 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_14875))))
          ; cassgn (Laset Unaligned AAdirect U256 st_14866.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at_14875))) (aword U256) (Pvar w_14874)
          ; cassgn (Lvar offset_14869.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14869) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14872))) ]
        [::] ].

Definition fd_A1600____addstate_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____addstate_bcast_avx2x4;
    f_params := args_A1600____addstate_bcast_avx2x4;
    f_body := body_A1600____addstate_bcast_avx2x4;
    f_tyout := tyout_A1600____addstate_bcast_avx2x4;
    f_res := res_A1600____addstate_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
