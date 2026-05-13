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

(* A1600____addstate_avx2x4 *)
(* Local variables *)
Definition st_14822 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14822).
Definition AT_14823 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14823).
Definition buf0_14824 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14824).
Definition buf1_14825 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14825).
Definition buf2_14826 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14826).
Definition buf3_14827 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14827).
Definition offset_14828 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14828).
Definition _LEN_14829 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14829).
Definition _TRAILB_14830 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14830).
Definition DELTA_14831 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14831).
Definition AT8_14832 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14832).
Definition t0_14833 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14833).
Definition t1_14834 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14834).
Definition t2_14835 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14835).
Definition t3_14836 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14836).
Definition j_at_14837 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14837).

(* Signature *)
Definition tyin_A1600____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 1600
    ; aarr U8 1600
    ; aarr U8 1600
    ; aarr U8 1600
    ; aword U64
    ; aint
    ; aint ].
Definition args_A1600____addstate_avx2x4 : seq var_i :=
  [:: st_14822.(gv)
    ; AT_14823.(gv)
    ; buf0_14824.(gv)
    ; buf1_14825.(gv)
    ; buf2_14826.(gv)
    ; buf3_14827.(gv)
    ; offset_14828.(gv)
    ; _LEN_14829.(gv)
    ; _TRAILB_14830.(gv) ].
Definition tyout_A1600____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1600____addstate_avx2x4 : seq var_i :=
  [:: st_14822.(gv); AT_14823.(gv); offset_14828.(gv) ].

(* Body *)
Definition body_A1600____addstate_avx2x4 : cmd :=
  [:: cassgn (Lvar DELTA_14831.(gv)) (aint) (Pconst (0)%Z)
    ; cassgn (Lvar AT8_14832.(gv)) (aint) (Pvar AT_14823)
    ; cassgn (Lvar AT_14823.(gv)) (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14823) (Pconst (8)%Z)))
    ; cif
        (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_14832) (Pconst (8)%Z)) (Pconst (0)%Z))
        [:: ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t0_14833.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf0_14824
                                                                    ; Pvar offset_14828
                                                                    ; Pvar DELTA_14831
                                                                    ; Pvar _LEN_14829
                                                                    ; Pvar _TRAILB_14830
                                                                    ; Pvar AT_14823
                                                                    ; Pvar AT8_14832 ]
          ; cassgn (Laset Aligned AAscale U64 st_14822.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14823) (Pconst (8)%Z))) (Pconst (0)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14822 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14823) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_14833))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t1_14834.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf1_14825
                                                                    ; Pvar offset_14828
                                                                    ; Pvar DELTA_14831
                                                                    ; Pvar _LEN_14829
                                                                    ; Pvar _TRAILB_14830
                                                                    ; Pvar AT_14823
                                                                    ; Pvar AT8_14832 ]
          ; cassgn (Laset Aligned AAscale U64 st_14822.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14823) (Pconst (8)%Z))) (Pconst (1)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14822 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14823) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_14834))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t2_14835.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf2_14826
                                                                    ; Pvar offset_14828
                                                                    ; Pvar DELTA_14831
                                                                    ; Pvar _LEN_14829
                                                                    ; Pvar _TRAILB_14830
                                                                    ; Pvar AT_14823
                                                                    ; Pvar AT8_14832 ]
          ; cassgn (Laset Aligned AAscale U64 st_14822.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14823) (Pconst (8)%Z))) (Pconst (2)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14822 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14823) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_14835))
          ; ccall [:: Lvar DELTA_14831.(gv)
                    ; Lvar _LEN_14829.(gv)
                    ; Lvar _TRAILB_14830.(gv)
                    ; Lvar AT8_14832.(gv)
                    ; Lvar t3_14836.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf3_14827
                                                                    ; Pvar offset_14828
                                                                    ; Pvar DELTA_14831
                                                                    ; Pvar _LEN_14829
                                                                    ; Pvar _TRAILB_14830
                                                                    ; Pvar AT_14823
                                                                    ; Pvar AT8_14832 ]
          ; cassgn (Laset Aligned AAscale U64 st_14822.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14823) (Pconst (8)%Z))) (Pconst (3)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14822 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14823) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_14836))
          ; cassgn (Lvar AT_14823.(gv)) (aint) (Pvar AT8_14832) ]
        [::]
    ; cassgn (Lvar offset_14828.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14828) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14831)))
    ; cassgn (Lvar j_at_14837.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14823) (Pconst (8)%Z))))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14823) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14829) (Pconst (8)%Z))))))
        [:: cassgn (Lvar t0_14833.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf0_14824 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14828)))
          ; cassgn (Laset Aligned AAscale U64 st_14822.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14822 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_14833))
          ; cassgn (Lvar t1_14834.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf1_14825 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14828)))
          ; cassgn (Laset Aligned AAscale U64 st_14822.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14822 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_14834))
          ; cassgn (Lvar t2_14835.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf2_14826 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14828)))
          ; cassgn (Laset Aligned AAscale U64 st_14822.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14822 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_14835))
          ; cassgn (Lvar t3_14836.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf3_14827 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14828)))
          ; cassgn (Lvar offset_14828.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14828) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Laset Aligned AAscale U64 st_14822.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14822 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_14836))
          ; cassgn (Lvar j_at_14837.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))) ]
    ; cassgn (Lvar AT_14823.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_14823) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14829) (Pconst (8)%Z))))
    ; cassgn (Lvar _LEN_14829.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14829) (Pconst (8)%Z))
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14829)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_14830) (Pconst (256)%Z)) (Pconst (0)%Z)))
        [:: ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t0_14833.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf0_14824
                                                                    ; Pvar offset_14828
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_14829
                                                                    ; Pvar _TRAILB_14830
                                                                    ; Pvar AT_14823
                                                                    ; Pvar AT_14823 ]
          ; cassgn (Laset Aligned AAscale U64 st_14822.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14822 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_14833))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t1_14834.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf1_14825
                                                                    ; Pvar offset_14828
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_14829
                                                                    ; Pvar _TRAILB_14830
                                                                    ; Pvar AT_14823
                                                                    ; Pvar AT_14823 ]
          ; cassgn (Laset Aligned AAscale U64 st_14822.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14822 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_14834))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t2_14835.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf2_14826
                                                                    ; Pvar offset_14828
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_14829
                                                                    ; Pvar _TRAILB_14830
                                                                    ; Pvar AT_14823
                                                                    ; Pvar AT_14823 ]
          ; cassgn (Laset Aligned AAscale U64 st_14822.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14822 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_14835))
          ; ccall [:: Lvar DELTA_14831.(gv)
                    ; Lvar _LEN_14829.(gv)
                    ; Lvar _TRAILB_14830.(gv)
                    ; Lvar AT_14823.(gv)
                    ; Lvar t3_14836.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf3_14827
                                                                    ; Pvar offset_14828
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_14829
                                                                    ; Pvar _TRAILB_14830
                                                                    ; Pvar AT_14823
                                                                    ; Pvar AT_14823 ]
          ; cassgn (Laset Aligned AAscale U64 st_14822.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14822 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14837) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_14836))
          ; cassgn (Lvar offset_14828.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14828) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14831))) ]
        [::] ].

Definition fd_A1600____addstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____addstate_avx2x4;
    f_params := args_A1600____addstate_avx2x4;
    f_body := body_A1600____addstate_avx2x4;
    f_tyout := tyout_A1600____addstate_avx2x4;
    f_res := res_A1600____addstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
