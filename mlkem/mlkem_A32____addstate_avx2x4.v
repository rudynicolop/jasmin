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

(* A32____addstate_avx2x4 *)
(* Local variables *)
Definition st_17361 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 17361).
Definition AT_17362 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17362).
Definition buf0_17363 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17363).
Definition buf1_17364 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17364).
Definition buf2_17365 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17365).
Definition buf3_17366 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 17366).
Definition offset_17367 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17367).
Definition _LEN_17368 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17368).
Definition _TRAILB_17369 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17369).
Definition DELTA_17370 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17370).
Definition AT8_17371 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17371).
Definition t0_17372 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17372).
Definition t1_17373 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17373).
Definition t2_17374 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17374).
Definition t3_17375 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17375).
Definition j_at_17376 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17376).

(* Signature *)
Definition tyin_A32____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 32
    ; aarr U8 32
    ; aarr U8 32
    ; aarr U8 32
    ; aword U64
    ; aint
    ; aint ].
Definition args_A32____addstate_avx2x4 : seq var_i :=
  [:: st_17361.(gv)
    ; AT_17362.(gv)
    ; buf0_17363.(gv)
    ; buf1_17364.(gv)
    ; buf2_17365.(gv)
    ; buf3_17366.(gv)
    ; offset_17367.(gv)
    ; _LEN_17368.(gv)
    ; _TRAILB_17369.(gv) ].
Definition tyout_A32____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A32____addstate_avx2x4 : seq var_i :=
  [:: st_17361.(gv); AT_17362.(gv); offset_17367.(gv) ].

(* Body *)
Definition body_A32____addstate_avx2x4 : cmd :=
  [:: cassgn (Lvar DELTA_17370.(gv)) (aint) (Pconst (0)%Z)
    ; cassgn (Lvar AT8_17371.(gv)) (aint) (Pvar AT_17362)
    ; cassgn (Lvar AT_17362.(gv)) (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17362) (Pconst (8)%Z)))
    ; cif
        (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_17371) (Pconst (8)%Z)) (Pconst (0)%Z))
        [:: ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t0_17372.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf0_17363
                                                                    ; Pvar offset_17367
                                                                    ; Pvar DELTA_17370
                                                                    ; Pvar _LEN_17368
                                                                    ; Pvar _TRAILB_17369
                                                                    ; Pvar AT_17362
                                                                    ; Pvar AT8_17371 ]
          ; cassgn (Laset Aligned AAscale U64 st_17361.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17362) (Pconst (8)%Z))) (Pconst (0)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17361 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17362) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_17372))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t1_17373.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf1_17364
                                                                    ; Pvar offset_17367
                                                                    ; Pvar DELTA_17370
                                                                    ; Pvar _LEN_17368
                                                                    ; Pvar _TRAILB_17369
                                                                    ; Pvar AT_17362
                                                                    ; Pvar AT8_17371 ]
          ; cassgn (Laset Aligned AAscale U64 st_17361.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17362) (Pconst (8)%Z))) (Pconst (1)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17361 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17362) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_17373))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t2_17374.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf2_17365
                                                                    ; Pvar offset_17367
                                                                    ; Pvar DELTA_17370
                                                                    ; Pvar _LEN_17368
                                                                    ; Pvar _TRAILB_17369
                                                                    ; Pvar AT_17362
                                                                    ; Pvar AT8_17371 ]
          ; cassgn (Laset Aligned AAscale U64 st_17361.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17362) (Pconst (8)%Z))) (Pconst (2)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17361 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17362) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_17374))
          ; ccall [:: Lvar DELTA_17370.(gv)
                    ; Lvar _LEN_17368.(gv)
                    ; Lvar _TRAILB_17369.(gv)
                    ; Lvar AT8_17371.(gv)
                    ; Lvar t3_17375.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf3_17366
                                                                    ; Pvar offset_17367
                                                                    ; Pvar DELTA_17370
                                                                    ; Pvar _LEN_17368
                                                                    ; Pvar _TRAILB_17369
                                                                    ; Pvar AT_17362
                                                                    ; Pvar AT8_17371 ]
          ; cassgn (Laset Aligned AAscale U64 st_17361.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17362) (Pconst (8)%Z))) (Pconst (3)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17361 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17362) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_17375))
          ; cassgn (Lvar AT_17362.(gv)) (aint) (Pvar AT8_17371) ]
        [::]
    ; cassgn (Lvar offset_17367.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17367) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17370)))
    ; cassgn (Lvar j_at_17376.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17362) (Pconst (8)%Z))))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17362) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17368) (Pconst (8)%Z))))))
        [:: cassgn (Lvar t0_17372.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf0_17363 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17367)))
          ; cassgn (Laset Aligned AAscale U64 st_17361.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17361 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_17372))
          ; cassgn (Lvar t1_17373.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf1_17364 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17367)))
          ; cassgn (Laset Aligned AAscale U64 st_17361.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17361 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_17373))
          ; cassgn (Lvar t2_17374.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf2_17365 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17367)))
          ; cassgn (Laset Aligned AAscale U64 st_17361.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17361 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_17374))
          ; cassgn (Lvar t3_17375.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf3_17366 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17367)))
          ; cassgn (Lvar offset_17367.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17367) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Laset Aligned AAscale U64 st_17361.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17361 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_17375))
          ; cassgn (Lvar j_at_17376.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))) ]
    ; cassgn (Lvar AT_17362.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_17362) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17368) (Pconst (8)%Z))))
    ; cassgn (Lvar _LEN_17368.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17368) (Pconst (8)%Z))
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17368)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_17369) (Pconst (256)%Z)) (Pconst (0)%Z)))
        [:: ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t0_17372.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf0_17363
                                                                    ; Pvar offset_17367
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_17368
                                                                    ; Pvar _TRAILB_17369
                                                                    ; Pvar AT_17362
                                                                    ; Pvar AT_17362 ]
          ; cassgn (Laset Aligned AAscale U64 st_17361.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17361 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_17372))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t1_17373.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf1_17364
                                                                    ; Pvar offset_17367
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_17368
                                                                    ; Pvar _TRAILB_17369
                                                                    ; Pvar AT_17362
                                                                    ; Pvar AT_17362 ]
          ; cassgn (Laset Aligned AAscale U64 st_17361.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17361 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_17373))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t2_17374.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf2_17365
                                                                    ; Pvar offset_17367
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_17368
                                                                    ; Pvar _TRAILB_17369
                                                                    ; Pvar AT_17362
                                                                    ; Pvar AT_17362 ]
          ; cassgn (Laset Aligned AAscale U64 st_17361.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17361 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_17374))
          ; ccall [:: Lvar DELTA_17370.(gv)
                    ; Lvar _LEN_17368.(gv)
                    ; Lvar _TRAILB_17369.(gv)
                    ; Lvar AT_17362.(gv)
                    ; Lvar t3_17375.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf3_17366
                                                                    ; Pvar offset_17367
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_17368
                                                                    ; Pvar _TRAILB_17369
                                                                    ; Pvar AT_17362
                                                                    ; Pvar AT_17362 ]
          ; cassgn (Laset Aligned AAscale U64 st_17361.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17361 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17376) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_17375))
          ; cassgn (Lvar offset_17367.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17367) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17370))) ]
        [::] ].

Definition fd_A32____addstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A32____addstate_avx2x4;
    f_params := args_A32____addstate_avx2x4;
    f_body := body_A32____addstate_avx2x4;
    f_tyout := tyout_A32____addstate_avx2x4;
    f_res := res_A32____addstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
