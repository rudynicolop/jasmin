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

(* A128____addstate_avx2x4 *)
(* Local variables *)
Definition st_16350 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 16350).
Definition AT_16351 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16351).
Definition buf0_16352 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16352).
Definition buf1_16353 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16353).
Definition buf2_16354 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16354).
Definition buf3_16355 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16355).
Definition offset_16356 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16356).
Definition _LEN_16357 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16357).
Definition _TRAILB_16358 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16358).
Definition DELTA_16359 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16359).
Definition AT8_16360 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16360).
Definition t0_16361 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16361).
Definition t1_16362 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16362).
Definition t2_16363 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16363).
Definition t3_16364 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16364).
Definition j_at_16365 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16365).

(* Signature *)
Definition tyin_A128____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 128
    ; aarr U8 128
    ; aarr U8 128
    ; aarr U8 128
    ; aword U64
    ; aint
    ; aint ].
Definition args_A128____addstate_avx2x4 : seq var_i :=
  [:: st_16350.(gv)
    ; AT_16351.(gv)
    ; buf0_16352.(gv)
    ; buf1_16353.(gv)
    ; buf2_16354.(gv)
    ; buf3_16355.(gv)
    ; offset_16356.(gv)
    ; _LEN_16357.(gv)
    ; _TRAILB_16358.(gv) ].
Definition tyout_A128____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A128____addstate_avx2x4 : seq var_i :=
  [:: st_16350.(gv); AT_16351.(gv); offset_16356.(gv) ].

(* Body *)
Definition body_A128____addstate_avx2x4 : cmd :=
  [:: cassgn (Lvar DELTA_16359.(gv)) (aint) (Pconst (0)%Z)
    ; cassgn (Lvar AT8_16360.(gv)) (aint) (Pvar AT_16351)
    ; cassgn (Lvar AT_16351.(gv)) (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16351) (Pconst (8)%Z)))
    ; cif
        (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_16360) (Pconst (8)%Z)) (Pconst (0)%Z))
        [:: ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t0_16361.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf0_16352
                                                                    ; Pvar offset_16356
                                                                    ; Pvar DELTA_16359
                                                                    ; Pvar _LEN_16357
                                                                    ; Pvar _TRAILB_16358
                                                                    ; Pvar AT_16351
                                                                    ; Pvar AT8_16360 ]
          ; cassgn (Laset Aligned AAscale U64 st_16350.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16351) (Pconst (8)%Z))) (Pconst (0)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16350 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16351) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_16361))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t1_16362.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf1_16353
                                                                    ; Pvar offset_16356
                                                                    ; Pvar DELTA_16359
                                                                    ; Pvar _LEN_16357
                                                                    ; Pvar _TRAILB_16358
                                                                    ; Pvar AT_16351
                                                                    ; Pvar AT8_16360 ]
          ; cassgn (Laset Aligned AAscale U64 st_16350.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16351) (Pconst (8)%Z))) (Pconst (1)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16350 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16351) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_16362))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t2_16363.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf2_16354
                                                                    ; Pvar offset_16356
                                                                    ; Pvar DELTA_16359
                                                                    ; Pvar _LEN_16357
                                                                    ; Pvar _TRAILB_16358
                                                                    ; Pvar AT_16351
                                                                    ; Pvar AT8_16360 ]
          ; cassgn (Laset Aligned AAscale U64 st_16350.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16351) (Pconst (8)%Z))) (Pconst (2)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16350 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16351) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_16363))
          ; ccall [:: Lvar DELTA_16359.(gv)
                    ; Lvar _LEN_16357.(gv)
                    ; Lvar _TRAILB_16358.(gv)
                    ; Lvar AT8_16360.(gv)
                    ; Lvar t3_16364.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf3_16355
                                                                    ; Pvar offset_16356
                                                                    ; Pvar DELTA_16359
                                                                    ; Pvar _LEN_16357
                                                                    ; Pvar _TRAILB_16358
                                                                    ; Pvar AT_16351
                                                                    ; Pvar AT8_16360 ]
          ; cassgn (Laset Aligned AAscale U64 st_16350.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16351) (Pconst (8)%Z))) (Pconst (3)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16350 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16351) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_16364))
          ; cassgn (Lvar AT_16351.(gv)) (aint) (Pvar AT8_16360) ]
        [::]
    ; cassgn (Lvar offset_16356.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16356) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16359)))
    ; cassgn (Lvar j_at_16365.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16351) (Pconst (8)%Z))))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16351) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16357) (Pconst (8)%Z))))))
        [:: cassgn (Lvar t0_16361.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf0_16352 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16356)))
          ; cassgn (Laset Aligned AAscale U64 st_16350.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16350 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_16361))
          ; cassgn (Lvar t1_16362.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf1_16353 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16356)))
          ; cassgn (Laset Aligned AAscale U64 st_16350.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16350 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_16362))
          ; cassgn (Lvar t2_16363.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf2_16354 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16356)))
          ; cassgn (Laset Aligned AAscale U64 st_16350.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16350 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_16363))
          ; cassgn (Lvar t3_16364.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf3_16355 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16356)))
          ; cassgn (Lvar offset_16356.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16356) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Laset Aligned AAscale U64 st_16350.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16350 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_16364))
          ; cassgn (Lvar j_at_16365.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))) ]
    ; cassgn (Lvar AT_16351.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_16351) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16357) (Pconst (8)%Z))))
    ; cassgn (Lvar _LEN_16357.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16357) (Pconst (8)%Z))
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16357)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_16358) (Pconst (256)%Z)) (Pconst (0)%Z)))
        [:: ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t0_16361.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf0_16352
                                                                    ; Pvar offset_16356
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_16357
                                                                    ; Pvar _TRAILB_16358
                                                                    ; Pvar AT_16351
                                                                    ; Pvar AT_16351 ]
          ; cassgn (Laset Aligned AAscale U64 st_16350.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16350 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_16361))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t1_16362.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf1_16353
                                                                    ; Pvar offset_16356
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_16357
                                                                    ; Pvar _TRAILB_16358
                                                                    ; Pvar AT_16351
                                                                    ; Pvar AT_16351 ]
          ; cassgn (Laset Aligned AAscale U64 st_16350.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16350 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_16362))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t2_16363.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf2_16354
                                                                    ; Pvar offset_16356
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_16357
                                                                    ; Pvar _TRAILB_16358
                                                                    ; Pvar AT_16351
                                                                    ; Pvar AT_16351 ]
          ; cassgn (Laset Aligned AAscale U64 st_16350.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16350 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_16363))
          ; ccall [:: Lvar DELTA_16359.(gv)
                    ; Lvar _LEN_16357.(gv)
                    ; Lvar _TRAILB_16358.(gv)
                    ; Lvar AT_16351.(gv)
                    ; Lvar t3_16364.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf3_16355
                                                                    ; Pvar offset_16356
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_16357
                                                                    ; Pvar _TRAILB_16358
                                                                    ; Pvar AT_16351
                                                                    ; Pvar AT_16351 ]
          ; cassgn (Laset Aligned AAscale U64 st_16350.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16350 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16365) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_16364))
          ; cassgn (Lvar offset_16356.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16356) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16359))) ]
        [::] ].

Definition fd_A128____addstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____addstate_avx2x4;
    f_params := args_A128____addstate_avx2x4;
    f_body := body_A128____addstate_avx2x4;
    f_tyout := tyout_A128____addstate_avx2x4;
    f_res := res_A128____addstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
