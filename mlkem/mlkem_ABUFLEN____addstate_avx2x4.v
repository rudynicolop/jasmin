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

(* ABUFLEN____addstate_avx2x4 *)
(* Local variables *)
Definition st_14440 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14440).
Definition AT_14441 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14441).
Definition buf0_14442 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14442).
Definition buf1_14443 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14443).
Definition buf2_14444 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14444).
Definition buf3_14445 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14445).
Definition offset_14446 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14446).
Definition _LEN_14447 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14447).
Definition _TRAILB_14448 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14448).
Definition DELTA_14449 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14449).
Definition AT8_14450 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14450).
Definition t0_14451 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14451).
Definition t1_14452 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14452).
Definition t2_14453 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14453).
Definition t3_14454 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14454).
Definition j_at_14455 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14455).

(* Signature *)
Definition tyin_ABUFLEN____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 536
    ; aarr U8 536
    ; aarr U8 536
    ; aarr U8 536
    ; aword U64
    ; aint
    ; aint ].
Definition args_ABUFLEN____addstate_avx2x4 : seq var_i :=
  [:: st_14440.(gv)
    ; AT_14441.(gv)
    ; buf0_14442.(gv)
    ; buf1_14443.(gv)
    ; buf2_14444.(gv)
    ; buf3_14445.(gv)
    ; offset_14446.(gv)
    ; _LEN_14447.(gv)
    ; _TRAILB_14448.(gv) ].
Definition tyout_ABUFLEN____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_ABUFLEN____addstate_avx2x4 : seq var_i :=
  [:: st_14440.(gv); AT_14441.(gv); offset_14446.(gv) ].

(* Body *)
Definition body_ABUFLEN____addstate_avx2x4 : cmd :=
  [:: cassgn (Lvar DELTA_14449.(gv)) (aint) (Pconst (0)%Z)
    ; cassgn (Lvar AT8_14450.(gv)) (aint) (Pvar AT_14441)
    ; cassgn (Lvar AT_14441.(gv)) (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14441) (Pconst (8)%Z)))
    ; cif
        (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_14450) (Pconst (8)%Z)) (Pconst (0)%Z))
        [:: ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t0_14451.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf0_14442
                                                                    ; Pvar offset_14446
                                                                    ; Pvar DELTA_14449
                                                                    ; Pvar _LEN_14447
                                                                    ; Pvar _TRAILB_14448
                                                                    ; Pvar AT_14441
                                                                    ; Pvar AT8_14450 ]
          ; cassgn (Laset Aligned AAscale U64 st_14440.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14441) (Pconst (8)%Z))) (Pconst (0)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14440 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14441) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_14451))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t1_14452.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf1_14443
                                                                    ; Pvar offset_14446
                                                                    ; Pvar DELTA_14449
                                                                    ; Pvar _LEN_14447
                                                                    ; Pvar _TRAILB_14448
                                                                    ; Pvar AT_14441
                                                                    ; Pvar AT8_14450 ]
          ; cassgn (Laset Aligned AAscale U64 st_14440.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14441) (Pconst (8)%Z))) (Pconst (1)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14440 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14441) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_14452))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t2_14453.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf2_14444
                                                                    ; Pvar offset_14446
                                                                    ; Pvar DELTA_14449
                                                                    ; Pvar _LEN_14447
                                                                    ; Pvar _TRAILB_14448
                                                                    ; Pvar AT_14441
                                                                    ; Pvar AT8_14450 ]
          ; cassgn (Laset Aligned AAscale U64 st_14440.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14441) (Pconst (8)%Z))) (Pconst (2)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14440 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14441) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_14453))
          ; ccall [:: Lvar DELTA_14449.(gv)
                    ; Lvar _LEN_14447.(gv)
                    ; Lvar _TRAILB_14448.(gv)
                    ; Lvar AT8_14450.(gv)
                    ; Lvar t3_14454.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf3_14445
                                                                    ; Pvar offset_14446
                                                                    ; Pvar DELTA_14449
                                                                    ; Pvar _LEN_14447
                                                                    ; Pvar _TRAILB_14448
                                                                    ; Pvar AT_14441
                                                                    ; Pvar AT8_14450 ]
          ; cassgn (Laset Aligned AAscale U64 st_14440.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14441) (Pconst (8)%Z))) (Pconst (3)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14440 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14441) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_14454))
          ; cassgn (Lvar AT_14441.(gv)) (aint) (Pvar AT8_14450) ]
        [::]
    ; cassgn (Lvar offset_14446.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14446) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14449)))
    ; cassgn (Lvar j_at_14455.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14441) (Pconst (8)%Z))))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_14441) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14447) (Pconst (8)%Z))))))
        [:: cassgn (Lvar t0_14451.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf0_14442 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14446)))
          ; cassgn (Laset Aligned AAscale U64 st_14440.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14440 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_14451))
          ; cassgn (Lvar t1_14452.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf1_14443 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14446)))
          ; cassgn (Laset Aligned AAscale U64 st_14440.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14440 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_14452))
          ; cassgn (Lvar t2_14453.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf2_14444 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14446)))
          ; cassgn (Laset Aligned AAscale U64 st_14440.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14440 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_14453))
          ; cassgn (Lvar t3_14454.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf3_14445 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_14446)))
          ; cassgn (Lvar offset_14446.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14446) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Laset Aligned AAscale U64 st_14440.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14440 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_14454))
          ; cassgn (Lvar j_at_14455.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))) ]
    ; cassgn (Lvar AT_14441.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_14441) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_14447) (Pconst (8)%Z))))
    ; cassgn (Lvar _LEN_14447.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_14447) (Pconst (8)%Z))
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_14447)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_14448) (Pconst (256)%Z)) (Pconst (0)%Z)))
        [:: ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t0_14451.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf0_14442
                                                                    ; Pvar offset_14446
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_14447
                                                                    ; Pvar _TRAILB_14448
                                                                    ; Pvar AT_14441
                                                                    ; Pvar AT_14441 ]
          ; cassgn (Laset Aligned AAscale U64 st_14440.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14440 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_14451))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t1_14452.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf1_14443
                                                                    ; Pvar offset_14446
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_14447
                                                                    ; Pvar _TRAILB_14448
                                                                    ; Pvar AT_14441
                                                                    ; Pvar AT_14441 ]
          ; cassgn (Laset Aligned AAscale U64 st_14440.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14440 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_14452))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t2_14453.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf2_14444
                                                                    ; Pvar offset_14446
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_14447
                                                                    ; Pvar _TRAILB_14448
                                                                    ; Pvar AT_14441
                                                                    ; Pvar AT_14441 ]
          ; cassgn (Laset Aligned AAscale U64 st_14440.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14440 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_14453))
          ; ccall [:: Lvar DELTA_14449.(gv)
                    ; Lvar _LEN_14447.(gv)
                    ; Lvar _TRAILB_14448.(gv)
                    ; Lvar AT_14441.(gv)
                    ; Lvar t3_14454.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf3_14445
                                                                    ; Pvar offset_14446
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_14447
                                                                    ; Pvar _TRAILB_14448
                                                                    ; Pvar AT_14441
                                                                    ; Pvar AT_14441 ]
          ; cassgn (Laset Aligned AAscale U64 st_14440.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_14440 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_14455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_14454))
          ; cassgn (Lvar offset_14446.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14446) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14449))) ]
        [::] ].

Definition fd_ABUFLEN____addstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____addstate_avx2x4;
    f_params := args_ABUFLEN____addstate_avx2x4;
    f_body := body_ABUFLEN____addstate_avx2x4;
    f_tyout := tyout_ABUFLEN____addstate_avx2x4;
    f_res := res_ABUFLEN____addstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
