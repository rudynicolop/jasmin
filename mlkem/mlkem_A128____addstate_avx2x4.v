From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* A128____addstate_avx2x4 *)
(* Local variables *)
Definition st_66 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 16350).
Definition AT_63 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16351).
Definition buf0_19 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16352).
Definition buf1_19 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16353).
Definition buf2_19 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16354).
Definition buf3_19 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16355).
Definition offset_91 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16356).
Definition _LEN_59 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16357).
Definition _TRAILB_35 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16358).
Definition DELTA_62 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16359).
Definition AT8_24 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16360).
Definition t0_14 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16361).
Definition t1_14 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16362).
Definition t2_12 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16363).
Definition t3_12 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16364).
Definition j_at_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16365).

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
  [:: st_66.(gv)
    ; AT_63.(gv)
    ; buf0_19.(gv)
    ; buf1_19.(gv)
    ; buf2_19.(gv)
    ; buf3_19.(gv)
    ; offset_91.(gv)
    ; _LEN_59.(gv)
    ; _TRAILB_35.(gv) ].
Definition tyout_A128____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A128____addstate_avx2x4 : seq var_i :=
  [:: st_66.(gv); AT_63.(gv); offset_91.(gv) ].

(* Body *)
Definition body_A128____addstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_62.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_24.(gv)) AT_none (aint) (Pvar AT_63))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_63.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_63) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_24) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_14.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf0_19
                                                                    ; Pvar offset_91
                                                                    ; Pvar DELTA_62
                                                                    ; Pvar _LEN_59
                                                                    ; Pvar _TRAILB_35
                                                                    ; Pvar AT_63
                                                                    ; Pvar AT8_24 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_66.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_63) (Pconst (8)%Z))) (Pconst (0)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_66 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_63) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_14)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_14.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf1_19
                                                                    ; Pvar offset_91
                                                                    ; Pvar DELTA_62
                                                                    ; Pvar _LEN_59
                                                                    ; Pvar _TRAILB_35
                                                                    ; Pvar AT_63
                                                                    ; Pvar AT8_24 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_66.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_63) (Pconst (8)%Z))) (Pconst (1)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_66 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_63) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_14)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_12.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf2_19
                                                                    ; Pvar offset_91
                                                                    ; Pvar DELTA_62
                                                                    ; Pvar _LEN_59
                                                                    ; Pvar _TRAILB_35
                                                                    ; Pvar AT_63
                                                                    ; Pvar AT8_24 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_66.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_63) (Pconst (8)%Z))) (Pconst (2)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_66 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_63) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_12)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_62.(gv)
                                                                ; Lvar _LEN_59.(gv)
                                                                ; Lvar _TRAILB_35.(gv)
                                                                ; Lvar AT8_24.(gv)
                                                                ; Lvar t3_12.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf3_19
                                                                    ; Pvar offset_91
                                                                    ; Pvar DELTA_62
                                                                    ; Pvar _LEN_59
                                                                    ; Pvar _TRAILB_35
                                                                    ; Pvar AT_63
                                                                    ; Pvar AT8_24 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_66.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_63) (Pconst (8)%Z))) (Pconst (3)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_66 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_63) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_12)))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_63.(gv)) AT_none (aint) (Pvar AT8_24)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_91.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_91) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_62))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_10.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_63) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_63) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_59) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_14.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf0_19 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_91))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_66.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_66 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_14)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_14.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf1_19 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_91))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_66.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_66 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_14)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_12.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf2_19 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_91))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_66.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_66 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_12)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_12.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf3_19 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_91))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_91.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_91) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_66.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_66 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_12)))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_10.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_63.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_63) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_59) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_59.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_59) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_59)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_35) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_14.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf0_19
                                                                    ; Pvar offset_91
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_59
                                                                    ; Pvar _TRAILB_35
                                                                    ; Pvar AT_63
                                                                    ; Pvar AT_63 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_66.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_66 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_14)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_14.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf1_19
                                                                    ; Pvar offset_91
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_59
                                                                    ; Pvar _TRAILB_35
                                                                    ; Pvar AT_63
                                                                    ; Pvar AT_63 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_66.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_66 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_14)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_12.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf2_19
                                                                    ; Pvar offset_91
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_59
                                                                    ; Pvar _TRAILB_35
                                                                    ; Pvar AT_63
                                                                    ; Pvar AT_63 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_66.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_66 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_12)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_62.(gv)
                                                                ; Lvar _LEN_59.(gv)
                                                                ; Lvar _TRAILB_35.(gv)
                                                                ; Lvar AT_63.(gv)
                                                                ; Lvar t3_12.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf3_19
                                                                    ; Pvar offset_91
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_59
                                                                    ; Pvar _TRAILB_35
                                                                    ; Pvar AT_63
                                                                    ; Pvar AT_63 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_66.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_66 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_10) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_12)))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_91.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_91) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_62)))) ]
                              [::]) ].

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
