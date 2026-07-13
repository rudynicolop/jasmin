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

(* A32____addstate_avx2x4 *)
(* Local variables *)
Definition st_42 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 17361).
Definition AT_37 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17362).
Definition buf0_11 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17363).
Definition buf1_11 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17364).
Definition buf2_11 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17365).
Definition buf3_11 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 17366).
Definition offset_46 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17367).
Definition _LEN_35 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17368).
Definition _TRAILB_21 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17369).
Definition DELTA_31 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17370).
Definition AT8_14 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17371).
Definition t0_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17372).
Definition t1_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17373).
Definition t2_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17374).
Definition t3_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17375).
Definition j_at_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17376).

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
  [:: st_42.(gv)
    ; AT_37.(gv)
    ; buf0_11.(gv)
    ; buf1_11.(gv)
    ; buf2_11.(gv)
    ; buf3_11.(gv)
    ; offset_46.(gv)
    ; _LEN_35.(gv)
    ; _TRAILB_21.(gv) ].
Definition tyout_A32____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A32____addstate_avx2x4 : seq var_i :=
  [:: st_42.(gv); AT_37.(gv); offset_46.(gv) ].

(* Body *)
Definition body_A32____addstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_31.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_14.(gv)) AT_none (aint) (Pvar AT_37))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_37.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_37) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_14) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_10.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf0_11
                                                                    ; Pvar offset_46
                                                                    ; Pvar DELTA_31
                                                                    ; Pvar _LEN_35
                                                                    ; Pvar _TRAILB_21
                                                                    ; Pvar AT_37
                                                                    ; Pvar AT8_14 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_42.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_37) (Pconst (8)%Z))) (Pconst (0)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_42 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_37) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_10)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_10.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf1_11
                                                                    ; Pvar offset_46
                                                                    ; Pvar DELTA_31
                                                                    ; Pvar _LEN_35
                                                                    ; Pvar _TRAILB_21
                                                                    ; Pvar AT_37
                                                                    ; Pvar AT8_14 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_42.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_37) (Pconst (8)%Z))) (Pconst (1)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_42 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_37) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_10)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_8.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf2_11
                                                                    ; Pvar offset_46
                                                                    ; Pvar DELTA_31
                                                                    ; Pvar _LEN_35
                                                                    ; Pvar _TRAILB_21
                                                                    ; Pvar AT_37
                                                                    ; Pvar AT8_14 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_42.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_37) (Pconst (8)%Z))) (Pconst (2)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_42 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_37) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_8)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_31.(gv)
                                                                ; Lvar _LEN_35.(gv)
                                                                ; Lvar _TRAILB_21.(gv)
                                                                ; Lvar AT8_14.(gv)
                                                                ; Lvar t3_8.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf3_11
                                                                    ; Pvar offset_46
                                                                    ; Pvar DELTA_31
                                                                    ; Pvar _LEN_35
                                                                    ; Pvar _TRAILB_21
                                                                    ; Pvar AT_37
                                                                    ; Pvar AT8_14 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_42.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_37) (Pconst (8)%Z))) (Pconst (3)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_42 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_37) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_8)))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_37.(gv)) AT_none (aint) (Pvar AT8_14)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_46.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_46) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_31))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_6.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_37) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_37) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_35) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_10.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf0_11 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_46))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_42.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_42 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_10)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_10.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf1_11 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_46))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_42.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_42 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_10)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_8.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf2_11 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_46))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_42.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_42 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_8)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_8.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf3_11 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_46))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_46.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_46) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_42.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_42 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_8)))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_6.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_37.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_37) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_35) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_35.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_35) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_35)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_21) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_10.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf0_11
                                                                    ; Pvar offset_46
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_35
                                                                    ; Pvar _TRAILB_21
                                                                    ; Pvar AT_37
                                                                    ; Pvar AT_37 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_42.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_42 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_10)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_10.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf1_11
                                                                    ; Pvar offset_46
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_35
                                                                    ; Pvar _TRAILB_21
                                                                    ; Pvar AT_37
                                                                    ; Pvar AT_37 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_42.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_42 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_10)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_8.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf2_11
                                                                    ; Pvar offset_46
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_35
                                                                    ; Pvar _TRAILB_21
                                                                    ; Pvar AT_37
                                                                    ; Pvar AT_37 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_42.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_42 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_8)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_31.(gv)
                                                                ; Lvar _LEN_35.(gv)
                                                                ; Lvar _TRAILB_21.(gv)
                                                                ; Lvar AT_37.(gv)
                                                                ; Lvar t3_8.(gv) ] A32____a_ilen_read_upto8_at [:: Pvar buf3_11
                                                                    ; Pvar offset_46
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_35
                                                                    ; Pvar _TRAILB_21
                                                                    ; Pvar AT_37
                                                                    ; Pvar AT_37 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_42.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_42 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_6) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_8)))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_46.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_46) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_31)))) ]
                              [::]) ].

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
