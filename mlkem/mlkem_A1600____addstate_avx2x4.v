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

(* A1600____addstate_avx2x4 *)
(* Local variables *)
Definition st_106 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14822).
Definition AT_103 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14823).
Definition buf0_35 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14824).
Definition buf1_35 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14825).
Definition buf2_35 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14826).
Definition buf3_35 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14827).
Definition offset_159 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14828).
Definition _LEN_99 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14829).
Definition _TRAILB_59 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14830).
Definition DELTA_106 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14831).
Definition AT8_40 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14832).
Definition t0_22 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14833).
Definition t1_22 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14834).
Definition t2_20 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14835).
Definition t3_20 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14836).
Definition j_at_18 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14837).

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
  [:: st_106.(gv)
    ; AT_103.(gv)
    ; buf0_35.(gv)
    ; buf1_35.(gv)
    ; buf2_35.(gv)
    ; buf3_35.(gv)
    ; offset_159.(gv)
    ; _LEN_99.(gv)
    ; _TRAILB_59.(gv) ].
Definition tyout_A1600____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1600____addstate_avx2x4 : seq var_i :=
  [:: st_106.(gv); AT_103.(gv); offset_159.(gv) ].

(* Body *)
Definition body_A1600____addstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_106.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_40.(gv)) AT_none (aint) (Pvar AT_103))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_103.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_103) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_40) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_22.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf0_35
                                                                    ; Pvar offset_159
                                                                    ; Pvar DELTA_106
                                                                    ; Pvar _LEN_99
                                                                    ; Pvar _TRAILB_59
                                                                    ; Pvar AT_103
                                                                    ; Pvar AT8_40 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_106.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_103) (Pconst (8)%Z))) (Pconst (0)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_106 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_103) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_22)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_22.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf1_35
                                                                    ; Pvar offset_159
                                                                    ; Pvar DELTA_106
                                                                    ; Pvar _LEN_99
                                                                    ; Pvar _TRAILB_59
                                                                    ; Pvar AT_103
                                                                    ; Pvar AT8_40 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_106.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_103) (Pconst (8)%Z))) (Pconst (1)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_106 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_103) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_22)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_20.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf2_35
                                                                    ; Pvar offset_159
                                                                    ; Pvar DELTA_106
                                                                    ; Pvar _LEN_99
                                                                    ; Pvar _TRAILB_59
                                                                    ; Pvar AT_103
                                                                    ; Pvar AT8_40 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_106.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_103) (Pconst (8)%Z))) (Pconst (2)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_106 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_103) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_20)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_106.(gv)
                                                                ; Lvar _LEN_99.(gv)
                                                                ; Lvar _TRAILB_59.(gv)
                                                                ; Lvar AT8_40.(gv)
                                                                ; Lvar t3_20.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf3_35
                                                                    ; Pvar offset_159
                                                                    ; Pvar DELTA_106
                                                                    ; Pvar _LEN_99
                                                                    ; Pvar _TRAILB_59
                                                                    ; Pvar AT_103
                                                                    ; Pvar AT8_40 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_106.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_103) (Pconst (8)%Z))) (Pconst (3)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_106 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_103) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_20)))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_103.(gv)) AT_none (aint) (Pvar AT8_40)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_159.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_159) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_106))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_18.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_103) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_103) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_99) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_22.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf0_35 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_159))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_106.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_106 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_22)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_22.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf1_35 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_159))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_106.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_106 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_22)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_20.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf2_35 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_159))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_106.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_106 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_20)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_20.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf3_35 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_159))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_159.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_159) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_106.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_106 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_20)))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_18.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_103.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_103) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_99) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_99.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_99) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_99)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_59) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_22.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf0_35
                                                                    ; Pvar offset_159
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_99
                                                                    ; Pvar _TRAILB_59
                                                                    ; Pvar AT_103
                                                                    ; Pvar AT_103 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_106.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_106 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_22)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_22.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf1_35
                                                                    ; Pvar offset_159
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_99
                                                                    ; Pvar _TRAILB_59
                                                                    ; Pvar AT_103
                                                                    ; Pvar AT_103 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_106.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_106 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_22)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_20.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf2_35
                                                                    ; Pvar offset_159
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_99
                                                                    ; Pvar _TRAILB_59
                                                                    ; Pvar AT_103
                                                                    ; Pvar AT_103 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_106.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_106 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_20)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_106.(gv)
                                                                ; Lvar _LEN_99.(gv)
                                                                ; Lvar _TRAILB_59.(gv)
                                                                ; Lvar AT_103.(gv)
                                                                ; Lvar t3_20.(gv) ] A1600____a_ilen_read_upto8_at [:: Pvar buf3_35
                                                                    ; Pvar offset_159
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_99
                                                                    ; Pvar _TRAILB_59
                                                                    ; Pvar AT_103
                                                                    ; Pvar AT_103 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_106.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_106 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_20)))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_159.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_159) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_106)))) ]
                              [::]) ].

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
