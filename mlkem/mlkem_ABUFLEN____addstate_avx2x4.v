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

(* ABUFLEN____addstate_avx2x4 *)
(* Local variables *)
Definition st_116 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 14440).
Definition AT_113 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14441).
Definition buf0_39 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14442).
Definition buf1_39 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14443).
Definition buf2_39 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14444).
Definition buf3_39 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14445).
Definition offset_176 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14446).
Definition _LEN_109 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14447).
Definition _TRAILB_65 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14448).
Definition DELTA_117 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14449).
Definition AT8_44 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14450).
Definition t0_24 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14451).
Definition t1_24 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14452).
Definition t2_22 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14453).
Definition t3_22 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14454).
Definition j_at_20 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14455).

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
  [:: st_116.(gv)
    ; AT_113.(gv)
    ; buf0_39.(gv)
    ; buf1_39.(gv)
    ; buf2_39.(gv)
    ; buf3_39.(gv)
    ; offset_176.(gv)
    ; _LEN_109.(gv)
    ; _TRAILB_65.(gv) ].
Definition tyout_ABUFLEN____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_ABUFLEN____addstate_avx2x4 : seq var_i :=
  [:: st_116.(gv); AT_113.(gv); offset_176.(gv) ].

(* Body *)
Definition body_ABUFLEN____addstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_117.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_44.(gv)) AT_none (aint) (Pvar AT_113))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_113.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_113) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_44) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_24.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf0_39
                                                                    ; Pvar offset_176
                                                                    ; Pvar DELTA_117
                                                                    ; Pvar _LEN_109
                                                                    ; Pvar _TRAILB_65
                                                                    ; Pvar AT_113
                                                                    ; Pvar AT8_44 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_116.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_113) (Pconst (8)%Z))) (Pconst (0)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_116 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_113) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_24)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_24.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf1_39
                                                                    ; Pvar offset_176
                                                                    ; Pvar DELTA_117
                                                                    ; Pvar _LEN_109
                                                                    ; Pvar _TRAILB_65
                                                                    ; Pvar AT_113
                                                                    ; Pvar AT8_44 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_116.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_113) (Pconst (8)%Z))) (Pconst (1)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_116 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_113) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_24)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_22.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf2_39
                                                                    ; Pvar offset_176
                                                                    ; Pvar DELTA_117
                                                                    ; Pvar _LEN_109
                                                                    ; Pvar _TRAILB_65
                                                                    ; Pvar AT_113
                                                                    ; Pvar AT8_44 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_116.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_113) (Pconst (8)%Z))) (Pconst (2)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_116 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_113) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_22)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_117.(gv)
                                                                ; Lvar _LEN_109.(gv)
                                                                ; Lvar _TRAILB_65.(gv)
                                                                ; Lvar AT8_44.(gv)
                                                                ; Lvar t3_22.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf3_39
                                                                    ; Pvar offset_176
                                                                    ; Pvar DELTA_117
                                                                    ; Pvar _LEN_109
                                                                    ; Pvar _TRAILB_65
                                                                    ; Pvar AT_113
                                                                    ; Pvar AT8_44 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_116.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_113) (Pconst (8)%Z))) (Pconst (3)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_116 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_113) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_22)))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_113.(gv)) AT_none (aint) (Pvar AT8_44)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_176.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_176) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_117))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_20.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_113) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_113) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_109) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_24.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf0_39 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_176))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_116.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_116 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_24)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_24.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf1_39 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_176))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_116.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_116 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_24)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_22.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf2_39 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_176))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_116.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_116 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_22)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_22.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf3_39 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_176))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_176.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_176) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_116.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_116 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_22)))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_20.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_113.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_113) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_109) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_109.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_109) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_109)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_65) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_24.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf0_39
                                                                    ; Pvar offset_176
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_109
                                                                    ; Pvar _TRAILB_65
                                                                    ; Pvar AT_113
                                                                    ; Pvar AT_113 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_116.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_116 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_24)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_24.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf1_39
                                                                    ; Pvar offset_176
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_109
                                                                    ; Pvar _TRAILB_65
                                                                    ; Pvar AT_113
                                                                    ; Pvar AT_113 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_116.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_116 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_24)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_22.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf2_39
                                                                    ; Pvar offset_176
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_109
                                                                    ; Pvar _TRAILB_65
                                                                    ; Pvar AT_113
                                                                    ; Pvar AT_113 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_116.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_116 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_22)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_117.(gv)
                                                                ; Lvar _LEN_109.(gv)
                                                                ; Lvar _TRAILB_65.(gv)
                                                                ; Lvar AT_113.(gv)
                                                                ; Lvar t3_22.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf3_39
                                                                    ; Pvar offset_176
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_109
                                                                    ; Pvar _TRAILB_65
                                                                    ; Pvar AT_113
                                                                    ; Pvar AT_113 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_116.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_116 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_20) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_22)))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_176.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_176) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_117)))) ]
                              [::]) ].

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
