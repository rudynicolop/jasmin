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

(* A2____addstate_avx2x4 *)
(* Local variables *)
Definition st_32 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 17743).
Definition AT_27 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17744).
Definition buf0_7 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17745).
Definition buf1_7 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17746).
Definition buf2_7 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17747).
Definition buf3_7 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17748).
Definition offset_29 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17749).
Definition _LEN_25 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17750).
Definition _TRAILB_15 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17751).
Definition DELTA_20 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17752).
Definition AT8_10 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17753).
Definition t0_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17754).
Definition t1_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17755).
Definition t2_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17756).
Definition t3_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17757).
Definition j_at_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17758).

(* Signature *)
Definition tyin_A2____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 2
    ; aarr U8 2
    ; aarr U8 2
    ; aarr U8 2
    ; aword U64
    ; aint
    ; aint ].
Definition args_A2____addstate_avx2x4 : seq var_i :=
  [:: st_32.(gv)
    ; AT_27.(gv)
    ; buf0_7.(gv)
    ; buf1_7.(gv)
    ; buf2_7.(gv)
    ; buf3_7.(gv)
    ; offset_29.(gv)
    ; _LEN_25.(gv)
    ; _TRAILB_15.(gv) ].
Definition tyout_A2____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A2____addstate_avx2x4 : seq var_i :=
  [:: st_32.(gv); AT_27.(gv); offset_29.(gv) ].

(* Body *)
Definition body_A2____addstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_20.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_10.(gv)) AT_none (aint) (Pvar AT_27))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_27.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_27) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_10) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_8.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf0_7
                                                                    ; Pvar offset_29
                                                                    ; Pvar DELTA_20
                                                                    ; Pvar _LEN_25
                                                                    ; Pvar _TRAILB_15
                                                                    ; Pvar AT_27
                                                                    ; Pvar AT8_10 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_32.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_27) (Pconst (8)%Z))) (Pconst (0)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_32 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_27) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_8)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_8.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf1_7
                                                                    ; Pvar offset_29
                                                                    ; Pvar DELTA_20
                                                                    ; Pvar _LEN_25
                                                                    ; Pvar _TRAILB_15
                                                                    ; Pvar AT_27
                                                                    ; Pvar AT8_10 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_32.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_27) (Pconst (8)%Z))) (Pconst (1)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_32 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_27) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_8)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_6.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf2_7
                                                                    ; Pvar offset_29
                                                                    ; Pvar DELTA_20
                                                                    ; Pvar _LEN_25
                                                                    ; Pvar _TRAILB_15
                                                                    ; Pvar AT_27
                                                                    ; Pvar AT8_10 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_32.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_27) (Pconst (8)%Z))) (Pconst (2)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_32 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_27) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_6)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_20.(gv)
                                                                ; Lvar _LEN_25.(gv)
                                                                ; Lvar _TRAILB_15.(gv)
                                                                ; Lvar AT8_10.(gv)
                                                                ; Lvar t3_6.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf3_7
                                                                    ; Pvar offset_29
                                                                    ; Pvar DELTA_20
                                                                    ; Pvar _LEN_25
                                                                    ; Pvar _TRAILB_15
                                                                    ; Pvar AT_27
                                                                    ; Pvar AT8_10 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_32.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_27) (Pconst (8)%Z))) (Pconst (3)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_32 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_27) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_6)))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_27.(gv)) AT_none (aint) (Pvar AT8_10)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_29.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_29) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_20))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_4.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_27) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_27) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_25) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_8.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf0_7 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_29))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_32.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_32 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_8)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_8.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf1_7 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_29))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_32.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_32 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_8)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_6.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf2_7 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_29))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_32.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_32 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_6)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_6.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf3_7 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_29))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_29.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_29) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_32.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_32 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_6)))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_4.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_27.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_27) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_25) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_25.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_25) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_25)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_15) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_8.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf0_7
                                                                    ; Pvar offset_29
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_25
                                                                    ; Pvar _TRAILB_15
                                                                    ; Pvar AT_27
                                                                    ; Pvar AT_27 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_32.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_32 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_8)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_8.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf1_7
                                                                    ; Pvar offset_29
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_25
                                                                    ; Pvar _TRAILB_15
                                                                    ; Pvar AT_27
                                                                    ; Pvar AT_27 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_32.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_32 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_8)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_6.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf2_7
                                                                    ; Pvar offset_29
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_25
                                                                    ; Pvar _TRAILB_15
                                                                    ; Pvar AT_27
                                                                    ; Pvar AT_27 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_32.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_32 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_6)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_20.(gv)
                                                                ; Lvar _LEN_25.(gv)
                                                                ; Lvar _TRAILB_15.(gv)
                                                                ; Lvar AT_27.(gv)
                                                                ; Lvar t3_6.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf3_7
                                                                    ; Pvar offset_29
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_25
                                                                    ; Pvar _TRAILB_15
                                                                    ; Pvar AT_27
                                                                    ; Pvar AT_27 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_32.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_32 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_4) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_6)))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_29.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_29) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_20)))) ]
                              [::]) ].

Definition fd_A2____addstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____addstate_avx2x4;
    f_params := args_A2____addstate_avx2x4;
    f_body := body_A2____addstate_avx2x4;
    f_tyout := tyout_A2____addstate_avx2x4;
    f_res := res_A2____addstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
