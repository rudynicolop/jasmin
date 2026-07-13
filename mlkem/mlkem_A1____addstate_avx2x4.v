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

(* A1____addstate_avx2x4 *)
(* Local variables *)
Definition st_22 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18125).
Definition AT_17 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18126).
Definition buf0_3 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18127).
Definition buf1_3 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18128).
Definition buf2_3 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18129).
Definition buf3_3 : gvar := mk_rocq_gvar Slocal (aarr U8 1) (mkident 18130).
Definition offset_12 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18131).
Definition _LEN_15 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18132).
Definition _TRAILB_9 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18133).
Definition DELTA_9 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18134).
Definition AT8_6 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18135).
Definition t0_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18136).
Definition t1_6 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18137).
Definition t2_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18138).
Definition t3_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18139).
Definition j_at_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18140).

(* Signature *)
Definition tyin_A1____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 1
    ; aarr U8 1
    ; aarr U8 1
    ; aarr U8 1
    ; aword U64
    ; aint
    ; aint ].
Definition args_A1____addstate_avx2x4 : seq var_i :=
  [:: st_22.(gv)
    ; AT_17.(gv)
    ; buf0_3.(gv)
    ; buf1_3.(gv)
    ; buf2_3.(gv)
    ; buf3_3.(gv)
    ; offset_12.(gv)
    ; _LEN_15.(gv)
    ; _TRAILB_9.(gv) ].
Definition tyout_A1____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1____addstate_avx2x4 : seq var_i :=
  [:: st_22.(gv); AT_17.(gv); offset_12.(gv) ].

(* Body *)
Definition body_A1____addstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_9.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_6.(gv)) AT_none (aint) (Pvar AT_17))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_17.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_6) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_6.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf0_3
                                                                    ; Pvar offset_12
                                                                    ; Pvar DELTA_9
                                                                    ; Pvar _LEN_15
                                                                    ; Pvar _TRAILB_9
                                                                    ; Pvar AT_17
                                                                    ; Pvar AT8_6 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_22.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17) (Pconst (8)%Z))) (Pconst (0)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_22 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_6)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_6.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf1_3
                                                                    ; Pvar offset_12
                                                                    ; Pvar DELTA_9
                                                                    ; Pvar _LEN_15
                                                                    ; Pvar _TRAILB_9
                                                                    ; Pvar AT_17
                                                                    ; Pvar AT8_6 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_22.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17) (Pconst (8)%Z))) (Pconst (1)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_22 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_6)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_4.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf2_3
                                                                    ; Pvar offset_12
                                                                    ; Pvar DELTA_9
                                                                    ; Pvar _LEN_15
                                                                    ; Pvar _TRAILB_9
                                                                    ; Pvar AT_17
                                                                    ; Pvar AT8_6 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_22.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17) (Pconst (8)%Z))) (Pconst (2)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_22 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_4)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_9.(gv)
                                                                ; Lvar _LEN_15.(gv)
                                                                ; Lvar _TRAILB_9.(gv)
                                                                ; Lvar AT8_6.(gv)
                                                                ; Lvar t3_4.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf3_3
                                                                    ; Pvar offset_12
                                                                    ; Pvar DELTA_9
                                                                    ; Pvar _LEN_15
                                                                    ; Pvar _TRAILB_9
                                                                    ; Pvar AT_17
                                                                    ; Pvar AT8_6 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_22.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17) (Pconst (8)%Z))) (Pconst (3)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_22 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_4)))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_17.(gv)) AT_none (aint) (Pvar AT8_6)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_12.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_9))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_2.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_6.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf0_3 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_12))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_22.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_22 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_6)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_6.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf1_3 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_12))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_22.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_22 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_6)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_4.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf2_3 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_12))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_22.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_22 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_4)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_4.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf3_3 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_12))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_12.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_22.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_22 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_4)))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_2.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_17.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_17) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_9) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_6.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf0_3
                                                                    ; Pvar offset_12
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15
                                                                    ; Pvar _TRAILB_9
                                                                    ; Pvar AT_17
                                                                    ; Pvar AT_17 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_22.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_22 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_6)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_6.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf1_3
                                                                    ; Pvar offset_12
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15
                                                                    ; Pvar _TRAILB_9
                                                                    ; Pvar AT_17
                                                                    ; Pvar AT_17 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_22.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_22 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_6)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_4.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf2_3
                                                                    ; Pvar offset_12
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15
                                                                    ; Pvar _TRAILB_9
                                                                    ; Pvar AT_17
                                                                    ; Pvar AT_17 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_22.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_22 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_4)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_9.(gv)
                                                                ; Lvar _LEN_15.(gv)
                                                                ; Lvar _TRAILB_9.(gv)
                                                                ; Lvar AT_17.(gv)
                                                                ; Lvar t3_4.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf3_3
                                                                    ; Pvar offset_12
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15
                                                                    ; Pvar _TRAILB_9
                                                                    ; Pvar AT_17
                                                                    ; Pvar AT_17 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_22.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_22 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_4)))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_12.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_9)))) ]
                              [::]) ].

Definition fd_A1____addstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____addstate_avx2x4;
    f_params := args_A1____addstate_avx2x4;
    f_body := body_A1____addstate_avx2x4;
    f_tyout := tyout_A1____addstate_avx2x4;
    f_res := res_A1____addstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
