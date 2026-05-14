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

(* A1568____addstate_avx2x4 *)
(* Local variables *)
Definition st_15586 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 15586).
Definition AT_15587 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15587).
Definition buf0_15588 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15588).
Definition buf1_15589 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15589).
Definition buf2_15590 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15590).
Definition buf3_15591 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15591).
Definition offset_15592 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15592).
Definition _LEN_15593 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15593).
Definition _TRAILB_15594 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15594).
Definition DELTA_15595 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15595).
Definition AT8_15596 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15596).
Definition t0_15597 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15597).
Definition t1_15598 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15598).
Definition t2_15599 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15599).
Definition t3_15600 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15600).
Definition j_at_15601 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15601).

(* Signature *)
Definition tyin_A1568____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 1568
    ; aarr U8 1568
    ; aarr U8 1568
    ; aarr U8 1568
    ; aword U64
    ; aint
    ; aint ].
Definition args_A1568____addstate_avx2x4 : seq var_i :=
  [:: st_15586.(gv)
    ; AT_15587.(gv)
    ; buf0_15588.(gv)
    ; buf1_15589.(gv)
    ; buf2_15590.(gv)
    ; buf3_15591.(gv)
    ; offset_15592.(gv)
    ; _LEN_15593.(gv)
    ; _TRAILB_15594.(gv) ].
Definition tyout_A1568____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1568____addstate_avx2x4 : seq var_i :=
  [:: st_15586.(gv); AT_15587.(gv); offset_15592.(gv) ].

(* Body *)
Definition body_A1568____addstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_15595.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_15596.(gv)) AT_none (aint) (Pvar AT_15587))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_15587.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15587) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_15596) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_15597.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf0_15588
                                                                    ; Pvar offset_15592
                                                                    ; Pvar DELTA_15595
                                                                    ; Pvar _LEN_15593
                                                                    ; Pvar _TRAILB_15594
                                                                    ; Pvar AT_15587
                                                                    ; Pvar AT8_15596 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15586.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15587) (Pconst (8)%Z))) (Pconst (0)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15586 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15587) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_15597)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_15598.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf1_15589
                                                                    ; Pvar offset_15592
                                                                    ; Pvar DELTA_15595
                                                                    ; Pvar _LEN_15593
                                                                    ; Pvar _TRAILB_15594
                                                                    ; Pvar AT_15587
                                                                    ; Pvar AT8_15596 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15586.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15587) (Pconst (8)%Z))) (Pconst (1)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15586 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15587) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_15598)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_15599.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf2_15590
                                                                    ; Pvar offset_15592
                                                                    ; Pvar DELTA_15595
                                                                    ; Pvar _LEN_15593
                                                                    ; Pvar _TRAILB_15594
                                                                    ; Pvar AT_15587
                                                                    ; Pvar AT8_15596 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15586.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15587) (Pconst (8)%Z))) (Pconst (2)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15586 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15587) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_15599)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_15595.(gv)
                                                                ; Lvar _LEN_15593.(gv)
                                                                ; Lvar _TRAILB_15594.(gv)
                                                                ; Lvar AT8_15596.(gv)
                                                                ; Lvar t3_15600.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf3_15591
                                                                    ; Pvar offset_15592
                                                                    ; Pvar DELTA_15595
                                                                    ; Pvar _LEN_15593
                                                                    ; Pvar _TRAILB_15594
                                                                    ; Pvar AT_15587
                                                                    ; Pvar AT8_15596 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15586.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15587) (Pconst (8)%Z))) (Pconst (3)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15586 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15587) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_15600)))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_15587.(gv)) AT_none (aint) (Pvar AT8_15596)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_15592.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15592) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15595))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_15601.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15587) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15587) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15593) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_15597.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf0_15588 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15592))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15586.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15586 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_15597)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_15598.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf1_15589 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15592))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15586.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15586 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_15598)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_15599.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf2_15590 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15592))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15586.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15586 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_15599)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_15600.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf3_15591 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15592))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_15592.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15592) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15586.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15586 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_15600)))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_15601.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_15587.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_15587) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15593) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15593.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15593) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15593)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_15594) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_15597.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf0_15588
                                                                    ; Pvar offset_15592
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15593
                                                                    ; Pvar _TRAILB_15594
                                                                    ; Pvar AT_15587
                                                                    ; Pvar AT_15587 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15586.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15586 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_15597)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_15598.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf1_15589
                                                                    ; Pvar offset_15592
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15593
                                                                    ; Pvar _TRAILB_15594
                                                                    ; Pvar AT_15587
                                                                    ; Pvar AT_15587 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15586.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15586 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_15598)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_15599.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf2_15590
                                                                    ; Pvar offset_15592
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15593
                                                                    ; Pvar _TRAILB_15594
                                                                    ; Pvar AT_15587
                                                                    ; Pvar AT_15587 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15586.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15586 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_15599)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_15595.(gv)
                                                                ; Lvar _LEN_15593.(gv)
                                                                ; Lvar _TRAILB_15594.(gv)
                                                                ; Lvar AT_15587.(gv)
                                                                ; Lvar t3_15600.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf3_15591
                                                                    ; Pvar offset_15592
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15593
                                                                    ; Pvar _TRAILB_15594
                                                                    ; Pvar AT_15587
                                                                    ; Pvar AT_15587 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15586.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15586 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15601) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_15600)))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_15592.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15592) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15595)))) ]
                              [::]) ].

Definition fd_A1568____addstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____addstate_avx2x4;
    f_params := args_A1568____addstate_avx2x4;
    f_body := body_A1568____addstate_avx2x4;
    f_tyout := tyout_A1568____addstate_avx2x4;
    f_res := res_A1568____addstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
