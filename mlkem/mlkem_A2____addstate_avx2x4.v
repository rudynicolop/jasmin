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
Definition st_17743 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 17743).
Definition AT_17744 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17744).
Definition buf0_17745 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17745).
Definition buf1_17746 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17746).
Definition buf2_17747 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17747).
Definition buf3_17748 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17748).
Definition offset_17749 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17749).
Definition _LEN_17750 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17750).
Definition _TRAILB_17751 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17751).
Definition DELTA_17752 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17752).
Definition AT8_17753 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17753).
Definition t0_17754 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17754).
Definition t1_17755 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17755).
Definition t2_17756 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17756).
Definition t3_17757 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17757).
Definition j_at_17758 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17758).

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
  [:: st_17743.(gv)
    ; AT_17744.(gv)
    ; buf0_17745.(gv)
    ; buf1_17746.(gv)
    ; buf2_17747.(gv)
    ; buf3_17748.(gv)
    ; offset_17749.(gv)
    ; _LEN_17750.(gv)
    ; _TRAILB_17751.(gv) ].
Definition tyout_A2____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A2____addstate_avx2x4 : seq var_i :=
  [:: st_17743.(gv); AT_17744.(gv); offset_17749.(gv) ].

(* Body *)
Definition body_A2____addstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_17752.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_17753.(gv)) AT_none (aint) (Pvar AT_17744))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_17744.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17744) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_17753) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_17754.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf0_17745
                                                                    ; Pvar offset_17749
                                                                    ; Pvar DELTA_17752
                                                                    ; Pvar _LEN_17750
                                                                    ; Pvar _TRAILB_17751
                                                                    ; Pvar AT_17744
                                                                    ; Pvar AT8_17753 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_17743.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17744) (Pconst (8)%Z))) (Pconst (0)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17743 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17744) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_17754)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_17755.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf1_17746
                                                                    ; Pvar offset_17749
                                                                    ; Pvar DELTA_17752
                                                                    ; Pvar _LEN_17750
                                                                    ; Pvar _TRAILB_17751
                                                                    ; Pvar AT_17744
                                                                    ; Pvar AT8_17753 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_17743.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17744) (Pconst (8)%Z))) (Pconst (1)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17743 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17744) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_17755)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_17756.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf2_17747
                                                                    ; Pvar offset_17749
                                                                    ; Pvar DELTA_17752
                                                                    ; Pvar _LEN_17750
                                                                    ; Pvar _TRAILB_17751
                                                                    ; Pvar AT_17744
                                                                    ; Pvar AT8_17753 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_17743.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17744) (Pconst (8)%Z))) (Pconst (2)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17743 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17744) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_17756)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_17752.(gv)
                                                                ; Lvar _LEN_17750.(gv)
                                                                ; Lvar _TRAILB_17751.(gv)
                                                                ; Lvar AT8_17753.(gv)
                                                                ; Lvar t3_17757.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf3_17748
                                                                    ; Pvar offset_17749
                                                                    ; Pvar DELTA_17752
                                                                    ; Pvar _LEN_17750
                                                                    ; Pvar _TRAILB_17751
                                                                    ; Pvar AT_17744
                                                                    ; Pvar AT8_17753 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_17743.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17744) (Pconst (8)%Z))) (Pconst (3)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17743 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17744) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_17757)))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_17744.(gv)) AT_none (aint) (Pvar AT8_17753)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_17749.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17749) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17752))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_17758.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17744) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_17744) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17750) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_17754.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf0_17745 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17749))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_17743.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17743 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_17754)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_17755.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf1_17746 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17749))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_17743.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17743 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_17755)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_17756.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf2_17747 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17749))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_17743.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17743 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_17756)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_17757.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf3_17748 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_17749))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_17749.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17749) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_17743.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17743 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_17757)))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_17758.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_17744.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_17744) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_17750) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_17750.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_17750) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_17750)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_17751) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_17754.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf0_17745
                                                                    ; Pvar offset_17749
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_17750
                                                                    ; Pvar _TRAILB_17751
                                                                    ; Pvar AT_17744
                                                                    ; Pvar AT_17744 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_17743.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17743 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_17754)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_17755.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf1_17746
                                                                    ; Pvar offset_17749
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_17750
                                                                    ; Pvar _TRAILB_17751
                                                                    ; Pvar AT_17744
                                                                    ; Pvar AT_17744 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_17743.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17743 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_17755)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_17756.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf2_17747
                                                                    ; Pvar offset_17749
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_17750
                                                                    ; Pvar _TRAILB_17751
                                                                    ; Pvar AT_17744
                                                                    ; Pvar AT_17744 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_17743.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17743 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_17756)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_17752.(gv)
                                                                ; Lvar _LEN_17750.(gv)
                                                                ; Lvar _TRAILB_17751.(gv)
                                                                ; Lvar AT_17744.(gv)
                                                                ; Lvar t3_17757.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf3_17748
                                                                    ; Pvar offset_17749
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_17750
                                                                    ; Pvar _TRAILB_17751
                                                                    ; Pvar AT_17744
                                                                    ; Pvar AT_17744 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_17743.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_17743 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_17758) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_17757)))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_17749.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17749) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17752)))) ]
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
