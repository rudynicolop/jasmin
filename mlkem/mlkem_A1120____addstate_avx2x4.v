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

(* A1120____addstate_avx2x4 *)
(* Local variables *)
Definition st_96 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 15204).
Definition AT_93 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15205).
Definition buf0_31 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15206).
Definition buf1_31 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15207).
Definition buf2_31 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15208).
Definition buf3_31 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15209).
Definition offset_142 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15210).
Definition _LEN_89 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15211).
Definition _TRAILB_53 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15212).
Definition DELTA_95 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15213).
Definition AT8_36 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15214).
Definition t0_20 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15215).
Definition t1_20 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15216).
Definition t2_18 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15217).
Definition t3_18 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15218).
Definition j_at_16 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15219).

(* Signature *)
Definition tyin_A1120____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 1120
    ; aarr U8 1120
    ; aarr U8 1120
    ; aarr U8 1120
    ; aword U64
    ; aint
    ; aint ].
Definition args_A1120____addstate_avx2x4 : seq var_i :=
  [:: st_96.(gv)
    ; AT_93.(gv)
    ; buf0_31.(gv)
    ; buf1_31.(gv)
    ; buf2_31.(gv)
    ; buf3_31.(gv)
    ; offset_142.(gv)
    ; _LEN_89.(gv)
    ; _TRAILB_53.(gv) ].
Definition tyout_A1120____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1120____addstate_avx2x4 : seq var_i :=
  [:: st_96.(gv); AT_93.(gv); offset_142.(gv) ].

(* Body *)
Definition body_A1120____addstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_95.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_36.(gv)) AT_none (aint) (Pvar AT_93))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_93.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_93) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_36) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_20.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf0_31
                                                                    ; Pvar offset_142
                                                                    ; Pvar DELTA_95
                                                                    ; Pvar _LEN_89
                                                                    ; Pvar _TRAILB_53
                                                                    ; Pvar AT_93
                                                                    ; Pvar AT8_36 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_96.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_93) (Pconst (8)%Z))) (Pconst (0)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_96 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_93) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_20)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_20.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf1_31
                                                                    ; Pvar offset_142
                                                                    ; Pvar DELTA_95
                                                                    ; Pvar _LEN_89
                                                                    ; Pvar _TRAILB_53
                                                                    ; Pvar AT_93
                                                                    ; Pvar AT8_36 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_96.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_93) (Pconst (8)%Z))) (Pconst (1)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_96 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_93) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_20)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_18.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf2_31
                                                                    ; Pvar offset_142
                                                                    ; Pvar DELTA_95
                                                                    ; Pvar _LEN_89
                                                                    ; Pvar _TRAILB_53
                                                                    ; Pvar AT_93
                                                                    ; Pvar AT8_36 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_96.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_93) (Pconst (8)%Z))) (Pconst (2)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_96 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_93) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_18)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_95.(gv)
                                                                ; Lvar _LEN_89.(gv)
                                                                ; Lvar _TRAILB_53.(gv)
                                                                ; Lvar AT8_36.(gv)
                                                                ; Lvar t3_18.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf3_31
                                                                    ; Pvar offset_142
                                                                    ; Pvar DELTA_95
                                                                    ; Pvar _LEN_89
                                                                    ; Pvar _TRAILB_53
                                                                    ; Pvar AT_93
                                                                    ; Pvar AT8_36 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_96.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_93) (Pconst (8)%Z))) (Pconst (3)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_96 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_93) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_18)))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_93.(gv)) AT_none (aint) (Pvar AT8_36)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_142.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_142) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_95))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_16.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_93) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_93) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_89) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_20.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf0_31 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_142))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_96.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_96 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_20)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_20.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf1_31 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_142))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_96.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_96 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_20)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_18.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf2_31 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_142))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_96.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_96 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_18)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_18.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf3_31 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_142))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_142.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_142) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_96.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_96 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_18)))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_16.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_93.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_93) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_89) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_89.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_89) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_89)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_53) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_20.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf0_31
                                                                    ; Pvar offset_142
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_89
                                                                    ; Pvar _TRAILB_53
                                                                    ; Pvar AT_93
                                                                    ; Pvar AT_93 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_96.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_96 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_20)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_20.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf1_31
                                                                    ; Pvar offset_142
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_89
                                                                    ; Pvar _TRAILB_53
                                                                    ; Pvar AT_93
                                                                    ; Pvar AT_93 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_96.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_96 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_20)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_18.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf2_31
                                                                    ; Pvar offset_142
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_89
                                                                    ; Pvar _TRAILB_53
                                                                    ; Pvar AT_93
                                                                    ; Pvar AT_93 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_96.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_96 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_18)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_95.(gv)
                                                                ; Lvar _LEN_89.(gv)
                                                                ; Lvar _TRAILB_53.(gv)
                                                                ; Lvar AT_93.(gv)
                                                                ; Lvar t3_18.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf3_31
                                                                    ; Pvar offset_142
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_89
                                                                    ; Pvar _TRAILB_53
                                                                    ; Pvar AT_93
                                                                    ; Pvar AT_93 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_96.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_96 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_18)))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_142.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_142) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_95)))) ]
                              [::]) ].

Definition fd_A1120____addstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____addstate_avx2x4;
    f_params := args_A1120____addstate_avx2x4;
    f_body := body_A1120____addstate_avx2x4;
    f_tyout := tyout_A1120____addstate_avx2x4;
    f_res := res_A1120____addstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
