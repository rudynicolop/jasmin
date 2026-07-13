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

(* A1184____addstate_avx2x4 *)
(* Local variables *)
Definition st_76 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 15968).
Definition AT_73 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15969).
Definition buf0_23 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15970).
Definition buf1_23 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15971).
Definition buf2_23 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15972).
Definition buf3_23 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15973).
Definition offset_108 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15974).
Definition _LEN_69 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15975).
Definition _TRAILB_41 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15976).
Definition DELTA_73 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15977).
Definition AT8_28 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15978).
Definition t0_16 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15979).
Definition t1_16 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15980).
Definition t2_14 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15981).
Definition t3_14 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15982).
Definition j_at_12 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15983).

(* Signature *)
Definition tyin_A1184____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 1184
    ; aarr U8 1184
    ; aarr U8 1184
    ; aarr U8 1184
    ; aword U64
    ; aint
    ; aint ].
Definition args_A1184____addstate_avx2x4 : seq var_i :=
  [:: st_76.(gv)
    ; AT_73.(gv)
    ; buf0_23.(gv)
    ; buf1_23.(gv)
    ; buf2_23.(gv)
    ; buf3_23.(gv)
    ; offset_108.(gv)
    ; _LEN_69.(gv)
    ; _TRAILB_41.(gv) ].
Definition tyout_A1184____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1184____addstate_avx2x4 : seq var_i :=
  [:: st_76.(gv); AT_73.(gv); offset_108.(gv) ].

(* Body *)
Definition body_A1184____addstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_73.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_28.(gv)) AT_none (aint) (Pvar AT_73))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_73.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_73) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_28) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_16.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf0_23
                                                                    ; Pvar offset_108
                                                                    ; Pvar DELTA_73
                                                                    ; Pvar _LEN_69
                                                                    ; Pvar _TRAILB_41
                                                                    ; Pvar AT_73
                                                                    ; Pvar AT8_28 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_76.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_73) (Pconst (8)%Z))) (Pconst (0)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_76 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_73) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_16)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_16.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf1_23
                                                                    ; Pvar offset_108
                                                                    ; Pvar DELTA_73
                                                                    ; Pvar _LEN_69
                                                                    ; Pvar _TRAILB_41
                                                                    ; Pvar AT_73
                                                                    ; Pvar AT8_28 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_76.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_73) (Pconst (8)%Z))) (Pconst (1)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_76 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_73) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_16)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_14.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf2_23
                                                                    ; Pvar offset_108
                                                                    ; Pvar DELTA_73
                                                                    ; Pvar _LEN_69
                                                                    ; Pvar _TRAILB_41
                                                                    ; Pvar AT_73
                                                                    ; Pvar AT8_28 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_76.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_73) (Pconst (8)%Z))) (Pconst (2)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_76 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_73) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_14)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_73.(gv)
                                                                ; Lvar _LEN_69.(gv)
                                                                ; Lvar _TRAILB_41.(gv)
                                                                ; Lvar AT8_28.(gv)
                                                                ; Lvar t3_14.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf3_23
                                                                    ; Pvar offset_108
                                                                    ; Pvar DELTA_73
                                                                    ; Pvar _LEN_69
                                                                    ; Pvar _TRAILB_41
                                                                    ; Pvar AT_73
                                                                    ; Pvar AT8_28 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_76.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_73) (Pconst (8)%Z))) (Pconst (3)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_76 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_73) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_14)))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_73.(gv)) AT_none (aint) (Pvar AT8_28)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_108.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_108) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_73))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_12.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_73) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_73) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_69) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_16.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf0_23 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_108))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_76.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_76 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_16)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_16.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf1_23 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_108))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_76.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_76 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_16)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_14.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf2_23 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_108))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_76.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_76 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_14)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_14.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf3_23 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_108))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_108.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_108) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_76.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_76 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_14)))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_12.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_73.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_73) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_69) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_69.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_69) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_69)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_41) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_16.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf0_23
                                                                    ; Pvar offset_108
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_69
                                                                    ; Pvar _TRAILB_41
                                                                    ; Pvar AT_73
                                                                    ; Pvar AT_73 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_76.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_76 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_16)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_16.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf1_23
                                                                    ; Pvar offset_108
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_69
                                                                    ; Pvar _TRAILB_41
                                                                    ; Pvar AT_73
                                                                    ; Pvar AT_73 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_76.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_76 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_16)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_14.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf2_23
                                                                    ; Pvar offset_108
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_69
                                                                    ; Pvar _TRAILB_41
                                                                    ; Pvar AT_73
                                                                    ; Pvar AT_73 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_76.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_76 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_14)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_73.(gv)
                                                                ; Lvar _LEN_69.(gv)
                                                                ; Lvar _TRAILB_41.(gv)
                                                                ; Lvar AT_73.(gv)
                                                                ; Lvar t3_14.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf3_23
                                                                    ; Pvar offset_108
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_69
                                                                    ; Pvar _TRAILB_41
                                                                    ; Pvar AT_73
                                                                    ; Pvar AT_73 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_76.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_76 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_12) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_14)))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_108.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_108) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_73)))) ]
                              [::]) ].

Definition fd_A1184____addstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____addstate_avx2x4;
    f_params := args_A1184____addstate_avx2x4;
    f_body := body_A1184____addstate_avx2x4;
    f_tyout := tyout_A1184____addstate_avx2x4;
    f_res := res_A1184____addstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
