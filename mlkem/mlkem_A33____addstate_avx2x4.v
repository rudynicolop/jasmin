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

(* A33____addstate_avx2x4 *)
(* Local variables *)
Definition st_52 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 16979).
Definition AT_47 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16980).
Definition buf0_15 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 16981).
Definition buf1_15 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 16982).
Definition buf2_15 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 16983).
Definition buf3_15 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 16984).
Definition offset_63 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16985).
Definition _LEN_45 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16986).
Definition _TRAILB_27 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16987).
Definition DELTA_42 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16988).
Definition AT8_18 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16989).
Definition t0_12 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16990).
Definition t1_12 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16991).
Definition t2_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16992).
Definition t3_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16993).
Definition j_at_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16994).

(* Signature *)
Definition tyin_A33____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aarr U8 33
    ; aarr U8 33
    ; aarr U8 33
    ; aarr U8 33
    ; aword U64
    ; aint
    ; aint ].
Definition args_A33____addstate_avx2x4 : seq var_i :=
  [:: st_52.(gv)
    ; AT_47.(gv)
    ; buf0_15.(gv)
    ; buf1_15.(gv)
    ; buf2_15.(gv)
    ; buf3_15.(gv)
    ; offset_63.(gv)
    ; _LEN_45.(gv)
    ; _TRAILB_27.(gv) ].
Definition tyout_A33____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A33____addstate_avx2x4 : seq var_i :=
  [:: st_52.(gv); AT_47.(gv); offset_63.(gv) ].

(* Body *)
Definition body_A33____addstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_42.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_18.(gv)) AT_none (aint) (Pvar AT_47))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_47.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_47) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_18) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_12.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf0_15
                                                                    ; Pvar offset_63
                                                                    ; Pvar DELTA_42
                                                                    ; Pvar _LEN_45
                                                                    ; Pvar _TRAILB_27
                                                                    ; Pvar AT_47
                                                                    ; Pvar AT8_18 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_52.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_47) (Pconst (8)%Z))) (Pconst (0)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_52 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_47) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_12)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_12.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf1_15
                                                                    ; Pvar offset_63
                                                                    ; Pvar DELTA_42
                                                                    ; Pvar _LEN_45
                                                                    ; Pvar _TRAILB_27
                                                                    ; Pvar AT_47
                                                                    ; Pvar AT8_18 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_52.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_47) (Pconst (8)%Z))) (Pconst (1)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_52 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_47) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_12)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_10.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf2_15
                                                                    ; Pvar offset_63
                                                                    ; Pvar DELTA_42
                                                                    ; Pvar _LEN_45
                                                                    ; Pvar _TRAILB_27
                                                                    ; Pvar AT_47
                                                                    ; Pvar AT8_18 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_52.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_47) (Pconst (8)%Z))) (Pconst (2)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_52 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_47) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_10)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_42.(gv)
                                                                ; Lvar _LEN_45.(gv)
                                                                ; Lvar _TRAILB_27.(gv)
                                                                ; Lvar AT8_18.(gv)
                                                                ; Lvar t3_10.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf3_15
                                                                    ; Pvar offset_63
                                                                    ; Pvar DELTA_42
                                                                    ; Pvar _LEN_45
                                                                    ; Pvar _TRAILB_27
                                                                    ; Pvar AT_47
                                                                    ; Pvar AT8_18 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_52.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_47) (Pconst (8)%Z))) (Pconst (3)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_52 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_47) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_10)))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_47.(gv)) AT_none (aint) (Pvar AT8_18)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_63.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_63) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_42))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_8.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_47) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_47) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_45) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_12.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf0_15 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_63))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_52.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_52 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_12)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_12.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf1_15 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_63))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_52.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_52 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_12)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_10.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf2_15 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_63))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_52.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_52 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_10)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_10.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf3_15 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_63))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_63.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_63) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_52.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_52 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_10)))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_8.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_47.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_47) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_45) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_45.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_45) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_45)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_27) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_12.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf0_15
                                                                    ; Pvar offset_63
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_45
                                                                    ; Pvar _TRAILB_27
                                                                    ; Pvar AT_47
                                                                    ; Pvar AT_47 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_52.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_52 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_12)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_12.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf1_15
                                                                    ; Pvar offset_63
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_45
                                                                    ; Pvar _TRAILB_27
                                                                    ; Pvar AT_47
                                                                    ; Pvar AT_47 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_52.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_52 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_12)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_10.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf2_15
                                                                    ; Pvar offset_63
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_45
                                                                    ; Pvar _TRAILB_27
                                                                    ; Pvar AT_47
                                                                    ; Pvar AT_47 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_52.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_52 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_10)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_42.(gv)
                                                                ; Lvar _LEN_45.(gv)
                                                                ; Lvar _TRAILB_27.(gv)
                                                                ; Lvar AT_47.(gv)
                                                                ; Lvar t3_10.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf3_15
                                                                    ; Pvar offset_63
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_45
                                                                    ; Pvar _TRAILB_27
                                                                    ; Pvar AT_47
                                                                    ; Pvar AT_47 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_52.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_52 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_8) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_10)))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_63.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_63) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_42)))) ]
                              [::]) ].

Definition fd_A33____addstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____addstate_avx2x4;
    f_params := args_A33____addstate_avx2x4;
    f_body := body_A33____addstate_avx2x4;
    f_tyout := tyout_A33____addstate_avx2x4;
    f_res := res_A33____addstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
