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
Definition st_15968 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 15968).
Definition AT_15969 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15969).
Definition buf0_15970 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15970).
Definition buf1_15971 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15971).
Definition buf2_15972 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15972).
Definition buf3_15973 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 15973).
Definition offset_15974 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15974).
Definition _LEN_15975 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15975).
Definition _TRAILB_15976 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15976).
Definition DELTA_15977 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15977).
Definition AT8_15978 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15978).
Definition t0_15979 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15979).
Definition t1_15980 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15980).
Definition t2_15981 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15981).
Definition t3_15982 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15982).
Definition j_at_15983 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15983).

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
  [:: st_15968.(gv)
    ; AT_15969.(gv)
    ; buf0_15970.(gv)
    ; buf1_15971.(gv)
    ; buf2_15972.(gv)
    ; buf3_15973.(gv)
    ; offset_15974.(gv)
    ; _LEN_15975.(gv)
    ; _TRAILB_15976.(gv) ].
Definition tyout_A1184____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1184____addstate_avx2x4 : seq var_i :=
  [:: st_15968.(gv); AT_15969.(gv); offset_15974.(gv) ].

(* Body *)
Definition body_A1184____addstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_15977.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_15978.(gv)) AT_none (aint) (Pvar AT_15969))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_15969.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15969) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_15978) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_15979.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf0_15970
                                                                    ; Pvar offset_15974
                                                                    ; Pvar DELTA_15977
                                                                    ; Pvar _LEN_15975
                                                                    ; Pvar _TRAILB_15976
                                                                    ; Pvar AT_15969
                                                                    ; Pvar AT8_15978 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15968.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15969) (Pconst (8)%Z))) (Pconst (0)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15968 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15969) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_15979)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_15980.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf1_15971
                                                                    ; Pvar offset_15974
                                                                    ; Pvar DELTA_15977
                                                                    ; Pvar _LEN_15975
                                                                    ; Pvar _TRAILB_15976
                                                                    ; Pvar AT_15969
                                                                    ; Pvar AT8_15978 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15968.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15969) (Pconst (8)%Z))) (Pconst (1)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15968 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15969) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_15980)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_15981.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf2_15972
                                                                    ; Pvar offset_15974
                                                                    ; Pvar DELTA_15977
                                                                    ; Pvar _LEN_15975
                                                                    ; Pvar _TRAILB_15976
                                                                    ; Pvar AT_15969
                                                                    ; Pvar AT8_15978 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15968.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15969) (Pconst (8)%Z))) (Pconst (2)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15968 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15969) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_15981)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_15977.(gv)
                                                                ; Lvar _LEN_15975.(gv)
                                                                ; Lvar _TRAILB_15976.(gv)
                                                                ; Lvar AT8_15978.(gv)
                                                                ; Lvar t3_15982.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf3_15973
                                                                    ; Pvar offset_15974
                                                                    ; Pvar DELTA_15977
                                                                    ; Pvar _LEN_15975
                                                                    ; Pvar _TRAILB_15976
                                                                    ; Pvar AT_15969
                                                                    ; Pvar AT8_15978 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15968.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15969) (Pconst (8)%Z))) (Pconst (3)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15968 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15969) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_15982)))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_15969.(gv)) AT_none (aint) (Pvar AT8_15978)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_15974.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15974) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15977))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_15983.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15969) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15969) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15975) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_15979.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf0_15970 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15974))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15968.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15968 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_15979)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_15980.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf1_15971 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15974))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15968.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15968 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_15980)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_15981.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf2_15972 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15974))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15968.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15968 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_15981)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_15982.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf3_15973 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15974))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_15974.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15974) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15968.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15968 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_15982)))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_15983.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_15969.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_15969) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15975) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15975.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15975) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15975)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_15976) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_15979.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf0_15970
                                                                    ; Pvar offset_15974
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15975
                                                                    ; Pvar _TRAILB_15976
                                                                    ; Pvar AT_15969
                                                                    ; Pvar AT_15969 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15968.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15968 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_15979)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_15980.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf1_15971
                                                                    ; Pvar offset_15974
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15975
                                                                    ; Pvar _TRAILB_15976
                                                                    ; Pvar AT_15969
                                                                    ; Pvar AT_15969 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15968.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15968 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_15980)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_15981.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf2_15972
                                                                    ; Pvar offset_15974
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15975
                                                                    ; Pvar _TRAILB_15976
                                                                    ; Pvar AT_15969
                                                                    ; Pvar AT_15969 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15968.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15968 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_15981)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_15977.(gv)
                                                                ; Lvar _LEN_15975.(gv)
                                                                ; Lvar _TRAILB_15976.(gv)
                                                                ; Lvar AT_15969.(gv)
                                                                ; Lvar t3_15982.(gv) ] A1184____a_ilen_read_upto8_at [:: Pvar buf3_15973
                                                                    ; Pvar offset_15974
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15975
                                                                    ; Pvar _TRAILB_15976
                                                                    ; Pvar AT_15969
                                                                    ; Pvar AT_15969 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15968.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15968 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15983) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_15982)))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_15974.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15974) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15977)))) ]
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
