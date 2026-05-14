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
Definition st_15204 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 15204).
Definition AT_15205 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15205).
Definition buf0_15206 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15206).
Definition buf1_15207 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15207).
Definition buf2_15208 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15208).
Definition buf3_15209 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15209).
Definition offset_15210 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15210).
Definition _LEN_15211 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15211).
Definition _TRAILB_15212 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15212).
Definition DELTA_15213 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15213).
Definition AT8_15214 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15214).
Definition t0_15215 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15215).
Definition t1_15216 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15216).
Definition t2_15217 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15217).
Definition t3_15218 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15218).
Definition j_at_15219 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15219).

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
  [:: st_15204.(gv)
    ; AT_15205.(gv)
    ; buf0_15206.(gv)
    ; buf1_15207.(gv)
    ; buf2_15208.(gv)
    ; buf3_15209.(gv)
    ; offset_15210.(gv)
    ; _LEN_15211.(gv)
    ; _TRAILB_15212.(gv) ].
Definition tyout_A1120____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1120____addstate_avx2x4 : seq var_i :=
  [:: st_15204.(gv); AT_15205.(gv); offset_15210.(gv) ].

(* Body *)
Definition body_A1120____addstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_15213.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_15214.(gv)) AT_none (aint) (Pvar AT_15205))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_15205.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15205) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_15214) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_15215.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf0_15206
                                                                    ; Pvar offset_15210
                                                                    ; Pvar DELTA_15213
                                                                    ; Pvar _LEN_15211
                                                                    ; Pvar _TRAILB_15212
                                                                    ; Pvar AT_15205
                                                                    ; Pvar AT8_15214 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15204.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15205) (Pconst (8)%Z))) (Pconst (0)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15204 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15205) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_15215)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_15216.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf1_15207
                                                                    ; Pvar offset_15210
                                                                    ; Pvar DELTA_15213
                                                                    ; Pvar _LEN_15211
                                                                    ; Pvar _TRAILB_15212
                                                                    ; Pvar AT_15205
                                                                    ; Pvar AT8_15214 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15204.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15205) (Pconst (8)%Z))) (Pconst (1)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15204 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15205) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_15216)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_15217.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf2_15208
                                                                    ; Pvar offset_15210
                                                                    ; Pvar DELTA_15213
                                                                    ; Pvar _LEN_15211
                                                                    ; Pvar _TRAILB_15212
                                                                    ; Pvar AT_15205
                                                                    ; Pvar AT8_15214 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15204.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15205) (Pconst (8)%Z))) (Pconst (2)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15204 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15205) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_15217)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_15213.(gv)
                                                                ; Lvar _LEN_15211.(gv)
                                                                ; Lvar _TRAILB_15212.(gv)
                                                                ; Lvar AT8_15214.(gv)
                                                                ; Lvar t3_15218.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf3_15209
                                                                    ; Pvar offset_15210
                                                                    ; Pvar DELTA_15213
                                                                    ; Pvar _LEN_15211
                                                                    ; Pvar _TRAILB_15212
                                                                    ; Pvar AT_15205
                                                                    ; Pvar AT8_15214 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15204.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15205) (Pconst (8)%Z))) (Pconst (3)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15204 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15205) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_15218)))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_15205.(gv)) AT_none (aint) (Pvar AT8_15214)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_15210.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15210) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15213))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_15219.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15205) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_15205) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15211) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_15215.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf0_15206 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15210))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15204.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15204 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_15215)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_15216.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf1_15207 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15210))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15204.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15204 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_15216)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_15217.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf2_15208 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15210))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15204.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15204 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_15217)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_15218.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf3_15209 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15210))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_15210.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15210) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15204.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15204 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_15218)))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_15219.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_15205.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_15205) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15211) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_15211.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15211) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_15211)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_15212) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_15215.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf0_15206
                                                                    ; Pvar offset_15210
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15211
                                                                    ; Pvar _TRAILB_15212
                                                                    ; Pvar AT_15205
                                                                    ; Pvar AT_15205 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15204.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15204 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_15215)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_15216.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf1_15207
                                                                    ; Pvar offset_15210
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15211
                                                                    ; Pvar _TRAILB_15212
                                                                    ; Pvar AT_15205
                                                                    ; Pvar AT_15205 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15204.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15204 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_15216)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_15217.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf2_15208
                                                                    ; Pvar offset_15210
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15211
                                                                    ; Pvar _TRAILB_15212
                                                                    ; Pvar AT_15205
                                                                    ; Pvar AT_15205 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15204.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15204 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_15217)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_15213.(gv)
                                                                ; Lvar _LEN_15211.(gv)
                                                                ; Lvar _TRAILB_15212.(gv)
                                                                ; Lvar AT_15205.(gv)
                                                                ; Lvar t3_15218.(gv) ] A1120____a_ilen_read_upto8_at [:: Pvar buf3_15209
                                                                    ; Pvar offset_15210
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_15211
                                                                    ; Pvar _TRAILB_15212
                                                                    ; Pvar AT_15205
                                                                    ; Pvar AT_15205 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_15204.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_15204 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_15219) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_15218)))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_15210.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15210) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15213)))) ]
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
