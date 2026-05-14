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
Definition st_18125 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 18125).
Definition AT_18126 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18126).
Definition buf0_18127 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18127).
Definition buf1_18128 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18128).
Definition buf2_18129 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18129).
Definition buf3_18130 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18130).
Definition offset_18131 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18131).
Definition _LEN_18132 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18132).
Definition _TRAILB_18133 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18133).
Definition DELTA_18134 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18134).
Definition AT8_18135 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18135).
Definition t0_18136 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18136).
Definition t1_18137 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18137).
Definition t2_18138 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18138).
Definition t3_18139 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18139).
Definition j_at_18140 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18140).

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
  [:: st_18125.(gv)
    ; AT_18126.(gv)
    ; buf0_18127.(gv)
    ; buf1_18128.(gv)
    ; buf2_18129.(gv)
    ; buf3_18130.(gv)
    ; offset_18131.(gv)
    ; _LEN_18132.(gv)
    ; _TRAILB_18133.(gv) ].
Definition tyout_A1____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A1____addstate_avx2x4 : seq var_i :=
  [:: st_18125.(gv); AT_18126.(gv); offset_18131.(gv) ].

(* Body *)
Definition body_A1____addstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar DELTA_18134.(gv)) AT_none (aint) (Pconst (0)%Z))
    ; MkI dummy_instr_info (Cassgn (Lvar AT8_18135.(gv)) AT_none (aint) (Pvar AT_18126))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_18126.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18126) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_18135) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_18136.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf0_18127
                                                                    ; Pvar offset_18131
                                                                    ; Pvar DELTA_18134
                                                                    ; Pvar _LEN_18132
                                                                    ; Pvar _TRAILB_18133
                                                                    ; Pvar AT_18126
                                                                    ; Pvar AT8_18135 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_18125.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18126) (Pconst (8)%Z))) (Pconst (0)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18125 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18126) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_18136)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_18137.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf1_18128
                                                                    ; Pvar offset_18131
                                                                    ; Pvar DELTA_18134
                                                                    ; Pvar _LEN_18132
                                                                    ; Pvar _TRAILB_18133
                                                                    ; Pvar AT_18126
                                                                    ; Pvar AT8_18135 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_18125.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18126) (Pconst (8)%Z))) (Pconst (1)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18125 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18126) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_18137)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_18138.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf2_18129
                                                                    ; Pvar offset_18131
                                                                    ; Pvar DELTA_18134
                                                                    ; Pvar _LEN_18132
                                                                    ; Pvar _TRAILB_18133
                                                                    ; Pvar AT_18126
                                                                    ; Pvar AT8_18135 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_18125.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18126) (Pconst (8)%Z))) (Pconst (2)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18125 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18126) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_18138)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_18134.(gv)
                                                                ; Lvar _LEN_18132.(gv)
                                                                ; Lvar _TRAILB_18133.(gv)
                                                                ; Lvar AT8_18135.(gv)
                                                                ; Lvar t3_18139.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf3_18130
                                                                    ; Pvar offset_18131
                                                                    ; Pvar DELTA_18134
                                                                    ; Pvar _LEN_18132
                                                                    ; Pvar _TRAILB_18133
                                                                    ; Pvar AT_18126
                                                                    ; Pvar AT8_18135 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_18125.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18126) (Pconst (8)%Z))) (Pconst (3)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18125 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18126) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_18139)))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_18126.(gv)) AT_none (aint) (Pvar AT8_18135)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar offset_18131.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18131) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18134))))
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_18140.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18126) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18126) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18132) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_18136.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf0_18127 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_18131))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_18125.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18125 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_18136)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_18137.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf1_18128 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_18131))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_18125.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18125 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_18137)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_18138.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf2_18129 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_18131))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_18125.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18125 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_18138)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_18139.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 buf3_18130 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_18131))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_18131.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18131) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_18125.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18125 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_18139)))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_18140.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_18126.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_18126) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18132) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_18132.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18132) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_18132)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_18133) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_18136.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf0_18127
                                                                    ; Pvar offset_18131
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_18132
                                                                    ; Pvar _TRAILB_18133
                                                                    ; Pvar AT_18126
                                                                    ; Pvar AT_18126 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_18125.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18125 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_18136)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_18137.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf1_18128
                                                                    ; Pvar offset_18131
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_18132
                                                                    ; Pvar _TRAILB_18133
                                                                    ; Pvar AT_18126
                                                                    ; Pvar AT_18126 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_18125.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18125 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_18137)))
                                ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_18138.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf2_18129
                                                                    ; Pvar offset_18131
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_18132
                                                                    ; Pvar _TRAILB_18133
                                                                    ; Pvar AT_18126
                                                                    ; Pvar AT_18126 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_18125.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18125 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_18138)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar DELTA_18134.(gv)
                                                                ; Lvar _LEN_18132.(gv)
                                                                ; Lvar _TRAILB_18133.(gv)
                                                                ; Lvar AT_18126.(gv)
                                                                ; Lvar t3_18139.(gv) ] A1____a_ilen_read_upto8_at [:: Pvar buf3_18130
                                                                    ; Pvar offset_18131
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_18132
                                                                    ; Pvar _TRAILB_18133
                                                                    ; Pvar AT_18126
                                                                    ; Pvar AT_18126 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_18125.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18125 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18140) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_18139)))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_18131.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18131) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18134)))) ]
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
