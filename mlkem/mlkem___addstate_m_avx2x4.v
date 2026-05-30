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

(* __addstate_m_avx2x4 *)
(* Local variables *)
Definition st_12 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18500).
Definition AT_7 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18501).
Definition buf0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18502).
Definition buf1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18503).
Definition buf2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18504).
Definition buf3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18505).
Definition _LEN_5 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18506).
Definition _TRAILB_3 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18507).
Definition AT8_2 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18508).
Definition t0_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18509).
Definition t1_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18510).
Definition t2_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18511).
Definition t3_2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18512).
Definition j_at_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18513).

(* Signature *)
Definition tyin___addstate_m_avx2x4 : seq atype :=
  [:: aarr U256 25
    ; aint
    ; aword U64
    ; aword U64
    ; aword U64
    ; aword U64
    ; aint
    ; aint ].
Definition args___addstate_m_avx2x4 : seq var_i :=
  [:: st_12.(gv)
    ; AT_7.(gv)
    ; buf0.(gv)
    ; buf1.(gv)
    ; buf2.(gv)
    ; buf3.(gv)
    ; _LEN_5.(gv)
    ; _TRAILB_3.(gv) ].
Definition tyout___addstate_m_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64; aword U64; aword U64; aword U64 ].
Definition res___addstate_m_avx2x4 : seq var_i :=
  [:: st_12.(gv); AT_7.(gv); buf0.(gv); buf1.(gv); buf2.(gv); buf3.(gv) ].

(* Body *)
Definition body___addstate_m_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar AT8_2.(gv)) AT_none (aint) (Pvar AT_7))
    ; MkI dummy_instr_info (Cassgn (Lvar AT_7.(gv)) AT_none (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_7) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_2) (Pconst (8)%Z)) (Pconst (0)%Z))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf0.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_4.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf0
                                                                    ; Pvar _LEN_5
                                                                    ; Pvar _TRAILB_3
                                                                    ; Pvar AT_7
                                                                    ; Pvar AT8_2 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_12.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_7) (Pconst (8)%Z))) (Pconst (0)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_12 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_7) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_4)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf1.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_4.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf1
                                                                    ; Pvar _LEN_5
                                                                    ; Pvar _TRAILB_3
                                                                    ; Pvar AT_7
                                                                    ; Pvar AT8_2 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_12.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_7) (Pconst (8)%Z))) (Pconst (1)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_12 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_7) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_4)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf2.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_2.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf2
                                                                    ; Pvar _LEN_5
                                                                    ; Pvar _TRAILB_3
                                                                    ; Pvar AT_7
                                                                    ; Pvar AT8_2 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_12.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_7) (Pconst (8)%Z))) (Pconst (2)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_12 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_7) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_2)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf3.(gv)
                                                                ; Lvar _LEN_5.(gv)
                                                                ; Lvar _TRAILB_3.(gv)
                                                                ; Lvar AT8_2.(gv)
                                                                ; Lvar t3_2.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf3
                                                                    ; Pvar _LEN_5
                                                                    ; Pvar _TRAILB_3
                                                                    ; Pvar AT_7
                                                                    ; Pvar AT8_2 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_12.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_7) (Pconst (8)%Z))) (Pconst (3)%Z))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_12 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_7) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_2)))
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_7.(gv)) AT_none (aint) (Pvar AT8_2)) ]
                              [::])
    ; MkI dummy_instr_info (Cassgn (Lvar j_at_0.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_7) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_7) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_5) (Pconst (8)%Z))))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_4.(gv)) AT_none (aword U64) (Pload Unaligned U64 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf0))))
                                ; MkI dummy_instr_info (Cassgn (Lvar buf0.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_12.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_12 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_4)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_4.(gv)) AT_none (aword U64) (Pload Unaligned U64 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf1))))
                                ; MkI dummy_instr_info (Cassgn (Lvar buf1.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf1) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_12.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_12 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_4)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_2.(gv)) AT_none (aword U64) (Pload Unaligned U64 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf2))))
                                ; MkI dummy_instr_info (Cassgn (Lvar buf2.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_12.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_12 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_2)))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_2.(gv)) AT_none (aword U64) (Pload Unaligned U64 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf3))))
                                ; MkI dummy_instr_info (Cassgn (Lvar buf3.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf3) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_12.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_12 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_2)))
                                ; MkI dummy_instr_info (Cassgn (Lvar j_at_0.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar AT_7.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_7) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_5) (Pconst (8)%Z)))))
    ; MkI dummy_instr_info (Cassgn (Lvar _LEN_5.(gv)) AT_none (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_5) (Pconst (8)%Z)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_5)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_3) (Pconst (256)%Z)) (Pconst (0)%Z)))
                              [:: MkI dummy_instr_info (Ccall [:: Lvar buf0.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t0_4.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf0
                                                                    ; Pvar _LEN_5
                                                                    ; Pvar _TRAILB_3
                                                                    ; Pvar AT_7
                                                                    ; Pvar AT_7 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_12.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_12 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_4)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf1.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t1_4.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf1
                                                                    ; Pvar _LEN_5
                                                                    ; Pvar _TRAILB_3
                                                                    ; Pvar AT_7
                                                                    ; Pvar AT_7 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_12.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_12 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_4)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf2.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar t2_2.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf2
                                                                    ; Pvar _LEN_5
                                                                    ; Pvar _TRAILB_3
                                                                    ; Pvar AT_7
                                                                    ; Pvar AT_7 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_12.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_12 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_2)))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf3.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lvar AT_7.(gv)
                                                                ; Lvar t3_2.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf3
                                                                    ; Pvar _LEN_5
                                                                    ; Pvar _TRAILB_3
                                                                    ; Pvar AT_7
                                                                    ; Pvar AT_7 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U64 st_12.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) AT_none (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_12 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_2))) ]
                              [::]) ].

Definition fd___addstate_m_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___addstate_m_avx2x4;
    f_params := args___addstate_m_avx2x4;
    f_body := body___addstate_m_avx2x4;
    f_tyout := tyout___addstate_m_avx2x4;
    f_res := res___addstate_m_avx2x4;
    f_extra := tt;
  |}.

End IDO.
