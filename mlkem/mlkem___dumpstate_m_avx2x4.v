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

(* __dumpstate_m_avx2x4 *)
(* Local variables *)
Definition buf0_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18453).
Definition buf1_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18454).
Definition buf2_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18455).
Definition buf3_1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18456).
Definition _LEN_7 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18457).
Definition st_14 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 18458).
Definition i_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18459).
Definition x0_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18460).
Definition x1_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18461).
Definition x2_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18462).
Definition x3_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18463).
Definition t0_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18464).
Definition t1_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18465).
Definition t2_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18466).
Definition t3_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18467).

(* Signature *)
Definition tyin___dumpstate_m_avx2x4 : seq atype :=
  [:: aword U64; aword U64; aword U64; aword U64; aint; aarr U256 25 ].
Definition args___dumpstate_m_avx2x4 : seq var_i :=
  [:: buf0_1.(gv)
    ; buf1_1.(gv)
    ; buf2_1.(gv)
    ; buf3_1.(gv)
    ; _LEN_7.(gv)
    ; st_14.(gv) ].
Definition tyout___dumpstate_m_avx2x4 : seq atype :=
  [:: aword U64; aword U64; aword U64; aword U64 ].
Definition res___dumpstate_m_avx2x4 : seq var_i :=
  [:: buf0_1.(gv); buf1_1.(gv); buf2_1.(gv); buf3_1.(gv) ].

(* Body *)
Definition body___dumpstate_m_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar i_9.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_9) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_7) (Pconst (32)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_3.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_9)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_3.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_9)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_3.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_9)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_3.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_9)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_9.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_9) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_3.(gv)
                                                                ; Lvar x1_3.(gv)
                                                                ; Lvar x2_3.(gv)
                                                                ; Lvar x3_3.(gv) ] __4u64x4_u256x4 [:: Pvar x0_3
                                                                    ; Pvar x1_3
                                                                    ; Pvar x2_3
                                                                    ; Pvar x3_3 ])
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U256 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf0_1))) AT_none (aword U256) (Pvar x0_3))
                                ; MkI dummy_instr_info (Cassgn (Lvar buf0_1.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf0_1) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U256 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf1_1))) AT_none (aword U256) (Pvar x1_3))
                                ; MkI dummy_instr_info (Cassgn (Lvar buf1_1.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf1_1) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U256 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf2_1))) AT_none (aword U256) (Pvar x2_3))
                                ; MkI dummy_instr_info (Cassgn (Lvar buf2_1.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf2_1) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U256 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf3_1))) AT_none (aword U256) (Pvar x3_3))
                                ; MkI dummy_instr_info (Cassgn (Lvar buf3_1.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf3_1) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_9) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_7) (Pconst (8)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_5.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_9)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf0_1) (Pvar i_9)))) AT_none (aword U64) (Pvar t0_5))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_5.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_9)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf1_1) (Pvar i_9)))) AT_none (aword U64) (Pvar t1_5))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_3.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_9)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf2_1) (Pvar i_9)))) AT_none (aword U64) (Pvar t2_3))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_3.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_9)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf3_1) (Pvar i_9)))) AT_none (aword U64) (Pvar t3_3))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_9.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_9) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar buf0_1.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf0_1) (Pvar i_9)))
    ; MkI dummy_instr_info (Cassgn (Lvar buf1_1.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf1_1) (Pvar i_9)))
    ; MkI dummy_instr_info (Cassgn (Lvar buf2_1.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf2_1) (Pvar i_9)))
    ; MkI dummy_instr_info (Cassgn (Lvar buf3_1.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf3_1) (Pvar i_9)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_7) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_5.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_9)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_1.(gv)
                                                                ; Lnone dummy_var_info (aint) ] __m_ilen_write_upto8 [:: Pvar buf0_1
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_7) (Pconst (8)%Z)
                                                                    ; Pvar t0_5 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_5.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_9)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf1_1.(gv)
                                                                ; Lnone dummy_var_info (aint) ] __m_ilen_write_upto8 [:: Pvar buf1_1
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_7) (Pconst (8)%Z)
                                                                    ; Pvar t1_5 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_3.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_9)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf2_1.(gv)
                                                                ; Lnone dummy_var_info (aint) ] __m_ilen_write_upto8 [:: Pvar buf2_1
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_7) (Pconst (8)%Z)
                                                                    ; Pvar t2_3 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_3.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_14 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_9)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf3_1.(gv)
                                                                ; Lnone dummy_var_info (aint) ] __m_ilen_write_upto8 [:: Pvar buf3_1
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_7) (Pconst (8)%Z)
                                                                    ; Pvar t3_3 ]) ]
                              [::]) ].

Definition fd___dumpstate_m_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___dumpstate_m_avx2x4;
    f_params := args___dumpstate_m_avx2x4;
    f_body := body___dumpstate_m_avx2x4;
    f_tyout := tyout___dumpstate_m_avx2x4;
    f_res := res___dumpstate_m_avx2x4;
    f_extra := tt;
  |}.

End IDO.
