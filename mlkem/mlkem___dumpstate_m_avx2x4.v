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
Definition buf0_18453 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18453).
Definition buf1_18454 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18454).
Definition buf2_18455 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18455).
Definition buf3_18456 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18456).
Definition _LEN_18457 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18457).
Definition st_18458 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 18458).
Definition i_18459 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18459).
Definition x0_18460 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18460).
Definition x1_18461 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18461).
Definition x2_18462 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18462).
Definition x3_18463 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 18463).
Definition t0_18464 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18464).
Definition t1_18465 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18465).
Definition t2_18466 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18466).
Definition t3_18467 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18467).

(* Signature *)
Definition tyin___dumpstate_m_avx2x4 : seq atype :=
  [:: aword U64; aword U64; aword U64; aword U64; aint; aarr U256 25 ].
Definition args___dumpstate_m_avx2x4 : seq var_i :=
  [:: buf0_18453.(gv)
    ; buf1_18454.(gv)
    ; buf2_18455.(gv)
    ; buf3_18456.(gv)
    ; _LEN_18457.(gv)
    ; st_18458.(gv) ].
Definition tyout___dumpstate_m_avx2x4 : seq atype :=
  [:: aword U64; aword U64; aword U64; aword U64 ].
Definition res___dumpstate_m_avx2x4 : seq var_i :=
  [:: buf0_18453.(gv); buf1_18454.(gv); buf2_18455.(gv); buf3_18456.(gv) ].

(* Body *)
Definition body___dumpstate_m_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar i_18459.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_18459) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18457) (Pconst (32)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_18460.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_18461.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_18462.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_18463.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_18459.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_18459) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_18460.(gv)
                                                                ; Lvar x1_18461.(gv)
                                                                ; Lvar x2_18462.(gv)
                                                                ; Lvar x3_18463.(gv) ] __4u64x4_u256x4 [:: Pvar x0_18460
                                                                    ; Pvar x1_18461
                                                                    ; Pvar x2_18462
                                                                    ; Pvar x3_18463 ])
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U256 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf0_18453))) AT_none (aword U256) (Pvar x0_18460))
                                ; MkI dummy_instr_info (Cassgn (Lvar buf0_18453.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf0_18453) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U256 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf1_18454))) AT_none (aword U256) (Pvar x1_18461))
                                ; MkI dummy_instr_info (Cassgn (Lvar buf1_18454.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf1_18454) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U256 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf2_18455))) AT_none (aword U256) (Pvar x2_18462))
                                ; MkI dummy_instr_info (Cassgn (Lvar buf2_18455.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf2_18455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U256 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf3_18456))) AT_none (aword U256) (Pvar x3_18463))
                                ; MkI dummy_instr_info (Cassgn (Lvar buf3_18456.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf3_18456) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_18459) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18457) (Pconst (8)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_18464.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf0_18453) (Pvar i_18459)))) AT_none (aword U64) (Pvar t0_18464))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_18465.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf1_18454) (Pvar i_18459)))) AT_none (aword U64) (Pvar t1_18465))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_18466.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf2_18455) (Pvar i_18459)))) AT_none (aword U64) (Pvar t2_18466))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_18467.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf3_18456) (Pvar i_18459)))) AT_none (aword U64) (Pvar t3_18467))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_18459.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_18459) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ])
    ; MkI dummy_instr_info (Cassgn (Lvar buf0_18453.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf0_18453) (Pvar i_18459)))
    ; MkI dummy_instr_info (Cassgn (Lvar buf1_18454.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf1_18454) (Pvar i_18459)))
    ; MkI dummy_instr_info (Cassgn (Lvar buf2_18455.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf2_18455) (Pvar i_18459)))
    ; MkI dummy_instr_info (Cassgn (Lvar buf3_18456.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf3_18456) (Pvar i_18459)))
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18457) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_18464.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_18453.(gv)
                                                                ; Lnone dummy_var_info (aint) ] __m_ilen_write_upto8 [:: Pvar buf0_18453
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18457) (Pconst (8)%Z)
                                                                    ; Pvar t0_18464 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_18465.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf1_18454.(gv)
                                                                ; Lnone dummy_var_info (aint) ] __m_ilen_write_upto8 [:: Pvar buf1_18454
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18457) (Pconst (8)%Z)
                                                                    ; Pvar t1_18465 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_18466.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf2_18455.(gv)
                                                                ; Lnone dummy_var_info (aint) ] __m_ilen_write_upto8 [:: Pvar buf2_18455
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18457) (Pconst (8)%Z)
                                                                    ; Pvar t2_18466 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_18467.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf3_18456.(gv)
                                                                ; Lnone dummy_var_info (aint) ] __m_ilen_write_upto8 [:: Pvar buf3_18456
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18457) (Pconst (8)%Z)
                                                                    ; Pvar t3_18467 ]) ]
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
