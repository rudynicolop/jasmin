From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi syntax data notations.

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
  [:: cassgn (Lvar i_18459.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_18459) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18457) (Pconst (32)%Z)))))
        [:: cassgn (Lvar x0_18460.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x1_18461.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x2_18462.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x3_18463.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar i_18459.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_18459) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))
          ; ccall [:: Lvar x0_18460.(gv)
                    ; Lvar x1_18461.(gv)
                    ; Lvar x2_18462.(gv)
                    ; Lvar x3_18463.(gv) ] __4u64x4_u256x4 [:: Pvar x0_18460
                                                             ; Pvar x1_18461
                                                             ; Pvar x2_18462
                                                             ; Pvar x3_18463 ]
          ; cassgn (Lmem Unaligned U256 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf0_18453))) (aword U256) (Pvar x0_18460)
          ; cassgn (Lvar buf0_18453.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf0_18453) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))
          ; cassgn (Lmem Unaligned U256 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf1_18454))) (aword U256) (Pvar x1_18461)
          ; cassgn (Lvar buf1_18454.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf1_18454) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))
          ; cassgn (Lmem Unaligned U256 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf2_18455))) (aword U256) (Pvar x2_18462)
          ; cassgn (Lvar buf2_18455.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf2_18455) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))
          ; cassgn (Lmem Unaligned U256 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf3_18456))) (aword U256) (Pvar x3_18463)
          ; cassgn (Lvar buf3_18456.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf3_18456) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))) ]
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_18459) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18457) (Pconst (8)%Z)))))
        [:: cassgn (Lvar t0_18464.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; cassgn (Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf0_18453) (Pvar i_18459)))) (aword U64) (Pvar t0_18464)
          ; cassgn (Lvar t1_18465.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; cassgn (Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf1_18454) (Pvar i_18459)))) (aword U64) (Pvar t1_18465)
          ; cassgn (Lvar t2_18466.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; cassgn (Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf2_18455) (Pvar i_18459)))) (aword U64) (Pvar t2_18466)
          ; cassgn (Lvar t3_18467.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; cassgn (Lmem Unaligned U64 dummy_var_info (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf3_18456) (Pvar i_18459)))) (aword U64) (Pvar t3_18467)
          ; cassgn (Lvar i_18459.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_18459) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
    ; cassgn (Lvar buf0_18453.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf0_18453) (Pvar i_18459))
    ; cassgn (Lvar buf1_18454.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf1_18454) (Pvar i_18459))
    ; cassgn (Lvar buf2_18455.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf2_18455) (Pvar i_18459))
    ; cassgn (Lvar buf3_18456.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf3_18456) (Pvar i_18459))
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18457) (Pconst (8)%Z)))
        [:: cassgn (Lvar t0_18464.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf0_18453.(gv); Lnone dummy_var_info (aint) ] __m_ilen_write_upto8 [:: Pvar buf0_18453
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18457) (Pconst (8)%Z)
                                                                    ; Pvar t0_18464 ]
          ; cassgn (Lvar t1_18465.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf1_18454.(gv); Lnone dummy_var_info (aint) ] __m_ilen_write_upto8 [:: Pvar buf1_18454
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18457) (Pconst (8)%Z)
                                                                    ; Pvar t1_18465 ]
          ; cassgn (Lvar t2_18466.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf2_18455.(gv); Lnone dummy_var_info (aint) ] __m_ilen_write_upto8 [:: Pvar buf2_18455
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18457) (Pconst (8)%Z)
                                                                    ; Pvar t2_18466 ]
          ; cassgn (Lvar t3_18467.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_18458 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_18459)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf3_18456.(gv); Lnone dummy_var_info (aint) ] __m_ilen_write_upto8 [:: Pvar buf3_18456
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18457) (Pconst (8)%Z)
                                                                    ; Pvar t3_18467 ] ]
        [::] ].

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
