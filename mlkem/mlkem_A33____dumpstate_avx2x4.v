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

(* A33____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_16929 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16929).
Definition buf1_16930 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16930).
Definition buf2_16931 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16931).
Definition buf3_16932 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16932).
Definition offset_16933 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16933).
Definition _LEN_16934 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16934).
Definition st_16935 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 16935).
Definition i_16936 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16936).
Definition x0_16937 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16937).
Definition x1_16938 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16938).
Definition x2_16939 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16939).
Definition x3_16940 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 16940).
Definition t0_16941 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16941).
Definition t1_16942 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16942).
Definition t2_16943 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16943).
Definition t3_16944 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16944).

(* Signature *)
Definition tyin_A33____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 33
    ; aarr U8 33
    ; aarr U8 33
    ; aarr U8 33
    ; aword U64
    ; aint
    ; aarr U256 25 ].
Definition args_A33____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_16929.(gv)
    ; buf1_16930.(gv)
    ; buf2_16931.(gv)
    ; buf3_16932.(gv)
    ; offset_16933.(gv)
    ; _LEN_16934.(gv)
    ; st_16935.(gv) ].
Definition tyout_A33____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 33; aarr U8 33; aarr U8 33; aarr U8 33; aword U64 ].
Definition res_A33____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_16929.(gv)
    ; buf1_16930.(gv)
    ; buf2_16931.(gv)
    ; buf3_16932.(gv)
    ; offset_16933.(gv) ].

(* Body *)
Definition body_A33____dumpstate_avx2x4 : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar i_16936.(gv)) AT_none (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16936) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16934) (Pconst (32)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar x0_16937.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_16935 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16936)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x1_16938.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_16935 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16936)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x2_16939.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_16935 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16936)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar x3_16940.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 st_16935 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16936)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_16936.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16936) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar x0_16937.(gv)
                                                                ; Lvar x1_16938.(gv)
                                                                ; Lvar x2_16939.(gv)
                                                                ; Lvar x3_16940.(gv) ] __4u64x4_u256x4 [:: Pvar x0_16937
                                                                    ; Pvar x1_16938
                                                                    ; Pvar x2_16939
                                                                    ; Pvar x3_16940 ])
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf0_16929.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16933))) AT_none (aword U256) (Pvar x0_16937))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf1_16930.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16933))) AT_none (aword U256) (Pvar x1_16938))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf2_16931.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16933))) AT_none (aword U256) (Pvar x2_16939))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 buf3_16932.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16933))) AT_none (aword U256) (Pvar x3_16940))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_16933.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16933) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))) ])
    ; MkI dummy_instr_info (Cwhile Align
                              [::]
                              (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_16936) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16934) (Pconst (8)%Z)))))
                              dummy_instr_info
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_16941.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_16935 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16936)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf0_16929.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16933))) AT_none (aword U64) (Pvar t0_16941))
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_16942.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_16935 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16936)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf1_16930.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16933))) AT_none (aword U64) (Pvar t1_16942))
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_16943.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_16935 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16936)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf2_16931.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16933))) AT_none (aword U64) (Pvar t2_16943))
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_16944.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_16935 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16936)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U64 buf3_16932.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16933))) AT_none (aword U64) (Pvar t3_16944))
                                ; MkI dummy_instr_info (Cassgn (Lvar i_16936.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_16936) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))))
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_16933.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16933) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))) ])
    ; MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16934) (Pconst (8)%Z)))
                              [:: MkI dummy_instr_info (Cassgn (Lvar t0_16941.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_16935 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16936)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf0_16929.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A33____a_ilen_write_upto8 [:: Pvar buf0_16929
                                                                    ; Pvar offset_16933
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16934) (Pconst (8)%Z)
                                                                    ; Pvar t0_16941 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t1_16942.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_16935 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16936)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf1_16930.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A33____a_ilen_write_upto8 [:: Pvar buf1_16930
                                                                    ; Pvar offset_16933
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16934) (Pconst (8)%Z)
                                                                    ; Pvar t1_16942 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t2_16943.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_16935 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16936)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf2_16931.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A33____a_ilen_write_upto8 [:: Pvar buf2_16931
                                                                    ; Pvar offset_16933
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16934) (Pconst (8)%Z)
                                                                    ; Pvar t2_16943 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar t3_16944.(gv)) AT_none (aword U64) (Pget Unaligned AAdirect U64 st_16935 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_16936)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z)))))))
                                ; MkI dummy_instr_info (Ccall [:: Lvar buf3_16932.(gv)
                                                                ; Lnone dummy_var_info (aint)
                                                                ; Lnone dummy_var_info (aint) ] A33____a_ilen_write_upto8 [:: Pvar buf3_16932
                                                                    ; Pvar offset_16933
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16934) (Pconst (8)%Z)
                                                                    ; Pvar t3_16944 ])
                                ; MkI dummy_instr_info (Cassgn (Lvar offset_16933.(gv)) AT_none (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16933) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16934) (Pconst (8)%Z))))) ]
                              [::]) ].

Definition fd_A33____dumpstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____dumpstate_avx2x4;
    f_params := args_A33____dumpstate_avx2x4;
    f_body := body_A33____dumpstate_avx2x4;
    f_tyout := tyout_A33____dumpstate_avx2x4;
    f_res := res_A33____dumpstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
