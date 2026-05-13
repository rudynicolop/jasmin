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

(* A1120____dumpstate_avx2x4 *)
(* Local variables *)
Definition buf0_15154 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15154).
Definition buf1_15155 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15155).
Definition buf2_15156 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15156).
Definition buf3_15157 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15157).
Definition offset_15158 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15158).
Definition _LEN_15159 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15159).
Definition st_15160 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 15160).
Definition i_15161 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15161).
Definition x0_15162 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15162).
Definition x1_15163 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15163).
Definition x2_15164 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15164).
Definition x3_15165 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15165).
Definition t0_15166 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15166).
Definition t1_15167 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15167).
Definition t2_15168 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15168).
Definition t3_15169 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15169).

(* Signature *)
Definition tyin_A1120____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1120
    ; aarr U8 1120
    ; aarr U8 1120
    ; aarr U8 1120
    ; aword U64
    ; aint
    ; aarr U256 25 ].
Definition args_A1120____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_15154.(gv)
    ; buf1_15155.(gv)
    ; buf2_15156.(gv)
    ; buf3_15157.(gv)
    ; offset_15158.(gv)
    ; _LEN_15159.(gv)
    ; st_15160.(gv) ].
Definition tyout_A1120____dumpstate_avx2x4 : seq atype :=
  [:: aarr U8 1120; aarr U8 1120; aarr U8 1120; aarr U8 1120; aword U64 ].
Definition res_A1120____dumpstate_avx2x4 : seq var_i :=
  [:: buf0_15154.(gv)
    ; buf1_15155.(gv)
    ; buf2_15156.(gv)
    ; buf3_15157.(gv)
    ; offset_15158.(gv) ].

(* Body *)
Definition body_A1120____dumpstate_avx2x4 : cmd :=
  [:: cassgn (Lvar i_15161.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15161) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15159) (Pconst (32)%Z)))))
        [:: cassgn (Lvar x0_15162.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_15160 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15161)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x1_15163.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_15160 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15161)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x2_15164.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_15160 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15161)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar x3_15165.(gv)) (aword U256) (Pget Unaligned AAdirect U256 st_15160 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15161)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (32)%Z))))))
          ; cassgn (Lvar i_15161.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15161) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z)))
          ; ccall [:: Lvar x0_15162.(gv)
                    ; Lvar x1_15163.(gv)
                    ; Lvar x2_15164.(gv)
                    ; Lvar x3_15165.(gv) ] __4u64x4_u256x4 [:: Pvar x0_15162
                                                             ; Pvar x1_15163
                                                             ; Pvar x2_15164
                                                             ; Pvar x3_15165 ]
          ; cassgn (Laset Unaligned AAdirect U256 buf0_15154.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15158))) (aword U256) (Pvar x0_15162)
          ; cassgn (Laset Unaligned AAdirect U256 buf1_15155.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15158))) (aword U256) (Pvar x1_15163)
          ; cassgn (Laset Unaligned AAdirect U256 buf2_15156.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15158))) (aword U256) (Pvar x2_15164)
          ; cassgn (Laset Unaligned AAdirect U256 buf3_15157.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15158))) (aword U256) (Pvar x3_15165)
          ; cassgn (Lvar offset_15158.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15158) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))) ]
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar i_15161) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_15159) (Pconst (8)%Z)))))
        [:: cassgn (Lvar t0_15166.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15160 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15161)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf0_15154.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15158))) (aword U64) (Pvar t0_15166)
          ; cassgn (Lvar t1_15167.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15160 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15161)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf1_15155.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15158))) (aword U64) (Pvar t1_15167)
          ; cassgn (Lvar t2_15168.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15160 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15161)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf2_15156.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15158))) (aword U64) (Pvar t2_15168)
          ; cassgn (Lvar t3_15169.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15160 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15161)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; cassgn (Laset Unaligned AAdirect U64 buf3_15157.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_15158))) (aword U64) (Pvar t3_15169)
          ; cassgn (Lvar i_15161.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar i_15161) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Lvar offset_15158.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15158) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z))) ]
    ; cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15159) (Pconst (8)%Z)))
        [:: cassgn (Lvar t0_15166.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15160 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15161)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf0_15154.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1120____a_ilen_write_upto8 [:: Pvar buf0_15154
                                                                    ; Pvar offset_15158
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15159) (Pconst (8)%Z)
                                                                    ; Pvar t0_15166 ]
          ; cassgn (Lvar t1_15167.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15160 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15161)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf1_15155.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1120____a_ilen_write_upto8 [:: Pvar buf1_15155
                                                                    ; Pvar offset_15158
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15159) (Pconst (8)%Z)
                                                                    ; Pvar t1_15167 ]
          ; cassgn (Lvar t2_15168.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15160 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15161)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf2_15156.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1120____a_ilen_write_upto8 [:: Pvar buf2_15156
                                                                    ; Pvar offset_15158
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15159) (Pconst (8)%Z)
                                                                    ; Pvar t2_15168 ]
          ; cassgn (Lvar t3_15169.(gv)) (aword U64) (Pget Unaligned AAdirect U64 st_15160 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Papp2 (Owi2 Unsigned U64 WImul) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z)) (Pvar i_15161)) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (8)%Z))))))
          ; ccall [:: Lvar buf3_15157.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint) ] A1120____a_ilen_write_upto8 [:: Pvar buf3_15157
                                                                    ; Pvar offset_15158
                                                                    ; Pconst (0)%Z
                                                                    ; Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15159) (Pconst (8)%Z)
                                                                    ; Pvar t3_15169 ]
          ; cassgn (Lvar offset_15158.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15158) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_15159) (Pconst (8)%Z)))) ]
        [::] ].

Definition fd_A1120____dumpstate_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____dumpstate_avx2x4;
    f_params := args_A1120____dumpstate_avx2x4;
    f_body := body_A1120____dumpstate_avx2x4;
    f_tyout := tyout_A1120____dumpstate_avx2x4;
    f_res := res_A1120____dumpstate_avx2x4;
    f_extra := tt;
  |}.

End IDO.
