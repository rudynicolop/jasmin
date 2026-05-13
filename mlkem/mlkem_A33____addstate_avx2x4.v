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

(* A33____addstate_avx2x4 *)
(* Local variables *)
Definition st_16979 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 16979).
Definition AT_16980 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16980).
Definition buf0_16981 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16981).
Definition buf1_16982 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16982).
Definition buf2_16983 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16983).
Definition buf3_16984 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 16984).
Definition offset_16985 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16985).
Definition _LEN_16986 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16986).
Definition _TRAILB_16987 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16987).
Definition DELTA_16988 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16988).
Definition AT8_16989 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16989).
Definition t0_16990 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16990).
Definition t1_16991 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16991).
Definition t2_16992 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16992).
Definition t3_16993 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16993).
Definition j_at_16994 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16994).

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
  [:: st_16979.(gv)
    ; AT_16980.(gv)
    ; buf0_16981.(gv)
    ; buf1_16982.(gv)
    ; buf2_16983.(gv)
    ; buf3_16984.(gv)
    ; offset_16985.(gv)
    ; _LEN_16986.(gv)
    ; _TRAILB_16987.(gv) ].
Definition tyout_A33____addstate_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64 ].
Definition res_A33____addstate_avx2x4 : seq var_i :=
  [:: st_16979.(gv); AT_16980.(gv); offset_16985.(gv) ].

(* Body *)
Definition body_A33____addstate_avx2x4 : cmd :=
  [:: cassgn (Lvar DELTA_16988.(gv)) (aint) (Pconst (0)%Z)
    ; cassgn (Lvar AT8_16989.(gv)) (aint) (Pvar AT_16980)
    ; cassgn (Lvar AT_16980.(gv)) (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16980) (Pconst (8)%Z)))
    ; cif
        (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_16989) (Pconst (8)%Z)) (Pconst (0)%Z))
        [:: ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t0_16990.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf0_16981
                                                                    ; Pvar offset_16985
                                                                    ; Pvar DELTA_16988
                                                                    ; Pvar _LEN_16986
                                                                    ; Pvar _TRAILB_16987
                                                                    ; Pvar AT_16980
                                                                    ; Pvar AT8_16989 ]
          ; cassgn (Laset Aligned AAscale U64 st_16979.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16980) (Pconst (8)%Z))) (Pconst (0)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16979 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16980) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_16990))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t1_16991.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf1_16982
                                                                    ; Pvar offset_16985
                                                                    ; Pvar DELTA_16988
                                                                    ; Pvar _LEN_16986
                                                                    ; Pvar _TRAILB_16987
                                                                    ; Pvar AT_16980
                                                                    ; Pvar AT8_16989 ]
          ; cassgn (Laset Aligned AAscale U64 st_16979.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16980) (Pconst (8)%Z))) (Pconst (1)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16979 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16980) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_16991))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t2_16992.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf2_16983
                                                                    ; Pvar offset_16985
                                                                    ; Pvar DELTA_16988
                                                                    ; Pvar _LEN_16986
                                                                    ; Pvar _TRAILB_16987
                                                                    ; Pvar AT_16980
                                                                    ; Pvar AT8_16989 ]
          ; cassgn (Laset Aligned AAscale U64 st_16979.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16980) (Pconst (8)%Z))) (Pconst (2)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16979 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16980) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_16992))
          ; ccall [:: Lvar DELTA_16988.(gv)
                    ; Lvar _LEN_16986.(gv)
                    ; Lvar _TRAILB_16987.(gv)
                    ; Lvar AT8_16989.(gv)
                    ; Lvar t3_16993.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf3_16984
                                                                    ; Pvar offset_16985
                                                                    ; Pvar DELTA_16988
                                                                    ; Pvar _LEN_16986
                                                                    ; Pvar _TRAILB_16987
                                                                    ; Pvar AT_16980
                                                                    ; Pvar AT8_16989 ]
          ; cassgn (Laset Aligned AAscale U64 st_16979.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16980) (Pconst (8)%Z))) (Pconst (3)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16979 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16980) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_16993))
          ; cassgn (Lvar AT_16980.(gv)) (aint) (Pvar AT8_16989) ]
        [::]
    ; cassgn (Lvar offset_16985.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16985) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16988)))
    ; cassgn (Lvar j_at_16994.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16980) (Pconst (8)%Z))))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_16980) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16986) (Pconst (8)%Z))))))
        [:: cassgn (Lvar t0_16990.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf0_16981 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16985)))
          ; cassgn (Laset Aligned AAscale U64 st_16979.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16979 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_16990))
          ; cassgn (Lvar t1_16991.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf1_16982 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16985)))
          ; cassgn (Laset Aligned AAscale U64 st_16979.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16979 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_16991))
          ; cassgn (Lvar t2_16992.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf2_16983 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16985)))
          ; cassgn (Laset Aligned AAscale U64 st_16979.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16979 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_16992))
          ; cassgn (Lvar t3_16993.(gv)) (aword U64) (Pget Unaligned AAdirect U64 buf3_16984 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar offset_16985)))
          ; cassgn (Lvar offset_16985.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16985) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Laset Aligned AAscale U64 st_16979.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16979 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_16993))
          ; cassgn (Lvar j_at_16994.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))) ]
    ; cassgn (Lvar AT_16980.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_16980) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_16986) (Pconst (8)%Z))))
    ; cassgn (Lvar _LEN_16986.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_16986) (Pconst (8)%Z))
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_16986)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_16987) (Pconst (256)%Z)) (Pconst (0)%Z)))
        [:: ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t0_16990.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf0_16981
                                                                    ; Pvar offset_16985
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_16986
                                                                    ; Pvar _TRAILB_16987
                                                                    ; Pvar AT_16980
                                                                    ; Pvar AT_16980 ]
          ; cassgn (Laset Aligned AAscale U64 st_16979.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16979 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_16990))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t1_16991.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf1_16982
                                                                    ; Pvar offset_16985
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_16986
                                                                    ; Pvar _TRAILB_16987
                                                                    ; Pvar AT_16980
                                                                    ; Pvar AT_16980 ]
          ; cassgn (Laset Aligned AAscale U64 st_16979.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16979 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_16991))
          ; ccall [:: Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t2_16992.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf2_16983
                                                                    ; Pvar offset_16985
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_16986
                                                                    ; Pvar _TRAILB_16987
                                                                    ; Pvar AT_16980
                                                                    ; Pvar AT_16980 ]
          ; cassgn (Laset Aligned AAscale U64 st_16979.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16979 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_16992))
          ; ccall [:: Lvar DELTA_16988.(gv)
                    ; Lvar _LEN_16986.(gv)
                    ; Lvar _TRAILB_16987.(gv)
                    ; Lvar AT_16980.(gv)
                    ; Lvar t3_16993.(gv) ] A33____a_ilen_read_upto8_at [:: Pvar buf3_16984
                                                                    ; Pvar offset_16985
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar _LEN_16986
                                                                    ; Pvar _TRAILB_16987
                                                                    ; Pvar AT_16980
                                                                    ; Pvar AT_16980 ]
          ; cassgn (Laset Aligned AAscale U64 st_16979.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_16979 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_16994) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_16993))
          ; cassgn (Lvar offset_16985.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16985) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16988))) ]
        [::] ].

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
