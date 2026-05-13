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

(* __addstate_m_avx2x4 *)
(* Local variables *)
Definition st_18500 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 18500).
Definition AT_18501 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18501).
Definition buf0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18502).
Definition buf1 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18503).
Definition buf2 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18504).
Definition buf3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18505).
Definition _LEN_18506 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18506).
Definition _TRAILB_18507 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18507).
Definition AT8_18508 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18508).
Definition t0_18509 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18509).
Definition t1_18510 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18510).
Definition t2_18511 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18511).
Definition t3_18512 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18512).
Definition j_at_18513 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18513).

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
  [:: st_18500.(gv)
    ; AT_18501.(gv)
    ; buf0.(gv)
    ; buf1.(gv)
    ; buf2.(gv)
    ; buf3.(gv)
    ; _LEN_18506.(gv)
    ; _TRAILB_18507.(gv) ].
Definition tyout___addstate_m_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64; aword U64; aword U64; aword U64 ].
Definition res___addstate_m_avx2x4 : seq var_i :=
  [:: st_18500.(gv)
    ; AT_18501.(gv)
    ; buf0.(gv)
    ; buf1.(gv)
    ; buf2.(gv)
    ; buf3.(gv) ].

(* Body *)
Definition body___addstate_m_avx2x4 : cmd :=
  [:: cassgn (Lvar AT8_18508.(gv)) (aint) (Pvar AT_18501)
    ; cassgn (Lvar AT_18501.(gv)) (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18501) (Pconst (8)%Z)))
    ; cif
        (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_18508) (Pconst (8)%Z)) (Pconst (0)%Z))
        [:: ccall [:: Lvar buf0.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t0_18509.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf0
                                                                    ; Pvar _LEN_18506
                                                                    ; Pvar _TRAILB_18507
                                                                    ; Pvar AT_18501
                                                                    ; Pvar AT8_18508 ]
          ; cassgn (Laset Aligned AAscale U64 st_18500.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18501) (Pconst (8)%Z))) (Pconst (0)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18500 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18501) (Pconst (8)%Z))) (Pconst (0)%Z))) (Pvar t0_18509))
          ; ccall [:: Lvar buf1.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t1_18510.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf1
                                                                    ; Pvar _LEN_18506
                                                                    ; Pvar _TRAILB_18507
                                                                    ; Pvar AT_18501
                                                                    ; Pvar AT8_18508 ]
          ; cassgn (Laset Aligned AAscale U64 st_18500.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18501) (Pconst (8)%Z))) (Pconst (1)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18500 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18501) (Pconst (8)%Z))) (Pconst (1)%Z))) (Pvar t1_18510))
          ; ccall [:: Lvar buf2.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t2_18511.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf2
                                                                    ; Pvar _LEN_18506
                                                                    ; Pvar _TRAILB_18507
                                                                    ; Pvar AT_18501
                                                                    ; Pvar AT8_18508 ]
          ; cassgn (Laset Aligned AAscale U64 st_18500.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18501) (Pconst (8)%Z))) (Pconst (2)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18500 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18501) (Pconst (8)%Z))) (Pconst (2)%Z))) (Pvar t2_18511))
          ; ccall [:: Lvar buf3.(gv)
                    ; Lvar _LEN_18506.(gv)
                    ; Lvar _TRAILB_18507.(gv)
                    ; Lvar AT8_18508.(gv)
                    ; Lvar t3_18512.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf3
                                                                    ; Pvar _LEN_18506
                                                                    ; Pvar _TRAILB_18507
                                                                    ; Pvar AT_18501
                                                                    ; Pvar AT8_18508 ]
          ; cassgn (Laset Aligned AAscale U64 st_18500.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18501) (Pconst (8)%Z))) (Pconst (3)%Z))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18500 (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18501) (Pconst (8)%Z))) (Pconst (3)%Z))) (Pvar t3_18512))
          ; cassgn (Lvar AT_18501.(gv)) (aint) (Pvar AT8_18508) ]
        [::]
    ; cassgn (Lvar j_at_18513.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18501) (Pconst (8)%Z))))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18501) (Pconst (8)%Z))) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18506) (Pconst (8)%Z))))))
        [:: cassgn (Lvar t0_18509.(gv)) (aword U64) (Pload Unaligned U64 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf0)))
          ; cassgn (Lvar buf0.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf0) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Laset Aligned AAscale U64 st_18500.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18500 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_18509))
          ; cassgn (Lvar t1_18510.(gv)) (aword U64) (Pload Unaligned U64 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf1)))
          ; cassgn (Lvar buf1.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf1) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Laset Aligned AAscale U64 st_18500.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18500 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_18510))
          ; cassgn (Lvar t2_18511.(gv)) (aword U64) (Pload Unaligned U64 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf2)))
          ; cassgn (Lvar buf2.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf2) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Laset Aligned AAscale U64 st_18500.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18500 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_18511))
          ; cassgn (Lvar t3_18512.(gv)) (aword U64) (Pload Unaligned U64 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf3)))
          ; cassgn (Lvar buf3.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf3) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Laset Aligned AAscale U64 st_18500.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18500 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_18512))
          ; cassgn (Lvar j_at_18513.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (4)%Z))) ]
    ; cassgn (Lvar AT_18501.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_18501) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18506) (Pconst (8)%Z))))
    ; cassgn (Lvar _LEN_18506.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18506) (Pconst (8)%Z))
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_18506)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_18507) (Pconst (256)%Z)) (Pconst (0)%Z)))
        [:: ccall [:: Lvar buf0.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t0_18509.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf0
                                                                    ; Pvar _LEN_18506
                                                                    ; Pvar _TRAILB_18507
                                                                    ; Pvar AT_18501
                                                                    ; Pvar AT_18501 ]
          ; cassgn (Laset Aligned AAscale U64 st_18500.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18500 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (0)%Z))))) (Pvar t0_18509))
          ; ccall [:: Lvar buf1.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t1_18510.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf1
                                                                    ; Pvar _LEN_18506
                                                                    ; Pvar _TRAILB_18507
                                                                    ; Pvar AT_18501
                                                                    ; Pvar AT_18501 ]
          ; cassgn (Laset Aligned AAscale U64 st_18500.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18500 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (1)%Z))))) (Pvar t1_18510))
          ; ccall [:: Lvar buf2.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar t2_18511.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf2
                                                                    ; Pvar _LEN_18506
                                                                    ; Pvar _TRAILB_18507
                                                                    ; Pvar AT_18501
                                                                    ; Pvar AT_18501 ]
          ; cassgn (Laset Aligned AAscale U64 st_18500.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18500 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (2)%Z))))) (Pvar t2_18511))
          ; ccall [:: Lvar buf3.(gv)
                    ; Lnone dummy_var_info (aint)
                    ; Lnone dummy_var_info (aint)
                    ; Lvar AT_18501.(gv)
                    ; Lvar t3_18512.(gv) ] __m_ilen_read_upto8_at [:: Pvar buf3
                                                                    ; Pvar _LEN_18506
                                                                    ; Pvar _TRAILB_18507
                                                                    ; Pvar AT_18501
                                                                    ; Pvar AT_18501 ]
          ; cassgn (Laset Aligned AAscale U64 st_18500.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (aword U64) (Papp2 (Olxor U64) (Pget Aligned AAscale U64 st_18500 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at_18513) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (3)%Z))))) (Pvar t3_18512)) ]
        [::] ].

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
