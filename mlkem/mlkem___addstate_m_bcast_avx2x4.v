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

(* __addstate_m_bcast_avx2x4 *)
(* Local variables *)
Definition st_18544 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 18544).
Definition AT_18545 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18545).
Definition buf_18546 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18546).
Definition _LEN_18547 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18547).
Definition _TRAILB_18548 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18548).
Definition AT8_18549 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18549).
Definition w_18550 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18550).
Definition j_at : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 18551).

(* Signature *)
Definition tyin___addstate_m_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint; aword U64; aint; aint ].
Definition args___addstate_m_bcast_avx2x4 : seq var_i :=
  [:: st_18544.(gv)
    ; AT_18545.(gv)
    ; buf_18546.(gv)
    ; _LEN_18547.(gv)
    ; _TRAILB_18548.(gv) ].
Definition tyout___addstate_m_bcast_avx2x4 : seq atype :=
  [:: aarr U256 25; aint ].
Definition res___addstate_m_bcast_avx2x4 : seq var_i :=
  [:: st_18544.(gv); AT_18545.(gv) ].

(* Body *)
Definition body___addstate_m_bcast_avx2x4 : cmd :=
  [:: cassgn (Lvar AT8_18549.(gv)) (aint) (Pvar AT_18545)
    ; cassgn (Lvar AT_18545.(gv)) (aint) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18545) (Pconst (8)%Z)))
    ; cif
        (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar AT8_18549) (Pconst (8)%Z)) (Pconst (0)%Z))
        [:: ccall [:: Lvar buf_18546.(gv)
                    ; Lvar _LEN_18547.(gv)
                    ; Lvar _TRAILB_18548.(gv)
                    ; Lvar AT8_18549.(gv)
                    ; Lvar w_18550.(gv) ] __m_ilen_read_bcast_upto8_at [:: Pvar buf_18546
                                                                    ; Pvar _LEN_18547
                                                                    ; Pvar _TRAILB_18548
                                                                    ; Pvar AT_18545
                                                                    ; Pvar AT8_18549 ]
          ; cassgn (Lvar w_18550.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_18550) (Pget Aligned AAscale U256 st_18544 (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18545) (Pconst (8)%Z))))
          ; cassgn (Laset Aligned AAscale U256 st_18544.(gv) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18545) (Pconst (8)%Z))) (aword U256) (Pvar w_18550)
          ; cassgn (Lvar AT_18545.(gv)) (aint) (Pvar AT8_18549) ]
        [::]
    ; cassgn (Lvar j_at.(gv)) (aword U64) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18545) (Pconst (8)%Z))))
    ; cwhile
        [::]
        (Papp2 (Owi2 Unsigned U64 WIlt) (Pvar j_at) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Papp2 (Oadd (Op_int)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar AT_18545) (Pconst (8)%Z)) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18547) (Pconst (8)%Z))))))
        [:: copn [:: Lvar w_18550.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pload Unaligned U64 (Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar buf_18546)) ]
          ; cassgn (Lvar buf_18546.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar buf_18546) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (8)%Z)))
          ; cassgn (Lvar w_18550.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_18550) (Pget Unaligned AAdirect U256 st_18544 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at))))
          ; cassgn (Laset Unaligned AAdirect U256 st_18544.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at))) (aword U256) (Pvar w_18550)
          ; cassgn (Lvar j_at.(gv)) (aword U64) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar j_at) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst (32)%Z))) ]
    ; cassgn (Lvar AT_18545.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar AT_18545) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Papp2 (Odiv Unsigned (Op_int)) (Pvar _LEN_18547) (Pconst (8)%Z))))
    ; cassgn (Lvar _LEN_18547.(gv)) (aint) (Papp2 (Omod Unsigned (Op_int)) (Pvar _LEN_18547) (Pconst (8)%Z))
    ; cif
        (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar _LEN_18547)) (Papp2 (Oneq (Op_int)) (Papp2 (Omod Unsigned (Op_int)) (Pvar _TRAILB_18548) (Pconst (256)%Z)) (Pconst (0)%Z)))
        [:: ccall [:: Lvar buf_18546.(gv)
                    ; Lvar _LEN_18547.(gv)
                    ; Lvar _TRAILB_18548.(gv)
                    ; Lvar AT_18545.(gv)
                    ; Lvar w_18550.(gv) ] __m_ilen_read_bcast_upto8_at [:: Pvar buf_18546
                                                                    ; Pvar _LEN_18547
                                                                    ; Pvar _TRAILB_18548
                                                                    ; Pvar AT_18545
                                                                    ; Pvar AT_18545 ]
          ; cassgn (Lvar w_18550.(gv)) (aword U256) (Papp2 (Olxor U256) (Pvar w_18550) (Pget Unaligned AAdirect U256 st_18544 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at))))
          ; cassgn (Laset Unaligned AAdirect U256 st_18544.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar j_at))) (aword U256) (Pvar w_18550) ]
        [::] ].

Definition fd___addstate_m_bcast_avx2x4 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___addstate_m_bcast_avx2x4;
    f_params := args___addstate_m_bcast_avx2x4;
    f_body := body___addstate_m_bcast_avx2x4;
    f_tyout := tyout___addstate_m_bcast_avx2x4;
    f_res := res___addstate_m_bcast_avx2x4;
    f_extra := tt;
  |}.

End IDO.
