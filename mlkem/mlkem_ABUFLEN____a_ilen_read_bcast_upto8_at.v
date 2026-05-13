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

(* ABUFLEN____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_14658 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14658).
Definition offset_14659 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14659).
Definition DELTA_14660 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14660).
Definition LEN_14661 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14661).
Definition TRAIL_14662 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14662).
Definition CUR_14663 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14663).
Definition AT_14664 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14664).
Definition w256_14665 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14665).
Definition AT8_14666 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14666).
Definition w_14667 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14667).
Definition t128_14668 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14668).

(* Signature *)
Definition tyin_ABUFLEN____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 536; aword U64; aint; aint; aint; aint; aint ].
Definition args_ABUFLEN____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_14658.(gv)
    ; offset_14659.(gv)
    ; DELTA_14660.(gv)
    ; LEN_14661.(gv)
    ; TRAIL_14662.(gv)
    ; CUR_14663.(gv)
    ; AT_14664.(gv) ].
Definition tyout_ABUFLEN____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_ABUFLEN____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_14660.(gv)
    ; LEN_14661.(gv)
    ; TRAIL_14662.(gv)
    ; AT_14664.(gv)
    ; w256_14665.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_ilen_read_bcast_upto8_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_14664) (Pvar CUR_14663)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_14663) (Pconst (8)%Z)) (Pvar AT_14664))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_14661) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_14662) (Pconst (0)%Z))))
        [:: copn [:: Lvar w256_14665.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ]
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_14661))
              [:: cassgn (Lvar AT8_14666.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_14664) (Pvar CUR_14663))
                ; copn [:: Lvar w256_14665.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_14658 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14659) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14660)))) ]
                ; ccall [:: Lvar w256_14665.(gv) ] __SHLQ_256 [:: Pvar w256_14665
                                                                ; Pvar AT8_14666 ]
                ; cassgn (Lvar DELTA_14660.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_14660) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_14666)))
                ; cassgn (Lvar LEN_14661.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14661) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_14666)))
                ; cassgn (Lvar AT_14664.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_14663) (Pconst (8)%Z)) ]
              [:: cassgn (Lvar AT8_14666.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_14664) (Pvar CUR_14663))
                ; ccall [:: Lvar DELTA_14660.(gv)
                          ; Lvar LEN_14661.(gv)
                          ; Lvar TRAIL_14662.(gv)
                          ; Lvar AT_14664.(gv)
                          ; Lvar w_14667.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_14658
                                                                    ; Pvar offset_14659
                                                                    ; Pvar DELTA_14660
                                                                    ; Pvar LEN_14661
                                                                    ; Pvar TRAIL_14662
                                                                    ; Pvar CUR_14663
                                                                    ; Pvar AT_14664 ]
                ; cassgn (Lvar t128_14668.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_14667))
                ; copn [:: Lvar w256_14665.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_14668 ]
                ; ccall [:: Lvar w256_14665.(gv) ] __SHLQ_256 [:: Pvar w256_14665
                                                                ; Pvar AT8_14666 ] ] ] ].

Definition fd_ABUFLEN____a_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____a_ilen_read_bcast_upto8_at;
    f_params := args_ABUFLEN____a_ilen_read_bcast_upto8_at;
    f_body := body_ABUFLEN____a_ilen_read_bcast_upto8_at;
    f_tyout := tyout_ABUFLEN____a_ilen_read_bcast_upto8_at;
    f_res := res_ABUFLEN____a_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
