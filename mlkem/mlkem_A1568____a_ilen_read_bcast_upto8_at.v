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

(* A1568____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_15804 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15804).
Definition offset_15805 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15805).
Definition DELTA_15806 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15806).
Definition LEN_15807 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15807).
Definition TRAIL_15808 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15808).
Definition CUR_15809 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15809).
Definition AT_15810 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15810).
Definition w256_15811 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 15811).
Definition AT8_15812 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15812).
Definition w_15813 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15813).
Definition t128_15814 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15814).

(* Signature *)
Definition tyin_A1568____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 1568; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1568____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_15804.(gv)
    ; offset_15805.(gv)
    ; DELTA_15806.(gv)
    ; LEN_15807.(gv)
    ; TRAIL_15808.(gv)
    ; CUR_15809.(gv)
    ; AT_15810.(gv) ].
Definition tyout_A1568____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A1568____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_15806.(gv)
    ; LEN_15807.(gv)
    ; TRAIL_15808.(gv)
    ; AT_15810.(gv)
    ; w256_15811.(gv) ].

(* Body *)
Definition body_A1568____a_ilen_read_bcast_upto8_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_15810) (Pvar CUR_15809)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_15809) (Pconst (8)%Z)) (Pvar AT_15810))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_15807) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_15808) (Pconst (0)%Z))))
        [:: copn [:: Lvar w256_15811.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ]
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_15807))
              [:: cassgn (Lvar AT8_15812.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_15810) (Pvar CUR_15809))
                ; copn [:: Lvar w256_15811.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_15804 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15805) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15806)))) ]
                ; ccall [:: Lvar w256_15811.(gv) ] __SHLQ_256 [:: Pvar w256_15811
                                                                ; Pvar AT8_15812 ]
                ; cassgn (Lvar DELTA_15806.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15806) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15812)))
                ; cassgn (Lvar LEN_15807.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15807) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_15812)))
                ; cassgn (Lvar AT_15810.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_15809) (Pconst (8)%Z)) ]
              [:: cassgn (Lvar AT8_15812.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_15810) (Pvar CUR_15809))
                ; ccall [:: Lvar DELTA_15806.(gv)
                          ; Lvar LEN_15807.(gv)
                          ; Lvar TRAIL_15808.(gv)
                          ; Lvar AT_15810.(gv)
                          ; Lvar w_15813.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_15804
                                                                    ; Pvar offset_15805
                                                                    ; Pvar DELTA_15806
                                                                    ; Pvar LEN_15807
                                                                    ; Pvar TRAIL_15808
                                                                    ; Pvar CUR_15809
                                                                    ; Pvar AT_15810 ]
                ; cassgn (Lvar t128_15814.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_15813))
                ; copn [:: Lvar w256_15811.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_15814 ]
                ; ccall [:: Lvar w256_15811.(gv) ] __SHLQ_256 [:: Pvar w256_15811
                                                                ; Pvar AT8_15812 ] ] ] ].

Definition fd_A1568____a_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____a_ilen_read_bcast_upto8_at;
    f_params := args_A1568____a_ilen_read_bcast_upto8_at;
    f_body := body_A1568____a_ilen_read_bcast_upto8_at;
    f_tyout := tyout_A1568____a_ilen_read_bcast_upto8_at;
    f_res := res_A1568____a_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
