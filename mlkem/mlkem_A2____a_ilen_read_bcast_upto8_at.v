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

(* A2____a_ilen_read_bcast_upto8_at *)
(* Local variables *)
Definition buf_17961 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17961).
Definition offset_17962 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17962).
Definition DELTA_17963 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17963).
Definition LEN_17964 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17964).
Definition TRAIL_17965 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17965).
Definition CUR_17966 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17966).
Definition AT_17967 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17967).
Definition w256_17968 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 17968).
Definition AT8_17969 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17969).
Definition w_17970 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17970).
Definition t128_17971 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17971).

(* Signature *)
Definition tyin_A2____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aarr U8 2; aword U64; aint; aint; aint; aint; aint ].
Definition args_A2____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: buf_17961.(gv)
    ; offset_17962.(gv)
    ; DELTA_17963.(gv)
    ; LEN_17964.(gv)
    ; TRAIL_17965.(gv)
    ; CUR_17966.(gv)
    ; AT_17967.(gv) ].
Definition tyout_A2____a_ilen_read_bcast_upto8_at : seq atype :=
  [:: aint; aint; aint; aint; aword U256 ].
Definition res_A2____a_ilen_read_bcast_upto8_at : seq var_i :=
  [:: DELTA_17963.(gv)
    ; LEN_17964.(gv)
    ; TRAIL_17965.(gv)
    ; AT_17967.(gv)
    ; w256_17968.(gv) ].

(* Body *)
Definition body_A2____a_ilen_read_bcast_upto8_at : cmd :=
  [:: cif
        (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_17967) (Pvar CUR_17966)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_17966) (Pconst (8)%Z)) (Pvar AT_17967))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_17964) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_17965) (Pconst (0)%Z))))
        [:: copn [:: Lvar w256_17968.(gv) ] (Oasm ((ExtOp (Oset0 U256)))) [::] ]
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_17964))
              [:: cassgn (Lvar AT8_17969.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_17967) (Pvar CUR_17966))
                ; copn [:: Lvar w256_17968.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pget Unaligned AAdirect U64 buf_17961 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17962) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17963)))) ]
                ; ccall [:: Lvar w256_17968.(gv) ] __SHLQ_256 [:: Pvar w256_17968
                                                                ; Pvar AT8_17969 ]
                ; cassgn (Lvar DELTA_17963.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17963) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17969)))
                ; cassgn (Lvar LEN_17964.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17964) (Papp2 (Osub (Op_int)) (Pconst (8)%Z) (Pvar AT8_17969)))
                ; cassgn (Lvar AT_17967.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_17966) (Pconst (8)%Z)) ]
              [:: cassgn (Lvar AT8_17969.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar AT_17967) (Pvar CUR_17966))
                ; ccall [:: Lvar DELTA_17963.(gv)
                          ; Lvar LEN_17964.(gv)
                          ; Lvar TRAIL_17965.(gv)
                          ; Lvar AT_17967.(gv)
                          ; Lvar w_17970.(gv) ] A2____a_ilen_read_upto8_at [:: Pvar buf_17961
                                                                    ; Pvar offset_17962
                                                                    ; Pvar DELTA_17963
                                                                    ; Pvar LEN_17964
                                                                    ; Pvar TRAIL_17965
                                                                    ; Pvar CUR_17966
                                                                    ; Pvar AT_17967 ]
                ; cassgn (Lvar t128_17971.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar w_17970))
                ; copn [:: Lvar w256_17968.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar t128_17971 ]
                ; ccall [:: Lvar w256_17968.(gv) ] __SHLQ_256 [:: Pvar w256_17968
                                                                ; Pvar AT8_17969 ] ] ] ].

Definition fd_A2____a_ilen_read_bcast_upto8_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____a_ilen_read_bcast_upto8_at;
    f_params := args_A2____a_ilen_read_bcast_upto8_at;
    f_body := body_A2____a_ilen_read_bcast_upto8_at;
    f_tyout := tyout_A2____a_ilen_read_bcast_upto8_at;
    f_res := res_A2____a_ilen_read_bcast_upto8_at;
    f_extra := tt;
  |}.

End IDO.
