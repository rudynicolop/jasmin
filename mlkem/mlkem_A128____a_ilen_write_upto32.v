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

(* A128____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_16527 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 16527).
Definition offset_16528 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16528).
Definition DELTA_16529 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16529).
Definition LEN_16530 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16530).
Definition w_16531 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16531).
Definition t128_16532 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16532).

(* Signature *)
Definition tyin_A128____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 128; aword U64; aint; aint; aword U256 ].
Definition args_A128____a_ilen_write_upto32 : seq var_i :=
  [:: buf_16527.(gv)
    ; offset_16528.(gv)
    ; DELTA_16529.(gv)
    ; LEN_16530.(gv)
    ; w_16531.(gv) ].
Definition tyout_A128____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 128; aint; aint ].
Definition res_A128____a_ilen_write_upto32 : seq var_i :=
  [:: buf_16527.(gv); DELTA_16529.(gv); LEN_16530.(gv) ].

(* Body *)
Definition body_A128____a_ilen_write_upto32 : cmd :=
  [:: cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_16530))
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_16530))
              [:: cassgn (Laset Unaligned AAdirect U256 buf_16527.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16528) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16529))))) (aword U256) (Pvar w_16531)
                ; cassgn (Lvar DELTA_16529.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16529) (Pconst (32)%Z))
                ; cassgn (Lvar LEN_16530.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16530) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar t128_16532.(gv)) (aword U128) (Pvar w_16531)
                ; cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_16530))
                    [:: cassgn (Laset Unaligned AAdirect U128 buf_16527.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16528) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16529))))) (aword U128) (Pvar t128_16532)
                      ; cassgn (Lvar DELTA_16529.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16529) (Pconst (16)%Z))
                      ; cassgn (Lvar LEN_16530.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16530) (Pconst (16)%Z))
                      ; copn [:: Lvar t128_16532.(gv) ] (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_16531
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [::]
                ; ccall [:: Lvar buf_16527.(gv)
                          ; Lvar DELTA_16529.(gv)
                          ; Lvar LEN_16530.(gv) ] A128____a_ilen_write_upto16 [:: Pvar buf_16527
                                                                    ; Pvar offset_16528
                                                                    ; Pvar DELTA_16529
                                                                    ; Pvar LEN_16530
                                                                    ; Pvar t128_16532 ] ] ]
        [::] ].

Definition fd_A128____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____a_ilen_write_upto32;
    f_params := args_A128____a_ilen_write_upto32;
    f_body := body_A128____a_ilen_write_upto32;
    f_tyout := tyout_A128____a_ilen_write_upto32;
    f_res := res_A128____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
