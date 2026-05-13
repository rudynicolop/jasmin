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

(* A2____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_17920 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17920).
Definition offset_17921 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17921).
Definition DELTA_17922 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17922).
Definition LEN_17923 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17923).
Definition w_17924 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17924).
Definition t128_17925 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17925).

(* Signature *)
Definition tyin_A2____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 2; aword U64; aint; aint; aword U256 ].
Definition args_A2____a_ilen_write_upto32 : seq var_i :=
  [:: buf_17920.(gv)
    ; offset_17921.(gv)
    ; DELTA_17922.(gv)
    ; LEN_17923.(gv)
    ; w_17924.(gv) ].
Definition tyout_A2____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 2; aint; aint ].
Definition res_A2____a_ilen_write_upto32 : seq var_i :=
  [:: buf_17920.(gv); DELTA_17922.(gv); LEN_17923.(gv) ].

(* Body *)
Definition body_A2____a_ilen_write_upto32 : cmd :=
  [:: cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_17923))
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_17923))
              [:: cassgn (Laset Unaligned AAdirect U256 buf_17920.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17921) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17922))))) (aword U256) (Pvar w_17924)
                ; cassgn (Lvar DELTA_17922.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17922) (Pconst (32)%Z))
                ; cassgn (Lvar LEN_17923.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17923) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar t128_17925.(gv)) (aword U128) (Pvar w_17924)
                ; cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_17923))
                    [:: cassgn (Laset Unaligned AAdirect U128 buf_17920.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17921) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17922))))) (aword U128) (Pvar t128_17925)
                      ; cassgn (Lvar DELTA_17922.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17922) (Pconst (16)%Z))
                      ; cassgn (Lvar LEN_17923.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17923) (Pconst (16)%Z))
                      ; copn [:: Lvar t128_17925.(gv) ] (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_17924
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [::]
                ; ccall [:: Lvar buf_17920.(gv)
                          ; Lvar DELTA_17922.(gv)
                          ; Lvar LEN_17923.(gv) ] A2____a_ilen_write_upto16 [:: Pvar buf_17920
                                                                    ; Pvar offset_17921
                                                                    ; Pvar DELTA_17922
                                                                    ; Pvar LEN_17923
                                                                    ; Pvar t128_17925 ] ] ]
        [::] ].

Definition fd_A2____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____a_ilen_write_upto32;
    f_params := args_A2____a_ilen_write_upto32;
    f_body := body_A2____a_ilen_write_upto32;
    f_tyout := tyout_A2____a_ilen_write_upto32;
    f_res := res_A2____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
