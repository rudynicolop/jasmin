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

(* A1568____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_15763 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15763).
Definition offset_15764 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15764).
Definition DELTA_15765 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15765).
Definition LEN_15766 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15766).
Definition w_15767 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15767).
Definition t128_15768 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15768).

(* Signature *)
Definition tyin_A1568____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 1568; aword U64; aint; aint; aword U256 ].
Definition args_A1568____a_ilen_write_upto32 : seq var_i :=
  [:: buf_15763.(gv)
    ; offset_15764.(gv)
    ; DELTA_15765.(gv)
    ; LEN_15766.(gv)
    ; w_15767.(gv) ].
Definition tyout_A1568____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 1568; aint; aint ].
Definition res_A1568____a_ilen_write_upto32 : seq var_i :=
  [:: buf_15763.(gv); DELTA_15765.(gv); LEN_15766.(gv) ].

(* Body *)
Definition body_A1568____a_ilen_write_upto32 : cmd :=
  [:: cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_15766))
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_15766))
              [:: cassgn (Laset Unaligned AAdirect U256 buf_15763.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15764) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15765))))) (aword U256) (Pvar w_15767)
                ; cassgn (Lvar DELTA_15765.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15765) (Pconst (32)%Z))
                ; cassgn (Lvar LEN_15766.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15766) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar t128_15768.(gv)) (aword U128) (Pvar w_15767)
                ; cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_15766))
                    [:: cassgn (Laset Unaligned AAdirect U128 buf_15763.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15764) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15765))))) (aword U128) (Pvar t128_15768)
                      ; cassgn (Lvar DELTA_15765.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15765) (Pconst (16)%Z))
                      ; cassgn (Lvar LEN_15766.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15766) (Pconst (16)%Z))
                      ; copn [:: Lvar t128_15768.(gv) ] (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_15767
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [::]
                ; ccall [:: Lvar buf_15763.(gv)
                          ; Lvar DELTA_15765.(gv)
                          ; Lvar LEN_15766.(gv) ] A1568____a_ilen_write_upto16 [:: Pvar buf_15763
                                                                    ; Pvar offset_15764
                                                                    ; Pvar DELTA_15765
                                                                    ; Pvar LEN_15766
                                                                    ; Pvar t128_15768 ] ] ]
        [::] ].

Definition fd_A1568____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____a_ilen_write_upto32;
    f_params := args_A1568____a_ilen_write_upto32;
    f_body := body_A1568____a_ilen_write_upto32;
    f_tyout := tyout_A1568____a_ilen_write_upto32;
    f_res := res_A1568____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
