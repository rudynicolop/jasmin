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

(* ABUFLEN____a_ilen_write_upto16 *)
(* Local variables *)
Definition buf_14631 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14631).
Definition offset_14632 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14632).
Definition DELTA_14633 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14633).
Definition LEN_14634 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14634).
Definition w_14635 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 14635).
Definition t64_14636 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14636).

(* Signature *)
Definition tyin_ABUFLEN____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 536; aword U64; aint; aint; aword U128 ].
Definition args_ABUFLEN____a_ilen_write_upto16 : seq var_i :=
  [:: buf_14631.(gv)
    ; offset_14632.(gv)
    ; DELTA_14633.(gv)
    ; LEN_14634.(gv)
    ; w_14635.(gv) ].
Definition tyout_ABUFLEN____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 536; aint; aint ].
Definition res_ABUFLEN____a_ilen_write_upto16 : seq var_i :=
  [:: buf_14631.(gv); DELTA_14633.(gv); LEN_14634.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_ilen_write_upto16 : cmd :=
  [:: cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_14634))
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_14634))
              [:: cassgn (Laset Unaligned AAdirect U128 buf_14631.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14632) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14633))))) (aword U128) (Pvar w_14635)
                ; cassgn (Lvar DELTA_14633.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_14633) (Pconst (16)%Z))
                ; cassgn (Lvar LEN_14634.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14634) (Pconst (16)%Z)) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_14634))
                    [:: copn [:: Laset Unaligned AAdirect U64 buf_14631.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14632) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14633)))) ] (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_14635 ]
                      ; cassgn (Lvar DELTA_14633.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_14633) (Pconst (8)%Z))
                      ; cassgn (Lvar LEN_14634.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14634) (Pconst (8)%Z))
                      ; copn [:: Lvar w_14635.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_14635
                                                                    ; Pvar w_14635 ] ]
                    [::]
                ; cassgn (Lvar t64_14636.(gv)) (aword U64) (Pvar w_14635)
                ; ccall [:: Lvar buf_14631.(gv)
                          ; Lvar DELTA_14633.(gv)
                          ; Lvar LEN_14634.(gv) ] ABUFLEN____a_ilen_write_upto8 [:: Pvar buf_14631
                                                                    ; Pvar offset_14632
                                                                    ; Pvar DELTA_14633
                                                                    ; Pvar LEN_14634
                                                                    ; Pvar t64_14636 ] ] ]
        [::] ].

Definition fd_ABUFLEN____a_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____a_ilen_write_upto16;
    f_params := args_ABUFLEN____a_ilen_write_upto16;
    f_body := body_ABUFLEN____a_ilen_write_upto16;
    f_tyout := tyout_ABUFLEN____a_ilen_write_upto16;
    f_res := res_ABUFLEN____a_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
