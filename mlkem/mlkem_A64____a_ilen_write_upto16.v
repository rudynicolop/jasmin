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

(* A64____a_ilen_write_upto16 *)
(* Local variables *)
Definition buf_16788 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 16788).
Definition offset_16789 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16789).
Definition DELTA_16790 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16790).
Definition LEN_16791 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16791).
Definition w_16792 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 16792).
Definition t64_16793 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16793).

(* Signature *)
Definition tyin_A64____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 64; aword U64; aint; aint; aword U128 ].
Definition args_A64____a_ilen_write_upto16 : seq var_i :=
  [:: buf_16788.(gv)
    ; offset_16789.(gv)
    ; DELTA_16790.(gv)
    ; LEN_16791.(gv)
    ; w_16792.(gv) ].
Definition tyout_A64____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 64; aint; aint ].
Definition res_A64____a_ilen_write_upto16 : seq var_i :=
  [:: buf_16788.(gv); DELTA_16790.(gv); LEN_16791.(gv) ].

(* Body *)
Definition body_A64____a_ilen_write_upto16 : cmd :=
  [:: cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_16791))
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_16791))
              [:: cassgn (Laset Unaligned AAdirect U128 buf_16788.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16789) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16790))))) (aword U128) (Pvar w_16792)
                ; cassgn (Lvar DELTA_16790.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16790) (Pconst (16)%Z))
                ; cassgn (Lvar LEN_16791.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16791) (Pconst (16)%Z)) ]
              [:: cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_16791))
                    [:: copn [:: Laset Unaligned AAdirect U64 buf_16788.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16789) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16790)))) ] (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_16792 ]
                      ; cassgn (Lvar DELTA_16790.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16790) (Pconst (8)%Z))
                      ; cassgn (Lvar LEN_16791.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16791) (Pconst (8)%Z))
                      ; copn [:: Lvar w_16792.(gv) ] (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_16792
                                                                    ; Pvar w_16792 ] ]
                    [::]
                ; cassgn (Lvar t64_16793.(gv)) (aword U64) (Pvar w_16792)
                ; ccall [:: Lvar buf_16788.(gv)
                          ; Lvar DELTA_16790.(gv)
                          ; Lvar LEN_16791.(gv) ] A64____a_ilen_write_upto8 [:: Pvar buf_16788
                                                                    ; Pvar offset_16789
                                                                    ; Pvar DELTA_16790
                                                                    ; Pvar LEN_16791
                                                                    ; Pvar t64_16793 ] ] ]
        [::] ].

Definition fd_A64____a_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____a_ilen_write_upto16;
    f_params := args_A64____a_ilen_write_upto16;
    f_body := body_A64____a_ilen_write_upto16;
    f_tyout := tyout_A64____a_ilen_write_upto16;
    f_res := res_A64____a_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
