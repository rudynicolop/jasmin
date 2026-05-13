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

(* A64____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_16774 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 64) (mkident 16774).
Definition offset_16775 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16775).
Definition DELTA_16776 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16776).
Definition LEN_16777 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16777).
Definition w_16778 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16778).
Definition t128_16779 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 16779).

(* Signature *)
Definition tyin_A64____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 64; aword U64; aint; aint; aword U256 ].
Definition args_A64____a_ilen_write_upto32 : seq var_i :=
  [:: buf_16774.(gv)
    ; offset_16775.(gv)
    ; DELTA_16776.(gv)
    ; LEN_16777.(gv)
    ; w_16778.(gv) ].
Definition tyout_A64____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 64; aint; aint ].
Definition res_A64____a_ilen_write_upto32 : seq var_i :=
  [:: buf_16774.(gv); DELTA_16776.(gv); LEN_16777.(gv) ].

(* Body *)
Definition body_A64____a_ilen_write_upto32 : cmd :=
  [:: cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_16777))
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_16777))
              [:: cassgn (Laset Unaligned AAdirect U256 buf_16774.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16775) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16776))))) (aword U256) (Pvar w_16778)
                ; cassgn (Lvar DELTA_16776.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16776) (Pconst (32)%Z))
                ; cassgn (Lvar LEN_16777.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16777) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar t128_16779.(gv)) (aword U128) (Pvar w_16778)
                ; cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_16777))
                    [:: cassgn (Laset Unaligned AAdirect U128 buf_16774.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_16775) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_16776))))) (aword U128) (Pvar t128_16779)
                      ; cassgn (Lvar DELTA_16776.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_16776) (Pconst (16)%Z))
                      ; cassgn (Lvar LEN_16777.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_16777) (Pconst (16)%Z))
                      ; copn [:: Lvar t128_16779.(gv) ] (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_16778
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [::]
                ; ccall [:: Lvar buf_16774.(gv)
                          ; Lvar DELTA_16776.(gv)
                          ; Lvar LEN_16777.(gv) ] A64____a_ilen_write_upto16 [:: Pvar buf_16774
                                                                    ; Pvar offset_16775
                                                                    ; Pvar DELTA_16776
                                                                    ; Pvar LEN_16777
                                                                    ; Pvar t128_16779 ] ] ]
        [::] ].

Definition fd_A64____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____a_ilen_write_upto32;
    f_params := args_A64____a_ilen_write_upto32;
    f_body := body_A64____a_ilen_write_upto32;
    f_tyout := tyout_A64____a_ilen_write_upto32;
    f_res := res_A64____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
