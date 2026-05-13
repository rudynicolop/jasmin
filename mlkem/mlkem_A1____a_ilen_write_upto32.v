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

(* A1____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_18302 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1) (mkident 18302).
Definition offset_18303 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 18303).
Definition DELTA_18304 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18304).
Definition LEN_18305 : gvar := mk_rocq_gvar Slocal (aint) (mkident 18305).
Definition w_18306 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 18306).
Definition t128_18307 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 18307).

(* Signature *)
Definition tyin_A1____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 1; aword U64; aint; aint; aword U256 ].
Definition args_A1____a_ilen_write_upto32 : seq var_i :=
  [:: buf_18302.(gv)
    ; offset_18303.(gv)
    ; DELTA_18304.(gv)
    ; LEN_18305.(gv)
    ; w_18306.(gv) ].
Definition tyout_A1____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 1; aint; aint ].
Definition res_A1____a_ilen_write_upto32 : seq var_i :=
  [:: buf_18302.(gv); DELTA_18304.(gv); LEN_18305.(gv) ].

(* Body *)
Definition body_A1____a_ilen_write_upto32 : cmd :=
  [:: cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_18305))
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_18305))
              [:: cassgn (Laset Unaligned AAdirect U256 buf_18302.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18303) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18304))))) (aword U256) (Pvar w_18306)
                ; cassgn (Lvar DELTA_18304.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18304) (Pconst (32)%Z))
                ; cassgn (Lvar LEN_18305.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18305) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar t128_18307.(gv)) (aword U128) (Pvar w_18306)
                ; cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_18305))
                    [:: cassgn (Laset Unaligned AAdirect U128 buf_18302.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_18303) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_18304))))) (aword U128) (Pvar t128_18307)
                      ; cassgn (Lvar DELTA_18304.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_18304) (Pconst (16)%Z))
                      ; cassgn (Lvar LEN_18305.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18305) (Pconst (16)%Z))
                      ; copn [:: Lvar t128_18307.(gv) ] (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_18306
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [::]
                ; ccall [:: Lvar buf_18302.(gv)
                          ; Lvar DELTA_18304.(gv)
                          ; Lvar LEN_18305.(gv) ] A1____a_ilen_write_upto16 [:: Pvar buf_18302
                                                                    ; Pvar offset_18303
                                                                    ; Pvar DELTA_18304
                                                                    ; Pvar LEN_18305
                                                                    ; Pvar t128_18307 ] ] ]
        [::] ].

Definition fd_A1____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1____a_ilen_write_upto32;
    f_params := args_A1____a_ilen_write_upto32;
    f_body := body_A1____a_ilen_write_upto32;
    f_tyout := tyout_A1____a_ilen_write_upto32;
    f_res := res_A1____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
