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

(* A33____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_17156 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 33) (mkident 17156).
Definition offset_17157 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17157).
Definition DELTA_17158 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17158).
Definition LEN_17159 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17159).
Definition w_17160 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17160).
Definition t128_17161 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 17161).

(* Signature *)
Definition tyin_A33____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 33; aword U64; aint; aint; aword U256 ].
Definition args_A33____a_ilen_write_upto32 : seq var_i :=
  [:: buf_17156.(gv)
    ; offset_17157.(gv)
    ; DELTA_17158.(gv)
    ; LEN_17159.(gv)
    ; w_17160.(gv) ].
Definition tyout_A33____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 33; aint; aint ].
Definition res_A33____a_ilen_write_upto32 : seq var_i :=
  [:: buf_17156.(gv); DELTA_17158.(gv); LEN_17159.(gv) ].

(* Body *)
Definition body_A33____a_ilen_write_upto32 : cmd :=
  [:: cif
        (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_17159))
        [:: cif
              (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_17159))
              [:: cassgn (Laset Unaligned AAdirect U256 buf_17156.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17157) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17158))))) (aword U256) (Pvar w_17160)
                ; cassgn (Lvar DELTA_17158.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17158) (Pconst (32)%Z))
                ; cassgn (Lvar LEN_17159.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17159) (Pconst (32)%Z)) ]
              [:: cassgn (Lvar t128_17161.(gv)) (aword U128) (Pvar w_17160)
                ; cif
                    (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_17159))
                    [:: cassgn (Laset Unaligned AAdirect U128 buf_17156.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17157) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17158))))) (aword U128) (Pvar t128_17161)
                      ; cassgn (Lvar DELTA_17158.(gv)) (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17158) (Pconst (16)%Z))
                      ; cassgn (Lvar LEN_17159.(gv)) (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17159) (Pconst (16)%Z))
                      ; copn [:: Lvar t128_17161.(gv) ] (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_17160
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ] ]
                    [::]
                ; ccall [:: Lvar buf_17156.(gv)
                          ; Lvar DELTA_17158.(gv)
                          ; Lvar LEN_17159.(gv) ] A33____a_ilen_write_upto16 [:: Pvar buf_17156
                                                                    ; Pvar offset_17157
                                                                    ; Pvar DELTA_17158
                                                                    ; Pvar LEN_17159
                                                                    ; Pvar t128_17161 ] ] ]
        [::] ].

Definition fd_A33____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____a_ilen_write_upto32;
    f_params := args_A33____a_ilen_write_upto32;
    f_body := body_A33____a_ilen_write_upto32;
    f_tyout := tyout_A33____a_ilen_write_upto32;
    f_res := res_A33____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
