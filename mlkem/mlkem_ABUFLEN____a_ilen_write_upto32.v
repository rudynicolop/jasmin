From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi data notations.

Require Import x86_decl x86_instr_decl x86_extra.
Existing Instance x86_atoI.

Require Import mlkem_globs.
Require Import mlkem_funnames.

Section IDO.
Context {IdO : IdentOracles}.

(* ABUFLEN____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_14617 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14617).
Definition offset_14618 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14618).
Definition DELTA_14619 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14619).
Definition LEN_14620 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14620).
Definition w_14621 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14621).
Definition t128_14622 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 14622).

(* Signature *)
Definition tyin_ABUFLEN____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 536; aword U64; aint; aint; aword U256 ].
Definition args_ABUFLEN____a_ilen_write_upto32 : seq var_i :=
  [:: buf_14617.(gv)
    ; offset_14618.(gv)
    ; DELTA_14619.(gv)
    ; LEN_14620.(gv)
    ; w_14621.(gv) ].
Definition tyout_ABUFLEN____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 536; aint; aint ].
Definition res_ABUFLEN____a_ilen_write_upto32 : seq var_i :=
  [:: buf_14617.(gv); DELTA_14619.(gv); LEN_14620.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_ilen_write_upto32 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_14620))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_14620))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 buf_14617.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14618) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14619))))) AT_none (aword U256) (Pvar w_14621))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_14619.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_14619) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_14620.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14620) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_14622.(gv)) AT_none (aword U128) (Pvar w_14621))
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_14620))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U128 buf_14617.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_14618) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_14619))))) AT_none (aword U128) (Pvar t128_14622))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_14619.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_14619) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_14620.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_14620) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_14622.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_14621
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_14617.(gv)
                                                                  ; Lvar DELTA_14619.(gv)
                                                                  ; Lvar LEN_14620.(gv) ] ABUFLEN____a_ilen_write_upto16 [:: Pvar buf_14617
                                                                    ; Pvar offset_14618
                                                                    ; Pvar DELTA_14619
                                                                    ; Pvar LEN_14620
                                                                    ; Pvar t128_14622 ]) ]) ]
                              [::]) ].

Definition fd_ABUFLEN____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____a_ilen_write_upto32;
    f_params := args_ABUFLEN____a_ilen_write_upto32;
    f_body := body_ABUFLEN____a_ilen_write_upto32;
    f_tyout := tyout_ABUFLEN____a_ilen_write_upto32;
    f_res := res_ABUFLEN____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
