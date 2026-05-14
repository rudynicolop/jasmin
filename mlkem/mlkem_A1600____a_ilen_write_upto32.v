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

(* A1600____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_14999 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1600) (mkident 14999).
Definition offset_15000 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15000).
Definition DELTA_15001 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15001).
Definition LEN_15002 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15002).
Definition w_15003 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15003).
Definition t128_15004 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 15004).

(* Signature *)
Definition tyin_A1600____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 1600; aword U64; aint; aint; aword U256 ].
Definition args_A1600____a_ilen_write_upto32 : seq var_i :=
  [:: buf_14999.(gv)
    ; offset_15000.(gv)
    ; DELTA_15001.(gv)
    ; LEN_15002.(gv)
    ; w_15003.(gv) ].
Definition tyout_A1600____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 1600; aint; aint ].
Definition res_A1600____a_ilen_write_upto32 : seq var_i :=
  [:: buf_14999.(gv); DELTA_15001.(gv); LEN_15002.(gv) ].

(* Body *)
Definition body_A1600____a_ilen_write_upto32 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_15002))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_15002))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 buf_14999.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15000) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15001))))) AT_none (aword U256) (Pvar w_15003))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_15001.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15001) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_15002.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15002) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_15004.(gv)) AT_none (aword U128) (Pvar w_15003))
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_15002))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U128 buf_14999.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15000) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15001))))) AT_none (aword U128) (Pvar t128_15004))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_15001.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15001) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_15002.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15002) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_15004.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_15003
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_14999.(gv)
                                                                  ; Lvar DELTA_15001.(gv)
                                                                  ; Lvar LEN_15002.(gv) ] A1600____a_ilen_write_upto16 [:: Pvar buf_14999
                                                                    ; Pvar offset_15000
                                                                    ; Pvar DELTA_15001
                                                                    ; Pvar LEN_15002
                                                                    ; Pvar t128_15004 ]) ]) ]
                              [::]) ].

Definition fd_A1600____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1600____a_ilen_write_upto32;
    f_params := args_A1600____a_ilen_write_upto32;
    f_body := body_A1600____a_ilen_write_upto32;
    f_tyout := tyout_A1600____a_ilen_write_upto32;
    f_res := res_A1600____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
