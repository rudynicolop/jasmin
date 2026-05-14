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

(* A2____a_ilen_write_upto16 *)
(* Local variables *)
Definition buf_17934 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2) (mkident 17934).
Definition offset_17935 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17935).
Definition DELTA_17936 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17936).
Definition LEN_17937 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17937).
Definition w_17938 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 17938).
Definition t64_17939 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17939).

(* Signature *)
Definition tyin_A2____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 2; aword U64; aint; aint; aword U128 ].
Definition args_A2____a_ilen_write_upto16 : seq var_i :=
  [:: buf_17934.(gv)
    ; offset_17935.(gv)
    ; DELTA_17936.(gv)
    ; LEN_17937.(gv)
    ; w_17938.(gv) ].
Definition tyout_A2____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 2; aint; aint ].
Definition res_A2____a_ilen_write_upto16 : seq var_i :=
  [:: buf_17934.(gv); DELTA_17936.(gv); LEN_17937.(gv) ].

(* Body *)
Definition body_A2____a_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_17937))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_17937))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U128 buf_17934.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17935) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17936))))) AT_none (aword U128) (Pvar w_17938))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_17936.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17936) (Pconst (16)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_17937.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17937) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_17937))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Laset Unaligned AAdirect U64 buf_17934.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_17935) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_17936)))) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_17938 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_17936.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_17936) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_17937.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_17937) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_17938.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_17938
                                                                    ; Pvar w_17938 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64_17939.(gv)) AT_none (aword U64) (Pvar w_17938))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_17934.(gv)
                                                                  ; Lvar DELTA_17936.(gv)
                                                                  ; Lvar LEN_17937.(gv) ] A2____a_ilen_write_upto8 [:: Pvar buf_17934
                                                                    ; Pvar offset_17935
                                                                    ; Pvar DELTA_17936
                                                                    ; Pvar LEN_17937
                                                                    ; Pvar t64_17939 ]) ]) ]
                              [::]) ].

Definition fd_A2____a_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A2____a_ilen_write_upto16;
    f_params := args_A2____a_ilen_write_upto16;
    f_body := body_A2____a_ilen_write_upto16;
    f_tyout := tyout_A2____a_ilen_write_upto16;
    f_res := res_A2____a_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
