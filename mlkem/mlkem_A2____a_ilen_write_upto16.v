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
Definition buf_33 : gvar := mk_rocq_gvar Slocal (aarr U8 2) (mkident 17934).
Definition offset_21 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17935).
Definition DELTA_15 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17936).
Definition LEN_18 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17937).
Definition w_23 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 17938).
Definition t64_3 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 17939).

(* Signature *)
Definition tyin_A2____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 2; aword U64; aint; aint; aword U128 ].
Definition args_A2____a_ilen_write_upto16 : seq var_i :=
  [:: buf_33.(gv); offset_21.(gv); DELTA_15.(gv); LEN_18.(gv); w_23.(gv) ].
Definition tyout_A2____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 2; aint; aint ].
Definition res_A2____a_ilen_write_upto16 : seq var_i :=
  [:: buf_33.(gv); DELTA_15.(gv); LEN_18.(gv) ].

(* Body *)
Definition body_A2____a_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_18))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_18))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U128 buf_33.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_21) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15))))) AT_none (aword U128) (Pvar w_23))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_15.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15) (Pconst (16)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_18.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_18))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Laset Unaligned AAdirect U64 buf_33.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_21) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15)))) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_23 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_15.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_18.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_18) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_23.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_23
                                                                    ; Pvar w_23 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64_3.(gv)) AT_none (aword U64) (Pvar w_23))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_33.(gv)
                                                                  ; Lvar DELTA_15.(gv)
                                                                  ; Lvar LEN_18.(gv) ] A2____a_ilen_write_upto8 [:: Pvar buf_33
                                                                    ; Pvar offset_21
                                                                    ; Pvar DELTA_15
                                                                    ; Pvar LEN_18
                                                                    ; Pvar t64_3 ]) ]) ]
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
