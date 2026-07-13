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

(* A128____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_83 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 16614).
Definition offset_79 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16615).
Definition DELTA_53 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16616).
Definition LEN_42 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16617).
Definition TRAIL_24 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16618).
Definition CUR_24 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16619).
Definition AT_56 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16620).
Definition w_58 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 16621).
Definition AT16_5 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16622).
Definition t64_0_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16623).
Definition t64_1_5 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16624).

(* Signature *)
Definition tyin_A128____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 128; aword U64; aint; aint; aint; aint; aint ].
Definition args_A128____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_83.(gv)
    ; offset_79.(gv)
    ; DELTA_53.(gv)
    ; LEN_42.(gv)
    ; TRAIL_24.(gv)
    ; CUR_24.(gv)
    ; AT_56.(gv) ].
Definition tyout_A128____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A128____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_53.(gv); LEN_42.(gv); TRAIL_24.(gv); AT_56.(gv); w_58.(gv) ].

(* Body *)
Definition body_A128____a_ilen_read_upto16_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_56) (Pvar CUR_24)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_24) (Pconst (16)%Z)) (Pvar AT_56))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_42) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_24) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_58.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT16_5.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_56) (Pvar CUR_24)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_42))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_58.(gv)) AT_none (aword U128) (Pget Unaligned AAdirect U128 buf_83 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_79) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_53))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_58.(gv) ] __SHLDQ [:: Pvar w_58
                                                                    ; Pvar AT16_5 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_53.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_53) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_5))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_42.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_42) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_5))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT16_5.(gv)) AT_none (aint) (Pconst (16)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_5))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_58.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_53.(gv)
                                                                    ; Lvar LEN_42.(gv)
                                                                    ; Lvar TRAIL_24.(gv)
                                                                    ; Lvar AT16_5.(gv)
                                                                    ; Lvar t64_1_5.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_83
                                                                    ; Pvar offset_79
                                                                    ; Pvar DELTA_53
                                                                    ; Pvar LEN_42
                                                                    ; Pvar TRAIL_24
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_5 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_58.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_58
                                                                    ; Pvar t64_1_5
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_53.(gv)
                                                                    ; Lvar LEN_42.(gv)
                                                                    ; Lvar TRAIL_24.(gv)
                                                                    ; Lvar AT16_5.(gv)
                                                                    ; Lvar t64_0_5.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_83
                                                                    ; Pvar offset_79
                                                                    ; Pvar DELTA_53
                                                                    ; Pvar LEN_42
                                                                    ; Pvar TRAIL_24
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_5 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_58.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_5)))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_53.(gv)
                                                                    ; Lvar LEN_42.(gv)
                                                                    ; Lvar TRAIL_24.(gv)
                                                                    ; Lvar AT16_5.(gv)
                                                                    ; Lvar t64_1_5.(gv) ] A128____a_ilen_read_upto8_at [:: Pvar buf_83
                                                                    ; Pvar offset_79
                                                                    ; Pvar DELTA_53
                                                                    ; Pvar LEN_42
                                                                    ; Pvar TRAIL_24
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_5 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_58.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_58
                                                                    ; Pvar t64_1_5
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_56.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_24) (Pvar AT16_5))) ]) ].

Definition fd_A128____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____a_ilen_read_upto16_at;
    f_params := args_A128____a_ilen_read_upto16_at;
    f_body := body_A128____a_ilen_read_upto16_at;
    f_tyout := tyout_A128____a_ilen_read_upto16_at;
    f_res := res_A128____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
