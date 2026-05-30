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

(* A64____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_71 : gvar := mk_rocq_gvar Slocal (aarr U8 64) (mkident 16861).
Definition offset_68 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16862).
Definition DELTA_44 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16863).
Definition LEN_35 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16864).
Definition TRAIL_20 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16865).
Definition CUR_20 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16866).
Definition AT_50 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16867).
Definition w_49 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 16868).
Definition AT16_4 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16869).
Definition t64_0_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16870).
Definition t64_1_4 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16871).

(* Signature *)
Definition tyin_A64____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 64; aword U64; aint; aint; aint; aint; aint ].
Definition args_A64____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_71.(gv)
    ; offset_68.(gv)
    ; DELTA_44.(gv)
    ; LEN_35.(gv)
    ; TRAIL_20.(gv)
    ; CUR_20.(gv)
    ; AT_50.(gv) ].
Definition tyout_A64____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A64____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_44.(gv); LEN_35.(gv); TRAIL_20.(gv); AT_50.(gv); w_49.(gv) ].

(* Body *)
Definition body_A64____a_ilen_read_upto16_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_50) (Pvar CUR_20)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_20) (Pconst (16)%Z)) (Pvar AT_50))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_35) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_20) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_49.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT16_4.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_50) (Pvar CUR_20)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_35))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_49.(gv)) AT_none (aword U128) (Pget Unaligned AAdirect U128 buf_71 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_68) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_44))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_49.(gv) ] __SHLDQ [:: Pvar w_49
                                                                    ; Pvar AT16_4 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_44.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_44) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_4))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_35.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_35) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_4))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT16_4.(gv)) AT_none (aint) (Pconst (16)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_4))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_49.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_44.(gv)
                                                                    ; Lvar LEN_35.(gv)
                                                                    ; Lvar TRAIL_20.(gv)
                                                                    ; Lvar AT16_4.(gv)
                                                                    ; Lvar t64_1_4.(gv) ] A64____a_ilen_read_upto8_at [:: Pvar buf_71
                                                                    ; Pvar offset_68
                                                                    ; Pvar DELTA_44
                                                                    ; Pvar LEN_35
                                                                    ; Pvar TRAIL_20
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_4 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_49.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_49
                                                                    ; Pvar t64_1_4
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_44.(gv)
                                                                    ; Lvar LEN_35.(gv)
                                                                    ; Lvar TRAIL_20.(gv)
                                                                    ; Lvar AT16_4.(gv)
                                                                    ; Lvar t64_0_4.(gv) ] A64____a_ilen_read_upto8_at [:: Pvar buf_71
                                                                    ; Pvar offset_68
                                                                    ; Pvar DELTA_44
                                                                    ; Pvar LEN_35
                                                                    ; Pvar TRAIL_20
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_4 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_49.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_4)))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_44.(gv)
                                                                    ; Lvar LEN_35.(gv)
                                                                    ; Lvar TRAIL_20.(gv)
                                                                    ; Lvar AT16_4.(gv)
                                                                    ; Lvar t64_1_4.(gv) ] A64____a_ilen_read_upto8_at [:: Pvar buf_71
                                                                    ; Pvar offset_68
                                                                    ; Pvar DELTA_44
                                                                    ; Pvar LEN_35
                                                                    ; Pvar TRAIL_20
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_4 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_49.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_49
                                                                    ; Pvar t64_1_4
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_50.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_20) (Pvar AT16_4))) ]) ].

Definition fd_A64____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A64____a_ilen_read_upto16_at;
    f_params := args_A64____a_ilen_read_upto16_at;
    f_body := body_A64____a_ilen_read_upto16_at;
    f_tyout := tyout_A64____a_ilen_read_upto16_at;
    f_res := res_A64____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
