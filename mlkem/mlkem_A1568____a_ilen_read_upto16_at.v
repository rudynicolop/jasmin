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

(* A1568____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_111 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15850).
Definition offset_113 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15851).
Definition DELTA_75 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15852).
Definition LEN_56 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15853).
Definition TRAIL_32 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15854).
Definition CUR_32 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15855).
Definition AT_76 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15856).
Definition w_78 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 15857).
Definition AT16_7 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15858).
Definition t64_0_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15859).
Definition t64_1_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15860).

(* Signature *)
Definition tyin_A1568____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 1568; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1568____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_111.(gv)
    ; offset_113.(gv)
    ; DELTA_75.(gv)
    ; LEN_56.(gv)
    ; TRAIL_32.(gv)
    ; CUR_32.(gv)
    ; AT_76.(gv) ].
Definition tyout_A1568____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A1568____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_75.(gv); LEN_56.(gv); TRAIL_32.(gv); AT_76.(gv); w_78.(gv) ].

(* Body *)
Definition body_A1568____a_ilen_read_upto16_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_76) (Pvar CUR_32)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_32) (Pconst (16)%Z)) (Pvar AT_76))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_56) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_32) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_78.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT16_7.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_76) (Pvar CUR_32)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_56))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_78.(gv)) AT_none (aword U128) (Pget Unaligned AAdirect U128 buf_111 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_113) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_75))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_78.(gv) ] __SHLDQ [:: Pvar w_78
                                                                    ; Pvar AT16_7 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_75.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_75) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_7))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_56.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_56) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_7))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT16_7.(gv)) AT_none (aint) (Pconst (16)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_7))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_78.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_75.(gv)
                                                                    ; Lvar LEN_56.(gv)
                                                                    ; Lvar TRAIL_32.(gv)
                                                                    ; Lvar AT16_7.(gv)
                                                                    ; Lvar t64_1_7.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_111
                                                                    ; Pvar offset_113
                                                                    ; Pvar DELTA_75
                                                                    ; Pvar LEN_56
                                                                    ; Pvar TRAIL_32
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_7 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_78.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_78
                                                                    ; Pvar t64_1_7
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_75.(gv)
                                                                    ; Lvar LEN_56.(gv)
                                                                    ; Lvar TRAIL_32.(gv)
                                                                    ; Lvar AT16_7.(gv)
                                                                    ; Lvar t64_0_7.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_111
                                                                    ; Pvar offset_113
                                                                    ; Pvar DELTA_75
                                                                    ; Pvar LEN_56
                                                                    ; Pvar TRAIL_32
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_7 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_78.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_7)))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_75.(gv)
                                                                    ; Lvar LEN_56.(gv)
                                                                    ; Lvar TRAIL_32.(gv)
                                                                    ; Lvar AT16_7.(gv)
                                                                    ; Lvar t64_1_7.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_111
                                                                    ; Pvar offset_113
                                                                    ; Pvar DELTA_75
                                                                    ; Pvar LEN_56
                                                                    ; Pvar TRAIL_32
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_7 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_78.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_78
                                                                    ; Pvar t64_1_7
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_76.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_32) (Pvar AT16_7))) ]) ].

Definition fd_A1568____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____a_ilen_read_upto16_at;
    f_params := args_A1568____a_ilen_read_upto16_at;
    f_body := body_A1568____a_ilen_read_upto16_at;
    f_tyout := tyout_A1568____a_ilen_read_upto16_at;
    f_res := res_A1568____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
