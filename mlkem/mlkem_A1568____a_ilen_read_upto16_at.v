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
Definition buf_15850 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15850).
Definition offset_15851 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15851).
Definition DELTA_15852 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15852).
Definition LEN_15853 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15853).
Definition TRAIL_15854 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15854).
Definition CUR_15855 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15855).
Definition AT_15856 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15856).
Definition w_15857 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 15857).
Definition AT16_15858 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15858).
Definition t64_0_15859 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15859).
Definition t64_1_15860 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15860).

(* Signature *)
Definition tyin_A1568____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 1568; aword U64; aint; aint; aint; aint; aint ].
Definition args_A1568____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_15850.(gv)
    ; offset_15851.(gv)
    ; DELTA_15852.(gv)
    ; LEN_15853.(gv)
    ; TRAIL_15854.(gv)
    ; CUR_15855.(gv)
    ; AT_15856.(gv) ].
Definition tyout_A1568____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_A1568____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_15852.(gv)
    ; LEN_15853.(gv)
    ; TRAIL_15854.(gv)
    ; AT_15856.(gv)
    ; w_15857.(gv) ].

(* Body *)
Definition body_A1568____a_ilen_read_upto16_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_15856) (Pvar CUR_15855)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_15855) (Pconst (16)%Z)) (Pvar AT_15856))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_15853) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_15854) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_15857.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT16_15858.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_15856) (Pvar CUR_15855)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_15853))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_15857.(gv)) AT_none (aword U128) (Pget Unaligned AAdirect U128 buf_15850 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15851) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15852))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_15857.(gv) ] __SHLDQ [:: Pvar w_15857
                                                                    ; Pvar AT16_15858 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_15852.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15852) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_15858))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_15853.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15853) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_15858))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT16_15858.(gv)) AT_none (aint) (Pconst (16)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_15858))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_15857.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_15852.(gv)
                                                                    ; Lvar LEN_15853.(gv)
                                                                    ; Lvar TRAIL_15854.(gv)
                                                                    ; Lvar AT16_15858.(gv)
                                                                    ; Lvar t64_1_15860.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_15850
                                                                    ; Pvar offset_15851
                                                                    ; Pvar DELTA_15852
                                                                    ; Pvar LEN_15853
                                                                    ; Pvar TRAIL_15854
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_15858 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_15857.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_15857
                                                                    ; Pvar t64_1_15860
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_15852.(gv)
                                                                    ; Lvar LEN_15853.(gv)
                                                                    ; Lvar TRAIL_15854.(gv)
                                                                    ; Lvar AT16_15858.(gv)
                                                                    ; Lvar t64_0_15859.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_15850
                                                                    ; Pvar offset_15851
                                                                    ; Pvar DELTA_15852
                                                                    ; Pvar LEN_15853
                                                                    ; Pvar TRAIL_15854
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_15858 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_15857.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_15859)))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_15852.(gv)
                                                                    ; Lvar LEN_15853.(gv)
                                                                    ; Lvar TRAIL_15854.(gv)
                                                                    ; Lvar AT16_15858.(gv)
                                                                    ; Lvar t64_1_15860.(gv) ] A1568____a_ilen_read_upto8_at [:: Pvar buf_15850
                                                                    ; Pvar offset_15851
                                                                    ; Pvar DELTA_15852
                                                                    ; Pvar LEN_15853
                                                                    ; Pvar TRAIL_15854
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_15858 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_15857.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_15857
                                                                    ; Pvar t64_1_15860
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_15856.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_15855) (Pvar AT16_15858))) ]) ].

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
