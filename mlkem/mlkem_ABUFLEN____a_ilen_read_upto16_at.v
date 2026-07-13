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

(* ABUFLEN____a_ilen_read_upto16_at *)
(* Local variables *)
Definition buf_153 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14704).
Definition offset_164 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14705).
Definition DELTA_108 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14706).
Definition LEN_77 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14707).
Definition TRAIL_44 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14708).
Definition CUR_44 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14709).
Definition AT_106 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14710).
Definition w_108 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 14711).
Definition AT16_10 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14712).
Definition t64_0_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14713).
Definition t64_1_10 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14714).

(* Signature *)
Definition tyin_ABUFLEN____a_ilen_read_upto16_at : seq atype :=
  [:: aarr U8 536; aword U64; aint; aint; aint; aint; aint ].
Definition args_ABUFLEN____a_ilen_read_upto16_at : seq var_i :=
  [:: buf_153.(gv)
    ; offset_164.(gv)
    ; DELTA_108.(gv)
    ; LEN_77.(gv)
    ; TRAIL_44.(gv)
    ; CUR_44.(gv)
    ; AT_106.(gv) ].
Definition tyout_ABUFLEN____a_ilen_read_upto16_at : seq atype :=
  [:: aint; aint; aint; aint; aword U128 ].
Definition res_ABUFLEN____a_ilen_read_upto16_at : seq var_i :=
  [:: DELTA_108.(gv); LEN_77.(gv); TRAIL_44.(gv); AT_106.(gv); w_108.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_ilen_read_upto16_at : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Oor) (Papp2 (Oor) (Papp2 (Olt (Cmp_int)) (Pvar AT_106) (Pvar CUR_44)) (Papp2 (Ole (Cmp_int)) (Papp2 (Oadd (Op_int)) (Pvar CUR_44) (Pconst (16)%Z)) (Pvar AT_106))) (Papp2 (Oand) (Papp2 (Oeq (Op_int)) (Pvar LEN_77) (Pconst (0)%Z)) (Papp2 (Oeq (Op_int)) (Pvar TRAIL_44) (Pconst (0)%Z))))
                              [:: MkI dummy_instr_info (Copn [:: Lvar w_108.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::]) ]
                              [:: MkI dummy_instr_info (Cassgn (Lvar AT16_10.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar AT_106) (Pvar CUR_44)))
                                ; MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_77))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar w_108.(gv)) AT_none (aword U128) (Pget Unaligned AAdirect U128 buf_153 (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_164) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_108))))))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar w_108.(gv) ] __SHLDQ [:: Pvar w_108
                                                                    ; Pvar AT16_10 ])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_108.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_108) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_10))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_77.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_77) (Papp2 (Osub (Op_int)) (Pconst (16)%Z) (Pvar AT16_10))))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar AT16_10.(gv)) AT_none (aint) (Pconst (16)%Z)) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar AT16_10))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Lvar w_108.(gv) ] AT_none (Oasm ((ExtOp (Oset0 U128)))) [::])
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_108.(gv)
                                                                    ; Lvar LEN_77.(gv)
                                                                    ; Lvar TRAIL_44.(gv)
                                                                    ; Lvar AT16_10.(gv)
                                                                    ; Lvar t64_1_10.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_153
                                                                    ; Pvar offset_164
                                                                    ; Pvar DELTA_108
                                                                    ; Pvar LEN_77
                                                                    ; Pvar TRAIL_44
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_10 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_108.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_108
                                                                    ; Pvar t64_1_10
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [:: MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_108.(gv)
                                                                    ; Lvar LEN_77.(gv)
                                                                    ; Lvar TRAIL_44.(gv)
                                                                    ; Lvar AT16_10.(gv)
                                                                    ; Lvar t64_0_10.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_153
                                                                    ; Pvar offset_164
                                                                    ; Pvar DELTA_108
                                                                    ; Pvar LEN_77
                                                                    ; Pvar TRAIL_44
                                                                    ; Pconst (0)%Z
                                                                    ; Pvar AT16_10 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar w_108.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pvar t64_0_10)))
                                                              ; MkI dummy_instr_info (
                                                            Ccall [:: Lvar DELTA_108.(gv)
                                                                    ; Lvar LEN_77.(gv)
                                                                    ; Lvar TRAIL_44.(gv)
                                                                    ; Lvar AT16_10.(gv)
                                                                    ; Lvar t64_1_10.(gv) ] ABUFLEN____a_ilen_read_upto8_at [:: Pvar buf_153
                                                                    ; Pvar offset_164
                                                                    ; Pvar DELTA_108
                                                                    ; Pvar LEN_77
                                                                    ; Pvar TRAIL_44
                                                                    ; Pconst (8)%Z
                                                                    ; Pvar AT16_10 ])
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_108.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPINSR VE64))))) [:: Pvar w_108
                                                                    ; Pvar t64_1_10
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]) ])
                                ; MkI dummy_instr_info (Cassgn (Lvar AT_106.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar CUR_44) (Pvar AT16_10))) ]) ].

Definition fd_ABUFLEN____a_ilen_read_upto16_at : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____a_ilen_read_upto16_at;
    f_params := args_ABUFLEN____a_ilen_read_upto16_at;
    f_body := body_ABUFLEN____a_ilen_read_upto16_at;
    f_tyout := tyout_ABUFLEN____a_ilen_read_upto16_at;
    f_res := res_ABUFLEN____a_ilen_read_upto16_at;
    f_extra := tt;
  |}.

End IDO.
