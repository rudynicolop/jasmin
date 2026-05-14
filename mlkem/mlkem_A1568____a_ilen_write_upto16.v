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

(* A1568____a_ilen_write_upto16 *)
(* Local variables *)
Definition buf_15777 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15777).
Definition offset_15778 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15778).
Definition DELTA_15779 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15779).
Definition LEN_15780 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15780).
Definition w_15781 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 15781).
Definition t64_15782 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15782).

(* Signature *)
Definition tyin_A1568____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 1568; aword U64; aint; aint; aword U128 ].
Definition args_A1568____a_ilen_write_upto16 : seq var_i :=
  [:: buf_15777.(gv)
    ; offset_15778.(gv)
    ; DELTA_15779.(gv)
    ; LEN_15780.(gv)
    ; w_15781.(gv) ].
Definition tyout_A1568____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 1568; aint; aint ].
Definition res_A1568____a_ilen_write_upto16 : seq var_i :=
  [:: buf_15777.(gv); DELTA_15779.(gv); LEN_15780.(gv) ].

(* Body *)
Definition body_A1568____a_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_15780))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_15780))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U128 buf_15777.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15778) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15779))))) AT_none (aword U128) (Pvar w_15781))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_15779.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15779) (Pconst (16)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_15780.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15780) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_15780))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Laset Unaligned AAdirect U64 buf_15777.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_15778) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_15779)))) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_15781 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_15779.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_15779) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_15780.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_15780) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_15781.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_15781
                                                                    ; Pvar w_15781 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64_15782.(gv)) AT_none (aword U64) (Pvar w_15781))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_15777.(gv)
                                                                  ; Lvar DELTA_15779.(gv)
                                                                  ; Lvar LEN_15780.(gv) ] A1568____a_ilen_write_upto8 [:: Pvar buf_15777
                                                                    ; Pvar offset_15778
                                                                    ; Pvar DELTA_15779
                                                                    ; Pvar LEN_15780
                                                                    ; Pvar t64_15782 ]) ]) ]
                              [::]) ].

Definition fd_A1568____a_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1568____a_ilen_write_upto16;
    f_params := args_A1568____a_ilen_write_upto16;
    f_body := body_A1568____a_ilen_write_upto16;
    f_tyout := tyout_A1568____a_ilen_write_upto16;
    f_res := res_A1568____a_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
