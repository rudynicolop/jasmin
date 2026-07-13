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
Definition buf_115 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1568) (mkident 15777).
Definition offset_117 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15778).
Definition DELTA_79 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15779).
Definition LEN_60 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15780).
Definition w_82 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 15781).
Definition t64_9 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 15782).

(* Signature *)
Definition tyin_A1568____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 1568; aword U64; aint; aint; aword U128 ].
Definition args_A1568____a_ilen_write_upto16 : seq var_i :=
  [:: buf_115.(gv); offset_117.(gv); DELTA_79.(gv); LEN_60.(gv); w_82.(gv) ].
Definition tyout_A1568____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 1568; aint; aint ].
Definition res_A1568____a_ilen_write_upto16 : seq var_i :=
  [:: buf_115.(gv); DELTA_79.(gv); LEN_60.(gv) ].

(* Body *)
Definition body_A1568____a_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_60))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_60))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U128 buf_115.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_117) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_79))))) AT_none (aword U128) (Pvar w_82))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_79.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_79) (Pconst (16)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_60.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_60) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_60))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Laset Unaligned AAdirect U64 buf_115.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_117) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_79)))) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_82 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_79.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_79) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_60.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_60) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_82.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_82
                                                                    ; Pvar w_82 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64_9.(gv)) AT_none (aword U64) (Pvar w_82))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_115.(gv)
                                                                  ; Lvar DELTA_79.(gv)
                                                                  ; Lvar LEN_60.(gv) ] A1568____a_ilen_write_upto8 [:: Pvar buf_115
                                                                    ; Pvar offset_117
                                                                    ; Pvar DELTA_79
                                                                    ; Pvar LEN_60
                                                                    ; Pvar t64_9 ]) ]) ]
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
