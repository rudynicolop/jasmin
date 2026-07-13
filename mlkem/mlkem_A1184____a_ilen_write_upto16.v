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

(* A1184____a_ilen_write_upto16 *)
(* Local variables *)
Definition buf_101 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16159).
Definition offset_100 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16160).
Definition DELTA_68 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16161).
Definition LEN_53 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16162).
Definition w_72 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 16163).
Definition t64_8 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16164).

(* Signature *)
Definition tyin_A1184____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 1184; aword U64; aint; aint; aword U128 ].
Definition args_A1184____a_ilen_write_upto16 : seq var_i :=
  [:: buf_101.(gv); offset_100.(gv); DELTA_68.(gv); LEN_53.(gv); w_72.(gv) ].
Definition tyout_A1184____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 1184; aint; aint ].
Definition res_A1184____a_ilen_write_upto16 : seq var_i :=
  [:: buf_101.(gv); DELTA_68.(gv); LEN_53.(gv) ].

(* Body *)
Definition body_A1184____a_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_53))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_53))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U128 buf_101.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_100) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_68))))) AT_none (aword U128) (Pvar w_72))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_68.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_68) (Pconst (16)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_53.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_53) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_53))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Laset Unaligned AAdirect U64 buf_101.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_100) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_68)))) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_72 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_68.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_68) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_53.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_53) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_72.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_72
                                                                    ; Pvar w_72 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64_8.(gv)) AT_none (aword U64) (Pvar w_72))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_101.(gv)
                                                                  ; Lvar DELTA_68.(gv)
                                                                  ; Lvar LEN_53.(gv) ] A1184____a_ilen_write_upto8 [:: Pvar buf_101
                                                                    ; Pvar offset_100
                                                                    ; Pvar DELTA_68
                                                                    ; Pvar LEN_53
                                                                    ; Pvar t64_8 ]) ]) ]
                              [::]) ].

Definition fd_A1184____a_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____a_ilen_write_upto16;
    f_params := args_A1184____a_ilen_write_upto16;
    f_body := body_A1184____a_ilen_write_upto16;
    f_tyout := tyout_A1184____a_ilen_write_upto16;
    f_res := res_A1184____a_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
