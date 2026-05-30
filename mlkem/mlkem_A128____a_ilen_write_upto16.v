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

(* A128____a_ilen_write_upto16 *)
(* Local variables *)
Definition buf_87 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 16541).
Definition offset_83 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16542).
Definition DELTA_57 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16543).
Definition LEN_46 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16544).
Definition w_62 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 16545).
Definition t64_7 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 16546).

(* Signature *)
Definition tyin_A128____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 128; aword U64; aint; aint; aword U128 ].
Definition args_A128____a_ilen_write_upto16 : seq var_i :=
  [:: buf_87.(gv); offset_83.(gv); DELTA_57.(gv); LEN_46.(gv); w_62.(gv) ].
Definition tyout_A128____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 128; aint; aint ].
Definition res_A128____a_ilen_write_upto16 : seq var_i :=
  [:: buf_87.(gv); DELTA_57.(gv); LEN_46.(gv) ].

(* Body *)
Definition body_A128____a_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_46))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_46))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U128 buf_87.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_83) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_57))))) AT_none (aword U128) (Pvar w_62))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_57.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_57) (Pconst (16)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_46.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_46) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_46))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Laset Unaligned AAdirect U64 buf_87.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_83) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_57)))) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_62 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_57.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_57) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_46.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_46) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_62.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_62
                                                                    ; Pvar w_62 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64_7.(gv)) AT_none (aword U64) (Pvar w_62))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_87.(gv)
                                                                  ; Lvar DELTA_57.(gv)
                                                                  ; Lvar LEN_46.(gv) ] A128____a_ilen_write_upto8 [:: Pvar buf_87
                                                                    ; Pvar offset_83
                                                                    ; Pvar DELTA_57
                                                                    ; Pvar LEN_46
                                                                    ; Pvar t64_7 ]) ]) ]
                              [::]) ].

Definition fd_A128____a_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A128____a_ilen_write_upto16;
    f_params := args_A128____a_ilen_write_upto16;
    f_body := body_A128____a_ilen_write_upto16;
    f_tyout := tyout_A128____a_ilen_write_upto16;
    f_res := res_A128____a_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
