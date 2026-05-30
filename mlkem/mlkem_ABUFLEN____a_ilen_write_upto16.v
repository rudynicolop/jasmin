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

(* ABUFLEN____a_ilen_write_upto16 *)
(* Local variables *)
Definition buf_157 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14631).
Definition offset_168 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14632).
Definition DELTA_112 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14633).
Definition LEN_81 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14634).
Definition w_112 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 14635).
Definition t64_12 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 14636).

(* Signature *)
Definition tyin_ABUFLEN____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 536; aword U64; aint; aint; aword U128 ].
Definition args_ABUFLEN____a_ilen_write_upto16 : seq var_i :=
  [:: buf_157.(gv)
    ; offset_168.(gv)
    ; DELTA_112.(gv)
    ; LEN_81.(gv)
    ; w_112.(gv) ].
Definition tyout_ABUFLEN____a_ilen_write_upto16 : seq atype :=
  [:: aarr U8 536; aint; aint ].
Definition res_ABUFLEN____a_ilen_write_upto16 : seq var_i :=
  [:: buf_157.(gv); DELTA_112.(gv); LEN_81.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_ilen_write_upto16 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_81))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_81))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U128 buf_157.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_168) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_112))))) AT_none (aword U128) (Pvar w_112))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_112.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_112) (Pconst (16)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_81.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_81) (Pconst (16)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (8)%Z) (Pvar LEN_81))
                                                            [:: MkI dummy_instr_info (
                                                            Copn [:: Laset Unaligned AAdirect U64 buf_157.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_168) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_112)))) ] AT_none (Oasm ((BaseOp ((None), (MOVV U64))))) [:: Pvar w_112 ])
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_112.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_112) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_81.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_81) (Pconst (8)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar w_112.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPUNPCKH VE64 U128))))) [:: Pvar w_112
                                                                    ; Pvar w_112 ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar t64_12.(gv)) AT_none (aword U64) (Pvar w_112))
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_157.(gv)
                                                                  ; Lvar DELTA_112.(gv)
                                                                  ; Lvar LEN_81.(gv) ] ABUFLEN____a_ilen_write_upto8 [:: Pvar buf_157
                                                                    ; Pvar offset_168
                                                                    ; Pvar DELTA_112
                                                                    ; Pvar LEN_81
                                                                    ; Pvar t64_12 ]) ]) ]
                              [::]) ].

Definition fd_ABUFLEN____a_ilen_write_upto16 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____a_ilen_write_upto16;
    f_params := args_ABUFLEN____a_ilen_write_upto16;
    f_body := body_ABUFLEN____a_ilen_write_upto16;
    f_tyout := tyout_ABUFLEN____a_ilen_write_upto16;
    f_res := res_ABUFLEN____a_ilen_write_upto16;
    f_extra := tt;
  |}.

End IDO.
