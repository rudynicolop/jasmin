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

(* ABUFLEN____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_158 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 536) (mkident 14617).
Definition offset_169 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 14618).
Definition DELTA_113 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14619).
Definition LEN_82 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14620).
Definition w_113 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14621).
Definition t128_24 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 14622).

(* Signature *)
Definition tyin_ABUFLEN____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 536; aword U64; aint; aint; aword U256 ].
Definition args_ABUFLEN____a_ilen_write_upto32 : seq var_i :=
  [:: buf_158.(gv)
    ; offset_169.(gv)
    ; DELTA_113.(gv)
    ; LEN_82.(gv)
    ; w_113.(gv) ].
Definition tyout_ABUFLEN____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 536; aint; aint ].
Definition res_ABUFLEN____a_ilen_write_upto32 : seq var_i :=
  [:: buf_158.(gv); DELTA_113.(gv); LEN_82.(gv) ].

(* Body *)
Definition body_ABUFLEN____a_ilen_write_upto32 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_82))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_82))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 buf_158.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_169) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_113))))) AT_none (aword U256) (Pvar w_113))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_113.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_113) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_82.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_82) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_24.(gv)) AT_none (aword U128) (Pvar w_113))
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_82))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U128 buf_158.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_169) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_113))))) AT_none (aword U128) (Pvar t128_24))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_113.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_113) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_82.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_82) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_24.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_113
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_158.(gv)
                                                                  ; Lvar DELTA_113.(gv)
                                                                  ; Lvar LEN_82.(gv) ] ABUFLEN____a_ilen_write_upto16 [:: Pvar buf_158
                                                                    ; Pvar offset_169
                                                                    ; Pvar DELTA_113
                                                                    ; Pvar LEN_82
                                                                    ; Pvar t128_24 ]) ]) ]
                              [::]) ].

Definition fd_ABUFLEN____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_ABUFLEN____a_ilen_write_upto32;
    f_params := args_ABUFLEN____a_ilen_write_upto32;
    f_body := body_ABUFLEN____a_ilen_write_upto32;
    f_tyout := tyout_ABUFLEN____a_ilen_write_upto32;
    f_res := res_ABUFLEN____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
