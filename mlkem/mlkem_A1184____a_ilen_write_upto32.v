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

(* A1184____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_102 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1184) (mkident 16145).
Definition offset_101 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 16146).
Definition DELTA_69 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16147).
Definition LEN_54 : gvar := mk_rocq_gvar Slocal (aint) (mkident 16148).
Definition w_73 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 16149).
Definition t128_16 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 16150).

(* Signature *)
Definition tyin_A1184____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 1184; aword U64; aint; aint; aword U256 ].
Definition args_A1184____a_ilen_write_upto32 : seq var_i :=
  [:: buf_102.(gv); offset_101.(gv); DELTA_69.(gv); LEN_54.(gv); w_73.(gv) ].
Definition tyout_A1184____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 1184; aint; aint ].
Definition res_A1184____a_ilen_write_upto32 : seq var_i :=
  [:: buf_102.(gv); DELTA_69.(gv); LEN_54.(gv) ].

(* Body *)
Definition body_A1184____a_ilen_write_upto32 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_54))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_54))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 buf_102.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_101) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_69))))) AT_none (aword U256) (Pvar w_73))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_69.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_69) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_54.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_54) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_16.(gv)) AT_none (aword U128) (Pvar w_73))
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_54))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U128 buf_102.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_101) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_69))))) AT_none (aword U128) (Pvar t128_16))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_69.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_69) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_54.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_54) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_16.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_73
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_102.(gv)
                                                                  ; Lvar DELTA_69.(gv)
                                                                  ; Lvar LEN_54.(gv) ] A1184____a_ilen_write_upto16 [:: Pvar buf_102
                                                                    ; Pvar offset_101
                                                                    ; Pvar DELTA_69
                                                                    ; Pvar LEN_54
                                                                    ; Pvar t128_16 ]) ]) ]
                              [::]) ].

Definition fd_A1184____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1184____a_ilen_write_upto32;
    f_params := args_A1184____a_ilen_write_upto32;
    f_body := body_A1184____a_ilen_write_upto32;
    f_tyout := tyout_A1184____a_ilen_write_upto32;
    f_res := res_A1184____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
