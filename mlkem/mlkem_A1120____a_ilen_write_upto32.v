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

(* A1120____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_130 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 1120) (mkident 15381).
Definition offset_135 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 15382).
Definition DELTA_91 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15383).
Definition LEN_68 : gvar := mk_rocq_gvar Slocal (aint) (mkident 15384).
Definition w_93 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 15385).
Definition t128_20 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 15386).

(* Signature *)
Definition tyin_A1120____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 1120; aword U64; aint; aint; aword U256 ].
Definition args_A1120____a_ilen_write_upto32 : seq var_i :=
  [:: buf_130.(gv); offset_135.(gv); DELTA_91.(gv); LEN_68.(gv); w_93.(gv) ].
Definition tyout_A1120____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 1120; aint; aint ].
Definition res_A1120____a_ilen_write_upto32 : seq var_i :=
  [:: buf_130.(gv); DELTA_91.(gv); LEN_68.(gv) ].

(* Body *)
Definition body_A1120____a_ilen_write_upto32 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_68))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_68))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 buf_130.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_135) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_91))))) AT_none (aword U256) (Pvar w_93))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_91.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_91) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_68.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_68) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_20.(gv)) AT_none (aword U128) (Pvar w_93))
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_68))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U128 buf_130.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_135) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_91))))) AT_none (aword U128) (Pvar t128_20))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_91.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_91) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_68.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_68) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_20.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_93
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_130.(gv)
                                                                  ; Lvar DELTA_91.(gv)
                                                                  ; Lvar LEN_68.(gv) ] A1120____a_ilen_write_upto16 [:: Pvar buf_130
                                                                    ; Pvar offset_135
                                                                    ; Pvar DELTA_91
                                                                    ; Pvar LEN_68
                                                                    ; Pvar t128_20 ]) ]) ]
                              [::]) ].

Definition fd_A1120____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A1120____a_ilen_write_upto32;
    f_params := args_A1120____a_ilen_write_upto32;
    f_body := body_A1120____a_ilen_write_upto32;
    f_tyout := tyout_A1120____a_ilen_write_upto32;
    f_res := res_A1120____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
