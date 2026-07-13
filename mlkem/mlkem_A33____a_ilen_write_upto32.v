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

(* A33____a_ilen_write_upto32 *)
(* Local variables *)
Definition buf_62 : gvar := mk_rocq_gvar Slocal (aarr U8 33) (mkident 17156).
Definition offset_56 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 17157).
Definition DELTA_38 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17158).
Definition LEN_33 : gvar := mk_rocq_gvar Slocal (aint) (mkident 17159).
Definition w_44 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 17160).
Definition t128_10 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 17161).

(* Signature *)
Definition tyin_A33____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 33; aword U64; aint; aint; aword U256 ].
Definition args_A33____a_ilen_write_upto32 : seq var_i :=
  [:: buf_62.(gv); offset_56.(gv); DELTA_38.(gv); LEN_33.(gv); w_44.(gv) ].
Definition tyout_A33____a_ilen_write_upto32 : seq atype :=
  [:: aarr U8 33; aint; aint ].
Definition res_A33____a_ilen_write_upto32 : seq var_i :=
  [:: buf_62.(gv); DELTA_38.(gv); LEN_33.(gv) ].

(* Body *)
Definition body_A33____a_ilen_write_upto32 : cmd :=
  [:: MkI dummy_instr_info (Cif
                              (Papp2 (Olt (Cmp_int)) (Pconst (0)%Z) (Pvar LEN_33))
                              [:: MkI dummy_instr_info (Cif
                                                          (Papp2 (Ole (Cmp_int)) (Pconst (32)%Z) (Pvar LEN_33))
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Laset Unaligned AAdirect U256 buf_62.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_56) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_38))))) AT_none (aword U256) (Pvar w_44))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar DELTA_38.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_38) (Pconst (32)%Z)))
                                                            ; MkI dummy_instr_info (
                                                          Cassgn (Lvar LEN_33.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_33) (Pconst (32)%Z))) ]
                                                          [:: MkI dummy_instr_info (
                                                          Cassgn (Lvar t128_10.(gv)) AT_none (aword U128) (Pvar w_44))
                                                            ; MkI dummy_instr_info (
                                                          Cif
                                                            (Papp2 (Ole (Cmp_int)) (Pconst (16)%Z) (Pvar LEN_33))
                                                            [:: MkI dummy_instr_info (
                                                            Cassgn (Laset Unaligned AAdirect U128 buf_62.(gv) (Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Papp2 (Owi2 Unsigned U64 WIadd) (Pvar offset_56) (Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pvar DELTA_38))))) AT_none (aword U128) (Pvar t128_10))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar DELTA_38.(gv)) AT_none (aint) (Papp2 (Oadd (Op_int)) (Pvar DELTA_38) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Cassgn (Lvar LEN_33.(gv)) AT_none (aint) (Papp2 (Osub (Op_int)) (Pvar LEN_33) (Pconst (16)%Z)))
                                                              ; MkI dummy_instr_info (
                                                            Copn [:: Lvar t128_10.(gv) ] AT_none (Oasm ((BaseOp ((None), VEXTRACTI128)))) [:: Pvar w_44
                                                                    ; Papp1 (Oword_of_int U8) (Pconst (1)%Z) ]) ]
                                                            [::])
                                                            ; MkI dummy_instr_info (
                                                          Ccall [:: Lvar buf_62.(gv)
                                                                  ; Lvar DELTA_38.(gv)
                                                                  ; Lvar LEN_33.(gv) ] A33____a_ilen_write_upto16 [:: Pvar buf_62
                                                                    ; Pvar offset_56
                                                                    ; Pvar DELTA_38
                                                                    ; Pvar LEN_33
                                                                    ; Pvar t128_10 ]) ]) ]
                              [::]) ].

Definition fd_A33____a_ilen_write_upto32 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin_A33____a_ilen_write_upto32;
    f_params := args_A33____a_ilen_write_upto32;
    f_body := body_A33____a_ilen_write_upto32;
    f_tyout := tyout_A33____a_ilen_write_upto32;
    f_res := res_A33____a_ilen_write_upto32;
    f_extra := tt;
  |}.

End IDO.
