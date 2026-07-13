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

(* _gen_matrix_sample_four_polynomials *)
(* Local variables *)
Definition polx4 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 1024) (mkident 13756).
Definition buf_176 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2144) (mkident 13757).
Definition rho : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 13758).
Definition pos_entry : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13759).
Definition transposed : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13760).
Definition indexes : gvar := mk_rocq_gvar Slocal (aarr U8 8) (mkident 13761).
Definition state_5 : gvar :=
  mk_rocq_gvar Slocal (aarr U256 25) (mkident 13762).
Definition stx4 : gvar := mk_rocq_gvar Slocal (aarr U256 25) (mkident 13763).
Definition pol_4 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13764).

(* Signature *)
Definition tyin__gen_matrix_sample_four_polynomials : seq atype :=
  [:: aarr U16 1024; aarr U8 2144; aarr U8 32; aword U64; aword U64 ].
Definition args__gen_matrix_sample_four_polynomials : seq var_i :=
  [:: polx4.(gv); buf_176.(gv); rho.(gv); pos_entry.(gv); transposed.(gv) ].
Definition tyout__gen_matrix_sample_four_polynomials : seq atype :=
  [:: aarr U16 1024; aarr U8 2144 ].
Definition res__gen_matrix_sample_four_polynomials : seq var_i :=
  [:: polx4.(gv); buf_176.(gv) ].

(* Body *)
Definition body__gen_matrix_sample_four_polynomials : cmd :=
  [:: MkI dummy_instr_info (Ccall [:: Laset Unaligned AAdirect U64 indexes.(gv) (Pconst (0)%Z) ] gen_matrix_get_indexes [:: Pvar pos_entry
                                                                    ; Pvar transposed ])
    ; MkI dummy_instr_info (Cassgn (Lvar stx4.(gv)) AT_none (aarr U256 25) (Pvar state_5))
    ; MkI dummy_instr_info (Ccall [:: Lvar stx4.(gv) ] _shake128x4_absorb_A32_A2 [:: Pvar stx4
                                                                    ; Pvar rho
                                                                    ; Pvar indexes ])
    ; MkI dummy_instr_info (Ccall [:: Lnone dummy_var_info (aarr U256 25)
                                    ; Lvar buf_176.(gv) ] _shake128x4_squeeze3blocks [:: Pvar stx4
                                                                    ; Pvar buf_176 ])
    ; MkI dummy_instr_info (Cassgn (Lvar pol_4.(gv)) AT_none (aarr U16 256) (Psub AAscale U16 256 polx4 (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (256)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar pol_4.(gv)
                                    ; Lasub AAscale U8 536 buf_176.(gv) (Papp2 (Omul (Op_int)) (Pconst (536)%Z) (Pconst (0)%Z)) ] __gen_matrix_fill_polynomial [:: Pvar pol_4
                                                                    ; Psub AAscale U8 536 buf_176 (Papp2 (Omul (Op_int)) (Pconst (536)%Z) (Pconst (0)%Z)) ])
    ; MkI dummy_instr_info (Cassgn (Lasub AAscale U16 256 polx4.(gv) (Papp2 (Omul (Op_int)) (Pconst (0)%Z) (Pconst (256)%Z))) AT_none (aarr U16 256) (Pvar pol_4))
    ; MkI dummy_instr_info (Cassgn (Lvar pol_4.(gv)) AT_none (aarr U16 256) (Psub AAscale U16 256 polx4 (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (256)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar pol_4.(gv)
                                    ; Lasub AAscale U8 536 buf_176.(gv) (Papp2 (Omul (Op_int)) (Pconst (536)%Z) (Pconst (1)%Z)) ] __gen_matrix_fill_polynomial [:: Pvar pol_4
                                                                    ; Psub AAscale U8 536 buf_176 (Papp2 (Omul (Op_int)) (Pconst (536)%Z) (Pconst (1)%Z)) ])
    ; MkI dummy_instr_info (Cassgn (Lasub AAscale U16 256 polx4.(gv) (Papp2 (Omul (Op_int)) (Pconst (1)%Z) (Pconst (256)%Z))) AT_none (aarr U16 256) (Pvar pol_4))
    ; MkI dummy_instr_info (Cassgn (Lvar pol_4.(gv)) AT_none (aarr U16 256) (Psub AAscale U16 256 polx4 (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (256)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar pol_4.(gv)
                                    ; Lasub AAscale U8 536 buf_176.(gv) (Papp2 (Omul (Op_int)) (Pconst (536)%Z) (Pconst (2)%Z)) ] __gen_matrix_fill_polynomial [:: Pvar pol_4
                                                                    ; Psub AAscale U8 536 buf_176 (Papp2 (Omul (Op_int)) (Pconst (536)%Z) (Pconst (2)%Z)) ])
    ; MkI dummy_instr_info (Cassgn (Lasub AAscale U16 256 polx4.(gv) (Papp2 (Omul (Op_int)) (Pconst (2)%Z) (Pconst (256)%Z))) AT_none (aarr U16 256) (Pvar pol_4))
    ; MkI dummy_instr_info (Cassgn (Lvar pol_4.(gv)) AT_none (aarr U16 256) (Psub AAscale U16 256 polx4 (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (256)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar pol_4.(gv)
                                    ; Lasub AAscale U8 536 buf_176.(gv) (Papp2 (Omul (Op_int)) (Pconst (536)%Z) (Pconst (3)%Z)) ] __gen_matrix_fill_polynomial [:: Pvar pol_4
                                                                    ; Psub AAscale U8 536 buf_176 (Papp2 (Omul (Op_int)) (Pconst (536)%Z) (Pconst (3)%Z)) ])
    ; MkI dummy_instr_info (Cassgn (Lasub AAscale U16 256 polx4.(gv) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (256)%Z))) AT_none (aarr U16 256) (Pvar pol_4)) ].

Definition fd__gen_matrix_sample_four_polynomials : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__gen_matrix_sample_four_polynomials;
    f_params := args__gen_matrix_sample_four_polynomials;
    f_body := body__gen_matrix_sample_four_polynomials;
    f_tyout := tyout__gen_matrix_sample_four_polynomials;
    f_res := res__gen_matrix_sample_four_polynomials;
    f_extra := tt;
  |}.

End IDO.
