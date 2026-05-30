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

(* _gen_matrix_avx2 *)
(* Local variables *)
Definition matrix : gvar :=
  mk_rocq_gvar Slocal (aarr U16 2304) (mkident 13729).
Definition rho_1 : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 13730).
Definition transposed_0 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13731).
Definition buf_s : gvar := mk_rocq_gvar Slocal (aarr U8 2144) (mkident 13732).
Definition buf_178 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2144) (mkident 13733).
Definition i_97 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13734).
Definition pos_entry_0 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13735).
Definition polx4_0 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 1024) (mkident 13736).
Definition pol_6 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13737).
Definition rc_2 : gvar := mk_rocq_gvar Slocal (aword U16) (mkident 13738).
Definition j : gvar := mk_rocq_gvar Slocal (aint) (mkident 13739).

(* Signature *)
Definition tyin__gen_matrix_avx2 : seq atype :=
  [:: aarr U16 2304; aarr U8 32; aword U64 ].
Definition args__gen_matrix_avx2 : seq var_i :=
  [:: matrix.(gv); rho_1.(gv); transposed_0.(gv) ].
Definition tyout__gen_matrix_avx2 : seq atype := [:: aarr U16 2304 ].
Definition res__gen_matrix_avx2 : seq var_i := [:: matrix.(gv) ].

(* Body *)
Definition body__gen_matrix_avx2 : cmd :=
  [:: MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Spill [:: aword U64 ])) [:: Pvar transposed_0 ])
    ; MkI dummy_instr_info (Cassgn (Lvar buf_178.(gv)) AT_none (aarr U8 2144) (Pvar buf_s))
    ; MkI dummy_instr_info (Cfor
                              (i_97.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (2)%Z)
                              [:: MkI dummy_instr_info (Cassgn (Lvar pos_entry_0.(gv)) AT_none (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_97))))
                                ; MkI dummy_instr_info (Cassgn (Lvar polx4_0.(gv)) AT_none (aarr U16 1024) (Psub AAscale U16 1024 matrix (Papp2 (Omul (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_97)) (Pconst (256)%Z))))
                                ; MkI dummy_instr_info (Copn [::] AT_none (Opseudo_op (Ospill Unspill [:: aword U64 ])) [:: Pvar transposed_0 ])
                                ; MkI dummy_instr_info (Ccall [:: Lvar polx4_0.(gv)
                                                                ; Lvar buf_178.(gv) ] _gen_matrix_sample_four_polynomials [:: Pvar polx4_0
                                                                    ; Pvar buf_178
                                                                    ; Pvar rho_1
                                                                    ; Pvar pos_entry_0
                                                                    ; Pvar transposed_0 ])
                                ; MkI dummy_instr_info (Cassgn (Lasub AAscale U16 1024 matrix.(gv) (Papp2 (Omul (Op_int)) (Papp2 (Omul (Op_int)) (Pvar i_97) (Pconst (4)%Z)) (Pconst (256)%Z))) AT_none (aarr U16 1024) (Pvar polx4_0)) ])
    ; MkI dummy_instr_info (Cassgn (Lvar pol_6.(gv)) AT_none (aarr U16 256) (Psub AAscale U16 256 matrix (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pconst (256)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar rc_2.(gv)) AT_none (aword U16) (Papp1 (Oword_of_int U16) (Pconst (514)%Z)))
    ; MkI dummy_instr_info (Ccall [:: Lvar pol_6.(gv)
                                    ; Lasub AAscale U8 536 buf_178.(gv) (Papp2 (Omul (Op_int)) (Pconst (536)%Z) (Pconst (0)%Z)) ] __gen_matrix_sample_one_polynomial [:: Pvar pol_6
                                                                    ; Psub AAscale U8 536 buf_178 (Papp2 (Omul (Op_int)) (Pconst (536)%Z) (Pconst (0)%Z))
                                                                    ; Pvar rho_1
                                                                    ; Pvar rc_2 ])
    ; MkI dummy_instr_info (Cassgn (Lasub AAscale U16 256 matrix.(gv) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pconst (256)%Z))) AT_none (aarr U16 256) (Pvar pol_6))
    ; MkI dummy_instr_info (Cfor
                              (i_97.(gv))
                              (UpTo, Pconst (0)%Z, Pconst (3)%Z)
                              [:: MkI dummy_instr_info (Cfor
                                                          (j.(gv))
                                                          (UpTo, Pconst (0)%Z, Pconst (3)%Z)
                                                          [:: MkI dummy_instr_info (
                                                          Ccall [:: Lasub AAscale U16 256 matrix.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pvar i_97) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (256)%Z))) (Papp2 (Omul (Op_int)) (Pvar j) (Pconst (256)%Z))) ] _nttunpack [:: Psub AAscale U16 256 matrix (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pvar i_97) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (256)%Z))) (Papp2 (Omul (Op_int)) (Pvar j) (Pconst (256)%Z))) ]) ]) ]) ].

Definition fd__gen_matrix_avx2 : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__gen_matrix_avx2;
    f_params := args__gen_matrix_avx2;
    f_body := body__gen_matrix_avx2;
    f_tyout := tyout__gen_matrix_avx2;
    f_res := res__gen_matrix_avx2;
    f_extra := tt;
  |}.

End IDO.
