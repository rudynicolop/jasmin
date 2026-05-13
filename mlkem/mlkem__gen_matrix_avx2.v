From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr ident var type global pseudo_operator sopn arch_extra.
From Printing Require Import atoi syntax data notations.

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
Definition rho_13730 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 32) (mkident 13730).
Definition transposed_13731 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13731).
Definition buf_s : gvar := mk_rocq_gvar Slocal (aarr U8 2144) (mkident 13732).
Definition buf_13733 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 2144) (mkident 13733).
Definition i_13734 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13734).
Definition pos_entry_13735 : gvar :=
  mk_rocq_gvar Slocal (aword U64) (mkident 13735).
Definition polx4_13736 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 1024) (mkident 13736).
Definition pol_13737 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 13737).
Definition rc_13738 : gvar := mk_rocq_gvar Slocal (aword U16) (mkident 13738).
Definition j : gvar := mk_rocq_gvar Slocal (aint) (mkident 13739).

(* Signature *)
Definition tyin__gen_matrix_avx2 : seq atype :=
  [:: aarr U16 2304; aarr U8 32; aword U64 ].
Definition args__gen_matrix_avx2 : seq var_i :=
  [:: matrix.(gv); rho_13730.(gv); transposed_13731.(gv) ].
Definition tyout__gen_matrix_avx2 : seq atype := [:: aarr U16 2304 ].
Definition res__gen_matrix_avx2 : seq var_i := [:: matrix.(gv) ].

(* Body *)
Definition body__gen_matrix_avx2 : cmd :=
  [:: copn [::] (Opseudo_op (Ospill Spill [:: aword U64 ])) [:: Pvar transposed_13731 ]
    ; cassgn (Lvar buf_13733.(gv)) (aarr U8 2144) (Pvar buf_s)
    ; cfor
        (i_13734.(gv))
        (UpTo, Pconst (0)%Z, Pconst (2)%Z)
        [:: cassgn (Lvar pos_entry_13735.(gv)) (aword U64) (Papp1 (Oword_of_int U64) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_13734)))
          ; cassgn (Lvar polx4_13736.(gv)) (aarr U16 1024) (Psub AAscale U16 1024 matrix (Papp2 (Omul (Op_int)) (Papp2 (Omul (Op_int)) (Pconst (4)%Z) (Pvar i_13734)) (Pconst (256)%Z)))
          ; copn [::] (Opseudo_op (Ospill Unspill [:: aword U64 ])) [:: Pvar transposed_13731 ]
          ; ccall [:: Lvar polx4_13736.(gv); Lvar buf_13733.(gv) ] _gen_matrix_sample_four_polynomials [:: Pvar polx4_13736
                                                                    ; Pvar buf_13733
                                                                    ; Pvar rho_13730
                                                                    ; Pvar pos_entry_13735
                                                                    ; Pvar transposed_13731 ]
          ; cassgn (Lasub AAscale U16 1024 matrix.(gv) (Papp2 (Omul (Op_int)) (Papp2 (Omul (Op_int)) (Pvar i_13734) (Pconst (4)%Z)) (Pconst (256)%Z))) (aarr U16 1024) (Pvar polx4_13736) ]
    ; cassgn (Lvar pol_13737.(gv)) (aarr U16 256) (Psub AAscale U16 256 matrix (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pconst (256)%Z)))
    ; cassgn (Lvar rc_13738.(gv)) (aword U16) (Papp1 (Oword_of_int U16) (Pconst (514)%Z))
    ; ccall [:: Lvar pol_13737.(gv)
              ; Lasub AAscale U8 536 buf_13733.(gv) (Papp2 (Omul (Op_int)) (Pconst (536)%Z) (Pconst (0)%Z)) ] __gen_matrix_sample_one_polynomial [:: Pvar pol_13737
                                                                    ; Psub AAscale U8 536 buf_13733 (Papp2 (Omul (Op_int)) (Pconst (536)%Z) (Pconst (0)%Z))
                                                                    ; Pvar rho_13730
                                                                    ; Pvar rc_13738 ]
    ; cassgn (Lasub AAscale U16 256 matrix.(gv) (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pconst (256)%Z))) (aarr U16 256) (Pvar pol_13737)
    ; cfor
        (i_13734.(gv))
        (UpTo, Pconst (0)%Z, Pconst (3)%Z)
        [:: cfor
              (j.(gv))
              (UpTo, Pconst (0)%Z, Pconst (3)%Z)
              [:: ccall [:: Lasub AAscale U16 256 matrix.(gv) (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pvar i_13734) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (256)%Z))) (Papp2 (Omul (Op_int)) (Pvar j) (Pconst (256)%Z))) ] _nttunpack [:: Psub AAscale U16 256 matrix (Papp2 (Oadd (Op_int)) (Papp2 (Omul (Op_int)) (Pvar i_13734) (Papp2 (Omul (Op_int)) (Pconst (3)%Z) (Pconst (256)%Z))) (Papp2 (Omul (Op_int)) (Pvar j) (Pconst (256)%Z))) ] ] ] ].

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
