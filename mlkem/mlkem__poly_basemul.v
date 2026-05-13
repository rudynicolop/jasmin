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

(* _poly_basemul *)
(* Local variables *)
Definition rp_14203 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14203).
Definition ap : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14204).
Definition bp_14205 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14205).
Definition qx16_14206 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14206).
Definition qinvx16_14207 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14207).
Definition zetaqinv_14208 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14208).
Definition zeta_14209 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14209).
Definition are_14210 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14210).
Definition aim_14211 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14211).
Definition bre_14212 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14212).
Definition bim_14213 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14213).

(* Signature *)
Definition tyin__poly_basemul : seq atype :=
  [:: aarr U16 256; aarr U16 256; aarr U16 256 ].
Definition args__poly_basemul : seq var_i :=
  [:: rp_14203.(gv); ap.(gv); bp_14205.(gv) ].
Definition tyout__poly_basemul : seq atype := [:: aarr U16 256 ].
Definition res__poly_basemul : seq var_i := [:: rp_14203.(gv) ].

(* Body *)
Definition body__poly_basemul : cmd :=
  [:: cassgn (Lvar qx16_14206.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jqx16 (Pconst (0)%Z))
    ; cassgn (Lvar qinvx16_14207.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jqinvx16 (Pconst (0)%Z))
    ; cassgn (Lvar zetaqinv_14208.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (272)%Z))
    ; cassgn (Lvar zeta_14209.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (304)%Z))
    ; cassgn (Lvar are_14210.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)))
    ; cassgn (Lvar aim_14211.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)))
    ; cassgn (Lvar bre_14212.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z)))
    ; cassgn (Lvar bim_14213.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z)))
    ; ccall [:: Lvar are_14210.(gv); Lvar aim_14211.(gv) ] __schoolbook16x [:: Pvar are_14210
                                                                    ; Pvar aim_14211
                                                                    ; Pvar bre_14212
                                                                    ; Pvar bim_14213
                                                                    ; Pvar zeta_14209
                                                                    ; Pvar zetaqinv_14208
                                                                    ; Pvar qx16_14206
                                                                    ; Pvar qinvx16_14207
                                                                    ; Pconst (0)%Z ]
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z))) (aword U256) (Pvar are_14210)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z))) (aword U256) (Pvar aim_14211)
    ; cassgn (Lvar are_14210.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)))
    ; cassgn (Lvar aim_14211.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)))
    ; cassgn (Lvar bre_14212.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z)))
    ; cassgn (Lvar bim_14213.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z)))
    ; ccall [:: Lvar are_14210.(gv); Lvar aim_14211.(gv) ] __schoolbook16x [:: Pvar are_14210
                                                                    ; Pvar aim_14211
                                                                    ; Pvar bre_14212
                                                                    ; Pvar bim_14213
                                                                    ; Pvar zeta_14209
                                                                    ; Pvar zetaqinv_14208
                                                                    ; Pvar qx16_14206
                                                                    ; Pvar qinvx16_14207
                                                                    ; Pconst (1)%Z ]
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z))) (aword U256) (Pvar are_14210)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z))) (aword U256) (Pvar aim_14211)
    ; cassgn (Lvar zetaqinv_14208.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (336)%Z))
    ; cassgn (Lvar zeta_14209.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (368)%Z))
    ; cassgn (Lvar are_14210.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z)))
    ; cassgn (Lvar aim_14211.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z)))
    ; cassgn (Lvar bre_14212.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z)))
    ; cassgn (Lvar bim_14213.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z)))
    ; ccall [:: Lvar are_14210.(gv); Lvar aim_14211.(gv) ] __schoolbook16x [:: Pvar are_14210
                                                                    ; Pvar aim_14211
                                                                    ; Pvar bre_14212
                                                                    ; Pvar bim_14213
                                                                    ; Pvar zeta_14209
                                                                    ; Pvar zetaqinv_14208
                                                                    ; Pvar qx16_14206
                                                                    ; Pvar qinvx16_14207
                                                                    ; Pconst (0)%Z ]
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z))) (aword U256) (Pvar are_14210)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z))) (aword U256) (Pvar aim_14211)
    ; cassgn (Lvar are_14210.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z)))
    ; cassgn (Lvar aim_14211.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z)))
    ; cassgn (Lvar bre_14212.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z)))
    ; cassgn (Lvar bim_14213.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z)))
    ; ccall [:: Lvar are_14210.(gv); Lvar aim_14211.(gv) ] __schoolbook16x [:: Pvar are_14210
                                                                    ; Pvar aim_14211
                                                                    ; Pvar bre_14212
                                                                    ; Pvar bim_14213
                                                                    ; Pvar zeta_14209
                                                                    ; Pvar zetaqinv_14208
                                                                    ; Pvar qx16_14206
                                                                    ; Pvar qinvx16_14207
                                                                    ; Pconst (1)%Z ]
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z))) (aword U256) (Pvar are_14210)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z))) (aword U256) (Pvar aim_14211)
    ; cassgn (Lvar zetaqinv_14208.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (664)%Z))
    ; cassgn (Lvar zeta_14209.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (696)%Z))
    ; cassgn (Lvar are_14210.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z)))
    ; cassgn (Lvar aim_14211.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z)))
    ; cassgn (Lvar bre_14212.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z)))
    ; cassgn (Lvar bim_14213.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z)))
    ; ccall [:: Lvar are_14210.(gv); Lvar aim_14211.(gv) ] __schoolbook16x [:: Pvar are_14210
                                                                    ; Pvar aim_14211
                                                                    ; Pvar bre_14212
                                                                    ; Pvar bim_14213
                                                                    ; Pvar zeta_14209
                                                                    ; Pvar zetaqinv_14208
                                                                    ; Pvar qx16_14206
                                                                    ; Pvar qinvx16_14207
                                                                    ; Pconst (0)%Z ]
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))) (aword U256) (Pvar are_14210)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z))) (aword U256) (Pvar aim_14211)
    ; cassgn (Lvar are_14210.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z)))
    ; cassgn (Lvar aim_14211.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z)))
    ; cassgn (Lvar bre_14212.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z)))
    ; cassgn (Lvar bim_14213.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z)))
    ; ccall [:: Lvar are_14210.(gv); Lvar aim_14211.(gv) ] __schoolbook16x [:: Pvar are_14210
                                                                    ; Pvar aim_14211
                                                                    ; Pvar bre_14212
                                                                    ; Pvar bim_14213
                                                                    ; Pvar zeta_14209
                                                                    ; Pvar zetaqinv_14208
                                                                    ; Pvar qx16_14206
                                                                    ; Pvar qinvx16_14207
                                                                    ; Pconst (1)%Z ]
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z))) (aword U256) (Pvar are_14210)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z))) (aword U256) (Pvar aim_14211)
    ; cassgn (Lvar zetaqinv_14208.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (728)%Z))
    ; cassgn (Lvar zeta_14209.(gv)) (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (760)%Z))
    ; cassgn (Lvar are_14210.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z)))
    ; cassgn (Lvar aim_14211.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z)))
    ; cassgn (Lvar bre_14212.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z)))
    ; cassgn (Lvar bim_14213.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z)))
    ; ccall [:: Lvar are_14210.(gv); Lvar aim_14211.(gv) ] __schoolbook16x [:: Pvar are_14210
                                                                    ; Pvar aim_14211
                                                                    ; Pvar bre_14212
                                                                    ; Pvar bim_14213
                                                                    ; Pvar zeta_14209
                                                                    ; Pvar zetaqinv_14208
                                                                    ; Pvar qx16_14206
                                                                    ; Pvar qinvx16_14207
                                                                    ; Pconst (0)%Z ]
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z))) (aword U256) (Pvar are_14210)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z))) (aword U256) (Pvar aim_14211)
    ; cassgn (Lvar are_14210.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z)))
    ; cassgn (Lvar aim_14211.(gv)) (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z)))
    ; cassgn (Lvar bre_14212.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z)))
    ; cassgn (Lvar bim_14213.(gv)) (aword U256) (Pget Unaligned AAdirect U256 bp_14205 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z)))
    ; ccall [:: Lvar are_14210.(gv); Lvar aim_14211.(gv) ] __schoolbook16x [:: Pvar are_14210
                                                                    ; Pvar aim_14211
                                                                    ; Pvar bre_14212
                                                                    ; Pvar bim_14213
                                                                    ; Pvar zeta_14209
                                                                    ; Pvar zetaqinv_14208
                                                                    ; Pvar qx16_14206
                                                                    ; Pvar qinvx16_14207
                                                                    ; Pconst (1)%Z ]
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z))) (aword U256) (Pvar are_14210)
    ; cassgn (Laset Unaligned AAdirect U256 rp_14203.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z))) (aword U256) (Pvar aim_14211) ].

Definition fd__poly_basemul : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__poly_basemul;
    f_params := args__poly_basemul;
    f_body := body__poly_basemul;
    f_tyout := tyout__poly_basemul;
    f_res := res__poly_basemul;
    f_extra := tt;
  |}.

End IDO.
