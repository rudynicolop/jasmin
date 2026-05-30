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

(* _poly_basemul *)
(* Local variables *)
Definition rp_2 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14203).
Definition ap : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14204).
Definition bp_0 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 14205).
Definition qx16_6 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14206).
Definition qinvx16_2 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14207).
Definition zetaqinv_0 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14208).
Definition zeta_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14209).
Definition are_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14210).
Definition aim_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14211).
Definition bre_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14212).
Definition bim_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14213).

(* Signature *)
Definition tyin__poly_basemul : seq atype :=
  [:: aarr U16 256; aarr U16 256; aarr U16 256 ].
Definition args__poly_basemul : seq var_i :=
  [:: rp_2.(gv); ap.(gv); bp_0.(gv) ].
Definition tyout__poly_basemul : seq atype := [:: aarr U16 256 ].
Definition res__poly_basemul : seq var_i := [:: rp_2.(gv) ].

(* Body *)
Definition body__poly_basemul : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar qx16_6.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jqx16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar qinvx16_2.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jqinvx16 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar zetaqinv_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (272)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar zeta_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (304)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar are_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar aim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bre_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar are_0.(gv); Lvar aim_0.(gv) ] __schoolbook16x [:: Pvar are_0
                                                                    ; Pvar aim_0
                                                                    ; Pvar bre_0
                                                                    ; Pvar bim_0
                                                                    ; Pvar zeta_0
                                                                    ; Pvar zetaqinv_0
                                                                    ; Pvar qx16_6
                                                                    ; Pvar qinvx16_2
                                                                    ; Pconst (0)%Z ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (0)%Z))) AT_none (aword U256) (Pvar are_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (1)%Z))) AT_none (aword U256) (Pvar aim_0))
    ; MkI dummy_instr_info (Cassgn (Lvar are_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar aim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bre_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar are_0.(gv); Lvar aim_0.(gv) ] __schoolbook16x [:: Pvar are_0
                                                                    ; Pvar aim_0
                                                                    ; Pvar bre_0
                                                                    ; Pvar bim_0
                                                                    ; Pvar zeta_0
                                                                    ; Pvar zetaqinv_0
                                                                    ; Pvar qx16_6
                                                                    ; Pvar qinvx16_2
                                                                    ; Pconst (1)%Z ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (2)%Z))) AT_none (aword U256) (Pvar are_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (3)%Z))) AT_none (aword U256) (Pvar aim_0))
    ; MkI dummy_instr_info (Cassgn (Lvar zetaqinv_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (336)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar zeta_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (368)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar are_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar aim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bre_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar are_0.(gv); Lvar aim_0.(gv) ] __schoolbook16x [:: Pvar are_0
                                                                    ; Pvar aim_0
                                                                    ; Pvar bre_0
                                                                    ; Pvar bim_0
                                                                    ; Pvar zeta_0
                                                                    ; Pvar zetaqinv_0
                                                                    ; Pvar qx16_6
                                                                    ; Pvar qinvx16_2
                                                                    ; Pconst (0)%Z ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (4)%Z))) AT_none (aword U256) (Pvar are_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (5)%Z))) AT_none (aword U256) (Pvar aim_0))
    ; MkI dummy_instr_info (Cassgn (Lvar are_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar aim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bre_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar are_0.(gv); Lvar aim_0.(gv) ] __schoolbook16x [:: Pvar are_0
                                                                    ; Pvar aim_0
                                                                    ; Pvar bre_0
                                                                    ; Pvar bim_0
                                                                    ; Pvar zeta_0
                                                                    ; Pvar zetaqinv_0
                                                                    ; Pvar qx16_6
                                                                    ; Pvar qinvx16_2
                                                                    ; Pconst (1)%Z ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (6)%Z))) AT_none (aword U256) (Pvar are_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (7)%Z))) AT_none (aword U256) (Pvar aim_0))
    ; MkI dummy_instr_info (Cassgn (Lvar zetaqinv_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (664)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar zeta_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (696)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar are_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar aim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bre_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar are_0.(gv); Lvar aim_0.(gv) ] __schoolbook16x [:: Pvar are_0
                                                                    ; Pvar aim_0
                                                                    ; Pvar bre_0
                                                                    ; Pvar bim_0
                                                                    ; Pvar zeta_0
                                                                    ; Pvar zetaqinv_0
                                                                    ; Pvar qx16_6
                                                                    ; Pvar qinvx16_2
                                                                    ; Pconst (0)%Z ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (8)%Z))) AT_none (aword U256) (Pvar are_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (9)%Z))) AT_none (aword U256) (Pvar aim_0))
    ; MkI dummy_instr_info (Cassgn (Lvar are_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar aim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bre_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar are_0.(gv); Lvar aim_0.(gv) ] __schoolbook16x [:: Pvar are_0
                                                                    ; Pvar aim_0
                                                                    ; Pvar bre_0
                                                                    ; Pvar bim_0
                                                                    ; Pvar zeta_0
                                                                    ; Pvar zetaqinv_0
                                                                    ; Pvar qx16_6
                                                                    ; Pvar qinvx16_2
                                                                    ; Pconst (1)%Z ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (10)%Z))) AT_none (aword U256) (Pvar are_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (11)%Z))) AT_none (aword U256) (Pvar aim_0))
    ; MkI dummy_instr_info (Cassgn (Lvar zetaqinv_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (728)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar zeta_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 jzetas_exp (Pconst (760)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar are_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar aim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bre_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar are_0.(gv); Lvar aim_0.(gv) ] __schoolbook16x [:: Pvar are_0
                                                                    ; Pvar aim_0
                                                                    ; Pvar bre_0
                                                                    ; Pvar bim_0
                                                                    ; Pvar zeta_0
                                                                    ; Pvar zetaqinv_0
                                                                    ; Pvar qx16_6
                                                                    ; Pvar qinvx16_2
                                                                    ; Pconst (0)%Z ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (12)%Z))) AT_none (aword U256) (Pvar are_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (13)%Z))) AT_none (aword U256) (Pvar aim_0))
    ; MkI dummy_instr_info (Cassgn (Lvar are_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar aim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 ap (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bre_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z))))
    ; MkI dummy_instr_info (Cassgn (Lvar bim_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 bp_0 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z))))
    ; MkI dummy_instr_info (Ccall [:: Lvar are_0.(gv); Lvar aim_0.(gv) ] __schoolbook16x [:: Pvar are_0
                                                                    ; Pvar aim_0
                                                                    ; Pvar bre_0
                                                                    ; Pvar bim_0
                                                                    ; Pvar zeta_0
                                                                    ; Pvar zetaqinv_0
                                                                    ; Pvar qx16_6
                                                                    ; Pvar qinvx16_2
                                                                    ; Pconst (1)%Z ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (14)%Z))) AT_none (aword U256) (Pvar are_0))
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 rp_2.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pconst (15)%Z))) AT_none (aword U256) (Pvar aim_0)) ].

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
