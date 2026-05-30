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

(* _i_poly_decompress *)
(* Local variables *)
Definition rp_16 : gvar := mk_rocq_gvar Slocal (aarr U16 256) (mkident 13949).
Definition a_36 : gvar := mk_rocq_gvar Slocal (aarr U8 128) (mkident 13950).
Definition x16p_0 : gvar := mk_rocq_gvar Slocal (aarr U16 16) (mkident 13951).
Definition q : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13952).
Definition x32p : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 13953).
Definition shufbidx : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13954).
Definition mask_1 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13955).
Definition shift_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13956).
Definition i_86 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13957).
Definition h : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 13958).
Definition sh_22 : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 13959).
Definition f_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13960).

(* Signature *)
Definition tyin__i_poly_decompress : seq atype :=
  [:: aarr U16 256; aarr U8 128 ].
Definition args__i_poly_decompress : seq var_i := [:: rp_16.(gv); a_36.(gv) ].
Definition tyout__i_poly_decompress : seq atype := [:: aarr U16 256 ].
Definition res__i_poly_decompress : seq var_i := [:: rp_16.(gv) ].

(* Body *)
Definition body__i_poly_decompress : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar x16p_0.(gv)) AT_none (aarr U16 16) (Pvar jqx16))
    ; MkI dummy_instr_info (Cassgn (Lvar q.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 x16p_0 (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar x32p.(gv)) AT_none (aarr U8 32) (Pvar pd_jshufbidx))
    ; MkI dummy_instr_info (Cassgn (Lvar shufbidx.(gv)) AT_none (aword U256) (Pget Aligned AAscale U256 x32p (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Copn [:: Lvar mask_1.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pvar pd_mask_s ])
    ; MkI dummy_instr_info (Copn [:: Lvar shift_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pvar pd_shift_s ])
    ; MkI dummy_instr_info (Cfor
                              (i_86.(gv))
                              (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Pconst (256)%Z) (Pconst (16)%Z))
                              [:: MkI dummy_instr_info (Cassgn (Lvar h.(gv)) AT_none (aword U128) (Papp1 (Ozeroext U128 U64) (Pget Unaligned AAdirect U64 a_36 (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_86)))))
                                ; MkI dummy_instr_info (Cassgn (Lvar sh_22.(gv)) AT_none (aword U128) (Pvar h))
                                ; MkI dummy_instr_info (Copn [:: Lvar f_0.(gv) ] AT_none (Oasm ((BaseOp ((None), VBROADCASTI128)))) [:: Pvar sh_22 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pvar f_0
                                                                    ; Pvar shufbidx ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f_0
                                                                    ; Pvar mask_1 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar f_0
                                                                    ; Pvar shift_0 ])
                                ; MkI dummy_instr_info (Copn [:: Lvar f_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPMULHRS U256))))) [:: Pvar f_0
                                                                    ; Pvar q ])
                                ; MkI dummy_instr_info (Cassgn (Laset Aligned AAscale U256 rp_16.(gv) (Pvar i_86)) AT_none (aword U256) (Pvar f_0)) ]) ].

Definition fd__i_poly_decompress : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__i_poly_decompress;
    f_params := args__i_poly_decompress;
    f_body := body__i_poly_decompress;
    f_tyout := tyout__i_poly_decompress;
    f_res := res__i_poly_decompress;
    f_extra := tt;
  |}.

End IDO.
