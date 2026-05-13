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

(* _i_poly_decompress *)
(* Local variables *)
Definition rp_13949 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 13949).
Definition a_13950 : gvar :=
  mk_rocq_gvar Slocal (aarr U8 128) (mkident 13950).
Definition x16p_13951 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 16) (mkident 13951).
Definition q : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13952).
Definition x32p : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 13953).
Definition shufbidx : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13954).
Definition mask_13955 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13955).
Definition shift_13956 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 13956).
Definition i_13957 : gvar := mk_rocq_gvar Slocal (aint) (mkident 13957).
Definition h : gvar := mk_rocq_gvar Slocal (aword U128) (mkident 13958).
Definition sh_13959 : gvar :=
  mk_rocq_gvar Slocal (aword U128) (mkident 13959).
Definition f_13960 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13960).

(* Signature *)
Definition tyin__i_poly_decompress : seq atype :=
  [:: aarr U16 256; aarr U8 128 ].
Definition args__i_poly_decompress : seq var_i :=
  [:: rp_13949.(gv); a_13950.(gv) ].
Definition tyout__i_poly_decompress : seq atype := [:: aarr U16 256 ].
Definition res__i_poly_decompress : seq var_i := [:: rp_13949.(gv) ].

(* Body *)
Definition body__i_poly_decompress : cmd :=
  [:: cassgn (Lvar x16p_13951.(gv)) (aarr U16 16) (Pvar jqx16)
    ; cassgn (Lvar q.(gv)) (aword U256) (Pget Aligned AAscale U256 x16p_13951 (Pconst (0)%Z))
    ; cassgn (Lvar x32p.(gv)) (aarr U8 32) (Pvar pd_jshufbidx)
    ; cassgn (Lvar shufbidx.(gv)) (aword U256) (Pget Aligned AAscale U256 x32p (Pconst (0)%Z))
    ; copn [:: Lvar mask_13955.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pvar pd_mask_s ]
    ; copn [:: Lvar shift_13956.(gv) ] (Oasm ((BaseOp ((None), (VPBROADCAST VE32 U256))))) [:: Pvar pd_shift_s ]
    ; cfor
        (i_13957.(gv))
        (UpTo, Pconst (0)%Z, Papp2 (Odiv Unsigned (Op_int)) (Pconst (256)%Z) (Pconst (16)%Z))
        [:: cassgn (Lvar h.(gv)) (aword U128) (Papp1 (Ozeroext U128 U64) (Pget Unaligned AAdirect U64 a_13950 (Papp2 (Omul (Op_int)) (Pconst (8)%Z) (Pvar i_13957))))
          ; cassgn (Lvar sh_13959.(gv)) (aword U128) (Pvar h)
          ; copn [:: Lvar f_13960.(gv) ] (Oasm ((BaseOp ((None), VBROADCASTI128)))) [:: Pvar sh_13959 ]
          ; copn [:: Lvar f_13960.(gv) ] (Oasm ((BaseOp ((None), (VPSHUFB U256))))) [:: Pvar f_13960
                                                                    ; Pvar shufbidx ]
          ; copn [:: Lvar f_13960.(gv) ] (Oasm ((BaseOp ((None), (VPAND U256))))) [:: Pvar f_13960
                                                                    ; Pvar mask_13955 ]
          ; copn [:: Lvar f_13960.(gv) ] (Oasm ((BaseOp ((None), (VPMULL VE16 U256))))) [:: Pvar f_13960
                                                                    ; Pvar shift_13956 ]
          ; copn [:: Lvar f_13960.(gv) ] (Oasm ((BaseOp ((None), (VPMULHRS U256))))) [:: Pvar f_13960
                                                                    ; Pvar q ]
          ; cassgn (Laset Aligned AAscale U256 rp_13949.(gv) (Pvar i_13957)) (aword U256) (Pvar f_13960) ] ].

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
