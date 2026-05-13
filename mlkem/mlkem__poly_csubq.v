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

(* _poly_csubq *)
(* Local variables *)
Definition rp_14261 : gvar :=
  mk_rocq_gvar Slocal (aarr U16 256) (mkident 14261).
Definition qx16_14262 : gvar :=
  mk_rocq_gvar Slocal (aword U256) (mkident 14262).
Definition i_14263 : gvar := mk_rocq_gvar Slocal (aint) (mkident 14263).
Definition r_14264 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 14264).

(* Signature *)
Definition tyin__poly_csubq : seq atype := [:: aarr U16 256 ].
Definition args__poly_csubq : seq var_i := [:: rp_14261.(gv) ].
Definition tyout__poly_csubq : seq atype := [:: aarr U16 256 ].
Definition res__poly_csubq : seq var_i := [:: rp_14261.(gv) ].

(* Body *)
Definition body__poly_csubq : cmd :=
  [:: cassgn (Lvar qx16_14262.(gv)) (aword U256) (Pget Aligned AAscale U256 jqx16 (Pconst (0)%Z))
    ; cfor
        (i_14263.(gv))
        (UpTo, Pconst (0)%Z, Pconst (16)%Z)
        [:: cassgn (Lvar r_14264.(gv)) (aword U256) (Pget Unaligned AAdirect U256 rp_14261 (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_14263)))
          ; ccall [:: Lvar r_14264.(gv) ] __csubq [:: Pvar r_14264
                                                    ; Pvar qx16_14262 ]
          ; cassgn (Laset Unaligned AAdirect U256 rp_14261.(gv) (Papp2 (Omul (Op_int)) (Pconst (32)%Z) (Pvar i_14263))) (aword U256) (Pvar r_14264) ] ].

Definition fd__poly_csubq : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin__poly_csubq;
    f_params := args__poly_csubq;
    f_body := body__poly_csubq;
    f_tyout := tyout__poly_csubq;
    f_res := res__poly_csubq;
    f_extra := tt;
  |}.

End IDO.
