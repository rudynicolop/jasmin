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

(* __cmov *)
(* Local variables *)
Definition dst : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 13659).
Definition src : gvar := mk_rocq_gvar Slocal (aarr U8 32) (mkident 13660).
Definition cnd_0 : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13661).
Definition scnd : gvar := mk_rocq_gvar Slocal (aword U64) (mkident 13662).
Definition m_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13663).
Definition f_3 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13664).
Definition g_0 : gvar := mk_rocq_gvar Slocal (aword U256) (mkident 13665).

(* Signature *)
Definition tyin___cmov : seq atype := [:: aarr U8 32; aarr U8 32; aword U64 ].
Definition args___cmov : seq var_i := [:: dst.(gv); src.(gv); cnd_0.(gv) ].
Definition tyout___cmov : seq atype := [:: aarr U8 32 ].
Definition res___cmov : seq var_i := [:: dst.(gv) ].

(* Body *)
Definition body___cmov : cmd :=
  [:: MkI dummy_instr_info (Cassgn (Lvar cnd_0.(gv)) AT_none (aword U64) (Papp1 (Oneg (Op_w U64)) (Pvar cnd_0)))
    ; MkI dummy_instr_info (Cassgn (Lvar scnd.(gv)) AT_none (aword U64) (Pvar cnd_0))
    ; MkI dummy_instr_info (Copn [:: Lvar m_0.(gv) ] AT_none (Oasm ((BaseOp ((None), (VPBROADCAST VE64 U256))))) [:: Pvar scnd ])
    ; MkI dummy_instr_info (Cassgn (Lvar f_3.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 src (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Cassgn (Lvar g_0.(gv)) AT_none (aword U256) (Pget Unaligned AAdirect U256 dst (Pconst (0)%Z)))
    ; MkI dummy_instr_info (Copn [:: Lvar f_3.(gv) ] AT_none (Oasm ((BaseOp ((None), (BLENDV VE8 U256))))) [:: Pvar f_3
                                                                    ; Pvar g_0
                                                                    ; Pvar m_0 ])
    ; MkI dummy_instr_info (Cassgn (Laset Unaligned AAdirect U256 dst.(gv) (Pconst (0)%Z)) AT_none (aword U256) (Pvar f_3)) ].

Definition fd___cmov : ufundef :=
  {|
    f_info := FunInfo.witness;
    f_contract := None;
    f_tyin := tyin___cmov;
    f_params := args___cmov;
    f_body := body___cmov;
    f_tyout := tyout___cmov;
    f_res := res___cmov;
    f_extra := tt;
  |}.

End IDO.
