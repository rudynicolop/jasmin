From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From Coq Require Import ZArith.

Require oseq.
Require Import expr ident var type global pseudo_operator sopn arch_extra.

Require x86_decl x86_instr_decl x86_extra.
Require arm_decl arm_instr_decl arm_extra.

Class IdentOracles :=
  {
    mkident : Z -> Ident.ident;
    mkident_inj : injective mkident;
    mkfunname : Z -> funname;
  }.

Section WITH_IDO.

Context {IdO : IdentOracles}.

Section X86_ATOI.

Import x86_decl x86_instr_decl x86_extra.

Definition x86_reg_to_ident (r : register) : Ident.ident :=
  mkident (Z.of_nat (find (pred1 r) cenum)).

Lemma x86_reg_inj_to_ident : injective x86_reg_to_ident.
Proof. by move=> r1 r2 /mkident_inj /Nat2Z.inj; case: r1; case: r2. Qed.

Definition x86_toI_r : ToIdent register :=
  {|
    to_ident := x86_reg_to_ident;
    of_ident := _;
    inj_to_ident := x86_reg_inj_to_ident;
    of_identE := fun _ => erefl;
  |}.

Definition x86_atoI : arch_toIdent.
Admitted.

End X86_ATOI.


Section ARM_ATOI.

Import arm_decl arm_instr_decl arm_extra.

Definition arm_reg_to_ident (r : register) : Ident.ident :=
  mkident (Z.of_nat (find (pred1 r) cenum)).

Lemma arm_reg_inj_to_ident : injective arm_reg_to_ident.
Proof. by move=> r1 r2 /mkident_inj /Nat2Z.inj; case: r1; case: r2. Qed.

Definition arm_toI_r : ToIdent register :=
  {|
    to_ident := arm_reg_to_ident;
    of_ident := _;
    inj_to_ident := arm_reg_inj_to_ident;
    of_identE := fun _ => erefl;
  |}.

End ARM_ATOI.

End WITH_IDO.
