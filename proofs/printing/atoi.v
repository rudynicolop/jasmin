From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From Coq Require Import ZArith.

Require Import expr ident var.
Require Import arch_extra arch_utils.

Require x86_decl x86_instr_decl x86_extra.
Require arm_decl arm_instr_decl arm_extra.
Require riscv_decl riscv_instr_decl riscv_extra.

(* TODO move arch_utls.v *)
Definition inj_of_empty {T} : injective (of_empty T).
Proof. by case. Qed.

(* TODO move arch_utls.v *)
Definition empty_toI {t} : ToIdent (t := t) empty :=
  {|
    to_ident := of_empty _;
    of_ident := _;
    inj_to_ident := inj_of_empty;
    of_identE := fun _ => erefl;
  |}.

(* TODO Remove when [Ident] module is removed. *)
Class IdentOracles :=
  {
    mkident : Z -> Ident.ident;
    mkident_inj : injective mkident;
    mkfname : Z -> funname;
  }.

Section WITH_IDO.

Context {IdO : IdentOracles}.

Definition mk_rocq_gvar (s : v_scope) (t : atype) (i : Ident.ident) : gvar :=
  {| gs := s; gv := mk_var_i {| vtype := t; vname := i; |}; |}.

(* TODO generalize to any fintype *)
Section X86_ATOI.

Import x86_decl x86_instr_decl x86_extra.

Definition x86_reg_to_ident (r : register) : Ident.ident :=
  mkident (Z.of_nat (find (pred1 r) cenum)).

Lemma x86_reg_inj_to_ident : injective x86_reg_to_ident.
Proof.
  move=> r1 r2 /mkident_inj /Nat2Z.inj h.
  (* TODO separate lemma for any fintype *)
  have Hr1 : has (pred1 r1) (cenum : seq register)
    by rewrite has_pred1; exact: mem_cenum r1.
  have Hr2 : has (pred1 r2) (cenum : seq register)
    by rewrite has_pred1; exact: mem_cenum r2.
  by rewrite -(eqP (nth_find r1 Hr1)) (congr1 (nth r1 cenum) h)
             (eqP (nth_find r1 Hr2)).
Qed.

Definition x86_toI_r : ToIdent register :=
  {|
    to_ident := x86_reg_to_ident;
    of_ident := _;
    inj_to_ident := x86_reg_inj_to_ident;
    of_identE := fun _ => erefl;
  |}.

Definition x86_reg_ext_to_ident (rx : register_ext) : Ident.ident :=
  mkident (Z.of_nat (size (cenum : seq register) + find (pred1 rx) cenum)).

Lemma x86_reg_ext_inj_to_ident : injective x86_reg_ext_to_ident.
Proof.
  move=> r1 r2 /mkident_inj /Nat2Z.inj /addnI h.
  have Hr1 : has (pred1 r1) (cenum : seq register_ext)
    by rewrite has_pred1; exact: mem_cenum r1.
  have Hr2 : has (pred1 r2) (cenum : seq register_ext)
    by rewrite has_pred1; exact: mem_cenum r2.
  by rewrite -(eqP (nth_find r1 Hr1)) (congr1 (nth r1 cenum) h)
             (eqP (nth_find r1 Hr2)).
Qed.

Definition x86_toI_rx : ToIdent register_ext :=
  {|
    to_ident := x86_reg_ext_to_ident;
    of_ident := _;
    inj_to_ident := x86_reg_ext_inj_to_ident;
    of_identE := fun _ => erefl;
  |}.

Definition x86_xmm_to_ident (x : xmm_register) : Ident.ident :=
  mkident (Z.of_nat (find (pred1 x) cenum)).

Lemma x86_xmm_inj_to_ident : injective x86_xmm_to_ident.
Proof.
  move=> r1 r2 /mkident_inj /Nat2Z.inj h.
  have Hr1 : has (pred1 r1) (cenum : seq xmm_register)
    by rewrite has_pred1; exact: mem_cenum r1.
  have Hr2 : has (pred1 r2) (cenum : seq xmm_register)
    by rewrite has_pred1; exact: mem_cenum r2.
  by rewrite -(eqP (nth_find r1 Hr1)) (congr1 (nth r1 cenum) h)
             (eqP (nth_find r1 Hr2)).
Qed.

Definition x86_toI_x : ToIdent xmm_register :=
  {|
    to_ident := x86_xmm_to_ident;
    of_ident := _;
    inj_to_ident := x86_xmm_inj_to_ident;
    of_identE := fun _ => erefl;
  |}.

Definition x86_rflag_to_ident (f : rflag) : Ident.ident :=
  mkident (Z.of_nat (find (pred1 f) cenum)).

Lemma x86_rflag_inj_to_ident : injective x86_rflag_to_ident.
Proof.
  move=> r1 r2 /mkident_inj /Nat2Z.inj h.
  have Hr1 : has (pred1 r1) (cenum : seq rflag)
    by rewrite has_pred1; exact: mem_cenum r1.
  have Hr2 : has (pred1 r2) (cenum : seq rflag)
    by rewrite has_pred1; exact: mem_cenum r2.
  by rewrite -(eqP (nth_find r1 Hr1)) (congr1 (nth r1 cenum) h)
             (eqP (nth_find r1 Hr2)).
Qed.

Definition x86_toI_f : ToIdent rflag :=
  {|
    to_ident := x86_rflag_to_ident;
    of_ident := _;
    inj_to_ident := x86_rflag_inj_to_ident;
    of_identE := fun _ => erefl;
  |}.

Lemma x86_inj_toI_reg_regx (r : register) (rx : register_ext) :
  to_ident (ToIdent := x86_toI_r) r <> to_ident (ToIdent := x86_toI_rx) rx.
Proof. by move=> /mkident_inj /Nat2Z.inj; case: r; case: rx. Qed.

Definition x86_atoI : arch_toIdent :=
  {|
    toI_r := x86_toI_r;
    toI_rx := x86_toI_rx;
    toI_x := x86_toI_x;
    toI_f := x86_toI_f;
    inj_toI_reg_regx := x86_inj_toI_reg_regx;
  |}.

End X86_ATOI.


Section ARM_ATOI.

Import arm_decl arm_instr_decl arm_extra.

Definition arm_reg_to_ident (r : register) : Ident.ident :=
  mkident (Z.of_nat (find (pred1 r) cenum)).

Lemma arm_reg_inj_to_ident : injective arm_reg_to_ident.
Proof.
  move=> r1 r2 /mkident_inj /Nat2Z.inj h.
  have Hr1 : has (pred1 r1) (cenum : seq register)
    by rewrite has_pred1; exact: mem_cenum r1.
  have Hr2 : has (pred1 r2) (cenum : seq register)
    by rewrite has_pred1; exact: mem_cenum r2.
  by rewrite -(eqP (nth_find r1 Hr1)) (congr1 (nth r1 cenum) h)
             (eqP (nth_find r1 Hr2)).
Qed.

Definition arm_toI_r : ToIdent register :=
  {|
    to_ident := arm_reg_to_ident;
    of_ident := _;
    inj_to_ident := arm_reg_inj_to_ident;
    of_identE := fun _ => erefl;
  |}.

Definition arm_rflag_to_ident (f : rflag) : Ident.ident :=
  mkident (Z.of_nat (find (pred1 f) cenum)).

Lemma arm_rflag_inj_to_ident : injective arm_rflag_to_ident.
Proof.
  move=> r1 r2 /mkident_inj /Nat2Z.inj h.
  have Hr1 : has (pred1 r1) (cenum : seq rflag)
    by rewrite has_pred1; exact: mem_cenum r1.
  have Hr2 : has (pred1 r2) (cenum : seq rflag)
    by rewrite has_pred1; exact: mem_cenum r2.
  by rewrite -(eqP (nth_find r1 Hr1)) (congr1 (nth r1 cenum) h)
             (eqP (nth_find r1 Hr2)).
Qed.

Definition arm_toI_f : ToIdent rflag :=
  {|
    to_ident := arm_rflag_to_ident;
    of_ident := _;
    inj_to_ident := arm_rflag_inj_to_ident;
    of_identE := fun _ => erefl;
  |}.

Definition arm_atoI : arch_toIdent :=
  {|
    toI_r := arm_toI_r;
    toI_rx := empty_toI;
    toI_x := empty_toI;
    toI_f := arm_toI_f;
    inj_toI_reg_regx := fun _ x => of_empty _ x;
  |}.

End ARM_ATOI.


Section RISCV_ATOI.

Import riscv_decl riscv_instr_decl riscv_extra.

Definition riscv_reg_to_ident (r : register) : Ident.ident :=
  mkident (Z.of_nat (find (pred1 r) cenum)).

Lemma riscv_reg_inj_to_ident : injective riscv_reg_to_ident.
Proof.
  move=> r1 r2 /mkident_inj /Nat2Z.inj h.
  have Hr1 : has (pred1 r1) (cenum : seq register)
    by rewrite has_pred1; exact: mem_cenum r1.
  have Hr2 : has (pred1 r2) (cenum : seq register)
    by rewrite has_pred1; exact: mem_cenum r2.
  by rewrite -(eqP (nth_find r1 Hr1)) (congr1 (nth r1 cenum) h)
             (eqP (nth_find r1 Hr2)).
Qed.

Definition riscv_toI_r : ToIdent register :=
  {|
    to_ident := riscv_reg_to_ident;
    of_ident := _;
    inj_to_ident := riscv_reg_inj_to_ident;
    of_identE := fun _ => erefl;
  |}.

Definition riscv_atoI : arch_toIdent :=
  {|
    toI_r := riscv_toI_r;
    toI_rx := empty_toI;
    toI_x := empty_toI;
    toI_f := empty_toI;
    inj_toI_reg_regx := fun _ x => of_empty _ x;
  |}.

End RISCV_ATOI.

End WITH_IDO.
