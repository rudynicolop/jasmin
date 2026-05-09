From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From Coq Require Import ZArith.

Require oseq.
Require Import expr ident var type global pseudo_operator sopn arch_extra.

Require x86_decl x86_instr_decl x86_extra.
Require arm_decl arm_instr_decl arm_extra.
Require riscv_decl riscv_instr_decl riscv_extra.

(* -------------------------------------------------------------------------- *)
(* Data *)

Definition arr_of_bytes (n : positive) (bs : seq u8) : WArray.array n :=
  rdflt (WArray.empty _) (WArray.fill n bs).

(* -------------------------------------------------------------------------- *)
(* Code *)

Section CODE.

Context
  {asm_op : Type}
  {asmop : asmOp asm_op}
.

Notation mki i := (MkI dummy_instr_info i) (only parsing).

Definition cassgn (lv : lval) (ty : atype) (e : pexpr) : instr :=
  mki (Cassgn lv AT_none ty e).

Definition copn (lvs : lvals) (o : sopn) (es : pexprs) : instr :=
  mki (Copn lvs AT_none o es).

Definition crandombytes
  (lv : lval) (ws : wsize) (n : positive) (e : pexpr) : instr :=
  mki (Csyscall [:: lv ] (RandomBytes ws n) [:: e ]).

Definition cassert (a : assertion) : instr := mki (Cassert a).

Definition cif (e : pexpr) (c1 c2 : cmd) : instr :=
  mki (Cif e c1 c2).

Definition cfor (v : var_i) (r : range) (c : cmd) : instr :=
  mki (Cfor v r c).

Definition cwhile
  (a : align) (c1 : cmd) (e : pexpr) (c2 : cmd) : instr :=
  mki (Cwhile a c1 e dummy_instr_info c2).

Definition ccall (lvs : lvals) (f : funname) (es : pexprs) : instr :=
  mki (Ccall lvs f es).

End CODE.


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

Definition arm_to_ident_empty : xregister -> Ident.ident.
Proof. by case. Defined.

Lemma arm_inj_empty : injective arm_to_ident_empty.
Proof. by case. Qed.

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

(* TODO declare as separate [ToIdent] records *)
Definition arm_atoI : arch_toIdent.
Proof.
  refine {|
    toI_r := arm_toI_r;
    toI_rx := {| to_ident := arm_to_ident_empty;
                 of_ident := _;
                 inj_to_ident := arm_inj_empty;
                 of_identE := fun _ => erefl |};
    toI_x := {| to_ident := arm_to_ident_empty;
                of_ident := _;
                inj_to_ident := arm_inj_empty;
                of_identE := fun _ => erefl |};
    toI_f := arm_toI_f;
    inj_toI_reg_regx := _;
  |}.
  by case.
Defined.

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

Definition riscv_to_ident_empty : rflag -> Ident.ident.
Proof. by case. Defined.

Lemma riscv_inj_empty : injective riscv_to_ident_empty.
Proof. by case. Qed.

(* TODO declare as separate [ToIdent] records *)
Definition riscv_atoI : arch_toIdent.
Proof.
  refine {|
    toI_r := riscv_toI_r;
    toI_rx := {| to_ident := riscv_to_ident_empty;
                 of_ident := _;
                 inj_to_ident := riscv_inj_empty;
                 of_identE := fun _ => erefl |};
    toI_x := {| to_ident := riscv_to_ident_empty;
                of_ident := _;
                inj_to_ident := riscv_inj_empty;
                of_identE := fun _ => erefl |};
    toI_f := {| to_ident := riscv_to_ident_empty;
                of_ident := _;
                inj_to_ident := riscv_inj_empty;
                of_identE := fun _ => erefl |};
    inj_toI_reg_regx := _;
  |}.
  by case.
Defined.

End RISCV_ATOI.

End WITH_IDO.
