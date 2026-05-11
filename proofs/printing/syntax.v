From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From Coq Require Import ZArith.

Require Import expr.

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

Definition cassert (l : assertion_label) (e : eassert) : instr :=
  mki (Cassert (l, e)).

#[global] Arguments cassert _%_string.

Definition cif (e : pexpr) (c1 c2 : cmd) : instr :=
  mki (Cif e c1 c2).

Definition cfor (v : var_i) (r : range) (c : cmd) : instr :=
  mki (Cfor v r c).

Definition cwhile (c1 : cmd) (e : pexpr) (c2 : cmd) : instr :=
  mki (Cwhile Align c1 e dummy_instr_info c2).

Definition ccall (lvs : lvals) (f : funname) (es : pexprs) : instr :=
  mki (Ccall lvs f es).

End CODE.
