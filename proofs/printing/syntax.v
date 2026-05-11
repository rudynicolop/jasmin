From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From Coq Require Import ZArith.

Require Import expr.

Notation mki i := (MkI dummy_instr_info i) (only parsing).

Notation cassgn lv ty e := (mki (Cassgn lv AT_none ty e)) (only parsing).

Notation copn lvs o es :=
  (mki (Copn lvs AT_none o es)) (only parsing).

Notation crandombytes lv ws n e :=
  (mki (Csyscall [:: lv] (RandomBytes ws n) [:: e])) (only parsing).

Notation cassert l e :=
  (mki (Cassert (l%string, e))) (only parsing).

Notation cif e c1 c2 :=
  (mki (Cif e c1 c2)) (only parsing).

Notation cfor v r c :=
  (mki (Cfor v r c)) (only parsing).

Notation cwhile c1 e c2 :=
  (mki (Cwhile Align c1 e dummy_instr_info c2)) (only parsing).

Notation ccall lvs f es :=
  (mki (Ccall lvs f es)) (only parsing).
