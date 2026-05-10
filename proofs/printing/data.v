From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From Coq Require Import ZArith.

Require Import expr.

Definition arr_of_bytes (n : positive) (bs : seq u8) : WArray.array n :=
  rdflt (WArray.empty _) (WArray.fill n bs).
