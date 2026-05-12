Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Stdlib Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr.
Require Import expr_notations.

(* TODO Add a docstring at the top of the file with every notation explained.
Give an exhaustive list of all the cases that are not supported by notations.
Here's the previous one as inspiration (needs updating):


-(** * Display notations for Jasmin left values
-
-    Wrap a [lval] in [lval:( lv )] to view it in Jasmin-like syntax.
-    Example:
-      Check lval:( aset[U64](x, #0) ).
-
-    Notation summary:
-      - lnone[b]             = discard of type bool   (Lnone _ abool)
-      - lnone[i]             = discard of type int    (Lnone _ aint)
-      - lnone[ws]            = discard of type word   (Lnone _ (aword ws))
-      - lnone[ws, len]       = discard of type array  (Lnone _ (aarr ws len))
-      - x                    = variable (Lvar)
-      - mem[w](e)         = unaligned memory write of word size w to address e
-      - aset[w](v, e)         = aligned array element write at index e
-      - asub[w](v, len, e)    = aligned subarray write of word size w
-
-    Not supported:
-      - [Lmem Aligned w vi e]  : aligned memory write (only [Lmem Unaligned]
-                                 is covered via [mem[w](e)])
-      - [Laset] with alignment other than [Aligned] or scale other than
-        [AAscale]
-      - [Lasub] with scale other than [AAscale]
-
-    Precedence: all constructors are atoms (level 0).
-*)

 *)

(* Bridge coercion: bare gvar in lval position elaborates to Lvar v.(gv) *)
Definition lvar_of_gvar (v : gvar) : lval := Lvar v.(gv).
Coercion lvar_of_gvar : gvar >-> lval.

Declare Scope jlval_scope.
Delimit Scope jlval_scope with L.
Bind Scope jlval_scope with lval.

Notation "lnone[ 'b' ]" := (Lnone dummy_var_info abool)
  (at level 0) : jlval_scope.
Notation "lnone[ 'i' ]" := (Lnone dummy_var_info aint)
  (at level 0) : jlval_scope.
Notation "lnone[ ws ]" := (Lnone dummy_var_info (aword ws))
  (at level 0, ws constr at level 0) : jlval_scope.
Notation "lnone[ ws , len ]" := (Lnone dummy_var_info (aarr ws len))
  (at level 0, ws constr at level 0, len constr at level 0)
  : jlval_scope.

Notation "mem[ w ]( e )" := (Lmem Unaligned w dummy_var_info e%E)
  (at level 0, w constr at level 0, e at level 99) : jlval_scope.

Notation "aset[ w ]( v , i )" :=
  (Laset Aligned AAscale w v.(gv) i%E)
  (at level 0, w constr at level 0, v constr at level 0,
   i at level 99) : jlval_scope.

Notation "asub[ w ]( v , len , i )" :=
  (Lasub AAscale w len v.(gv) i%E)
  (at level 0, w constr at level 0, v constr at level 0,
   len constr at level 0, i at level 99) : jlval_scope.

Section LvalTests.

Context (x y : gvar) (gx gy : gvar).

Goal (lnone[b])%L = Lnone dummy_var_info abool. done. Qed.
Goal (lnone[i])%L = Lnone dummy_var_info aint. done. Qed.
Goal (lnone[U64])%L = Lnone dummy_var_info (aword U64). done. Qed.
Goal (lnone[U32])%L = Lnone dummy_var_info (aword U32). done. Qed.
Goal (lnone[U64, 4])%L = Lnone dummy_var_info (aarr U64 4). done. Qed.
Goal (x : lval) = Lvar x.(gv). done. Qed.

Goal (mem[U64](0))%L =
  Lmem Unaligned U64 dummy_var_info (Pconst 0). done. Qed.
Goal (mem[U32](0))%L =
  Lmem Unaligned U32 dummy_var_info (Pconst 0). done. Qed.
Goal (mem[U64](gx))%L =
  Lmem Unaligned U64 dummy_var_info (Pvar gx). done. Qed.
Goal (mem[U64](gx +64u 4))%L =
  Lmem Unaligned U64 dummy_var_info
    (Papp2 (Oadd (Op_w U64)) (Pvar gx) (Pconst 4)).
done. Qed.

Goal (aset[U64](x, 0))%L =
  Laset Aligned AAscale U64 x.(gv) (Pconst 0). done. Qed.
Goal (aset[U32](x, 0))%L =
  Laset Aligned AAscale U32 x.(gv) (Pconst 0). done. Qed.
Goal (aset[U64](x, gx))%L =
  Laset Aligned AAscale U64 x.(gv) (Pvar gx). done. Qed.
Goal (aset[U64](x, gx +64u 1))%L =
  Laset Aligned AAscale U64 x.(gv)
    (Papp2 (Oadd (Op_w U64)) (Pvar gx) (Pconst 1)).
done. Qed.

Goal (asub[U64](x, 4, 0))%L =
  Lasub AAscale U64 4 x.(gv) (Pconst 0). done. Qed.
Goal (asub[U32](x, 8, 0))%L =
  Lasub AAscale U32 8 x.(gv) (Pconst 0). done. Qed.
Goal (asub[U64](x, 4, gx))%L =
  Lasub AAscale U64 4 x.(gv) (Pvar gx). done. Qed.

End LvalTests.
