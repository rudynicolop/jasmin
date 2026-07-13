(* Display notations for Jasmin left values (scope [%L])

  Activate with [lv%L] or [Open Scope jlval_scope].
  [gvar] values coerce to [lval] via [Lvar] (see [lvar_of_gvar]).

* Discard (Lnone)

  - [lnone[b]]          discard of type bool           (Lnone _ abool)
  - [lnone[i]]          discard of type int            (Lnone _ aint)
  - [lnone[ws]]         discard of type word [ws]      (Lnone _ (aword ws))
  - [lnone[ws, len]]    discard of type array          (Lnone _ (aarr ws len))

* Variable (Lvar)

  - [x]                 variable [x] (via [gvar] coercion)

* Memory write (Lmem)

  - [mset[w](e)]        unaligned memory write, word size [w], address [e]
  - [mset_al[w](e)]     aligned memory write, word size [w], address [e]

* Array element write (Laset)

  - [aset[w](v, i)]     aligned (AAscale) element write, word size [w],
                        index [i]
  - [asetX[al, sc, w](v, i)]  general element write, alignment [al],
                              scale [sc], word size [w], index [i]

* Subarray write (Lasub)

  - [sset[w](v, len, i)]        scaled (AAscale) subarray write, word size
                                [w], length [len], index [i]
  - [sset_direct[w](v, len, i)] direct (AAdirect) subarray write, word size
                                [w], length [len], index [i] *)

From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr.
Require Import expr_notations.

Declare Scope jlval_scope.
Delimit Scope jlval_scope with L.
Bind Scope jlval_scope with lval.

Coercion gv : gvar >-> var_i.

(* [jatype] doesn't work for some reason, so we do explicit cases. *)
Notation "lnone[ 'b' ]" := (Lnone dummy_var_info abool)
  (at level 0,
   format "lnone[ b ]") : jlval_scope.

Notation "lnone[ 'i' ]" := (Lnone dummy_var_info aint)
  (at level 0,
   format "lnone[ i ]") : jlval_scope.

Notation "lnone[ ws ]" := (Lnone dummy_var_info (aword ws))
  (at level 0, ws custom jwsize at level 0,
   format "lnone[ ws ]") : jlval_scope.

Notation "lnone[ ws , len ]" := (Lnone dummy_var_info (aarr ws len))
  (at level 0, ws custom jwsize at level 0,
   len constr at level 0,
   format "lnone[ ws ,  len ]") : jlval_scope.

Notation "mset[ w ]( e )" := (Lmem Unaligned w dummy_var_info e%E)
  (at level 0, w custom jwsize at level 0, e at level 99,
   format "mset[ w ]( e )") : jlval_scope.

Notation "mset_al[ w ]( e )" := (Lmem Aligned w dummy_var_info e%E)
  (at level 0, w custom jwsize at level 0, e at level 99,
   format "mset_al[ w ]( e )") : jlval_scope.

Notation "aset[ w ]( v , i )" :=
  (Laset Aligned AAscale w v i%E)
  (at level 0, w custom jwsize at level 0, v constr at level 0,
   i at level 99,
   format "aset[ w ]( v ,  i )") : jlval_scope.

Notation "asetX[ al , sc , w ]( v , i )" :=
  (Laset al sc w v i%E)
  (at level 0, al constr at level 0, sc constr at level 0,
   w custom jwsize at level 0, v constr at level 0,
   i at level 99,
   format "asetX[ al ,  sc ,  w ]( v ,  i )") : jlval_scope.

Notation "sset[ w ]( v , len , i )" :=
  (Lasub AAscale w len%positive v i%E)
  (at level 0, w custom jwsize at level 0, v constr at level 0,
   len constr at level 0, i at level 99,
   format "sset[ w ]( v ,  len ,  i )") : jlval_scope.

Notation "sset_direct[ w ]( v , len , i )" :=
  (Lasub AAdirect w len%positive v i%E)
  (at level 0, w custom jwsize at level 0, v constr at level 0,
   len constr at level 0, i at level 99,
   format "sset_direct[ w ]( v ,  len ,  i )") : jlval_scope.

Section LvalTests.

Context (x y : gvar) (gx gy : gvar).

Goal (lnone[b])%L = Lnone dummy_var_info abool. done. Qed.
Goal (lnone[i])%L = Lnone dummy_var_info aint. done. Qed.
Goal (lnone[U64])%L = Lnone dummy_var_info (aword U64). done. Qed.
Goal (lnone[U32])%L = Lnone dummy_var_info (aword U32). done. Qed.
Goal (lnone[U64, 4])%L = Lnone dummy_var_info (aarr U64 4). done. Qed.
Goal (x : lval) = Lvar x.(gv). done. Qed.

Goal (mset[U64](0))%L =
  Lmem Unaligned U64 dummy_var_info (Pconst 0). done. Qed.
Goal (mset[U32](0))%L =
  Lmem Unaligned U32 dummy_var_info (Pconst 0). done. Qed.
Goal (mset[U64](gx))%L =
  Lmem Unaligned U64 dummy_var_info (Pvar gx). done. Qed.
Goal (mset[U64](gx +[U64] 4))%L =
  Lmem Unaligned U64 dummy_var_info
    (Papp2 (Oadd (Op_w U64)) (Pvar gx) (Pconst 4)).
done. Qed.

Goal (aset[U64](x, 0))%L =
  Laset Aligned AAscale U64 x.(gv) (Pconst 0). done. Qed.
Goal (aset[U32](x, 0))%L =
  Laset Aligned AAscale U32 x.(gv) (Pconst 0). done. Qed.
Goal (aset[U64](x, gx))%L =
  Laset Aligned AAscale U64 x.(gv) (Pvar gx). done. Qed.
Goal (aset[U64](x, gx +[U64] 1))%L =
  Laset Aligned AAscale U64 x.(gv)
    (Papp2 (Oadd (Op_w U64)) (Pvar gx) (Pconst 1)).
done. Qed.

Goal (sset[U64](x, 4, 0))%L =
  Lasub AAscale U64 4 x.(gv) (Pconst 0). done. Qed.
Goal (sset[U32](x, 8, 0))%L =
  Lasub AAscale U32 8 x.(gv) (Pconst 0). done. Qed.
Goal (sset[U64](x, 4, gx))%L =
  Lasub AAscale U64 4 x.(gv) (Pvar gx). done. Qed.

Goal (mset_al[U64](0))%L =
  Lmem Aligned U64 dummy_var_info (Pconst 0). done. Qed.
Goal (mset_al[U32](gx))%L =
  Lmem Aligned U32 dummy_var_info (Pvar gx). done. Qed.

Goal (asetX[Aligned, AAscale, U64](x, 0))%L =
  Laset Aligned AAscale U64 x.(gv) (Pconst 0). done. Qed.
Goal (asetX[Unaligned, AAdirect, U32](x, 0))%L =
  Laset Unaligned AAdirect U32 x.(gv) (Pconst 0). done. Qed.

Goal (sset_direct[U64](x, 4, 0))%L =
  Lasub AAdirect U64 4 x.(gv) (Pconst 0). done. Qed.
Goal (sset_direct[U32](x, 8, gx))%L =
  Lasub AAdirect U32 8 x.(gv) (Pvar gx). done. Qed.

End LvalTests.
