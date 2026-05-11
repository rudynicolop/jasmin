From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr.
Require Import expr_notations.

(** * Display notations for Jasmin left values

    Wrap a [lval] in [lval:( lv )] to view it in Jasmin-like syntax.
    Example:
      Check lval:( aset[U64](x, #0) ).

    Notation summary:
      - lnone[b]             = discard of type bool   (Lnone _ abool)
      - lnone[i]             = discard of type int    (Lnone _ aint)
      - lnone[ws]            = discard of type word   (Lnone _ (aword ws))
      - lnone[ws, len]       = discard of type array  (Lnone _ (aarr ws len))
      - x                    = variable (Lvar)
      - st[w](e)         = unaligned memory write of word size w to address e
      - aset[w](v, e)         = aligned array element write at index e
      - asub[w](v, len, e)    = aligned subarray write of word size w

    Not supported:
      - [Lmem Aligned w vi e]  : aligned memory write (only [Lmem Unaligned]
                                 is covered via [st[w](e)])
      - [Laset] with alignment other than [Aligned] or scale other than
        [AAscale]
      - [Lasub] with scale other than [AAscale]

    Precedence: all constructors are atoms (level 0).
*)

Declare Custom Entry lval.

(* -------------------------------------------------------------------------- *)
(* Entry and exit *)

Notation "lval:( e )" := e
  (e custom lval at level 99,
   format "'lval:(' e ')'").

Notation "rocq:( e )" := e
  (in custom lval at level 0, e constr at level 99).

Notation "( e )" := e
  (in custom lval at level 0, e custom lval at level 99).

(* -------------------------------------------------------------------------- *)
(* Discard *)

Notation "lnone[ 'b' ]" := (Lnone dummy_var_info abool)
  (in custom lval at level 0).
Notation "lnone[ 'i' ]" := (Lnone dummy_var_info aint)
  (in custom lval at level 0).
Notation "lnone[ ws ]" := (Lnone dummy_var_info (aword ws))
  (in custom lval at level 0, ws constr at level 0).
Notation "lnone[ ws , len ]" := (Lnone dummy_var_info (aarr ws len))
  (in custom lval at level 0, ws constr at level 0, len constr at level 0).

(* -------------------------------------------------------------------------- *)
(* Variable *)

Notation "x" := (Lvar x.(gv))
  (in custom lval at level 0, x constr at level 0).

(* -------------------------------------------------------------------------- *)
(* Aligned memory store --st[w](e) *)

Notation "st[ w ]( e )" := (Lmem Unaligned w dummy_var_info e)
  (in custom lval,
   w constr at level 0, e custom expr at level 0).

(* -------------------------------------------------------------------------- *)
(* Aligned array element write --aset[w](v, i) *)

Notation "aset[ w ]( v , i )" := (Laset Aligned AAscale w v.(gv) i)
  (in custom lval,
   w constr at level 0, v constr at level 0, i custom expr at level 99).

(* -------------------------------------------------------------------------- *)
(* Aligned subarray write --asub[w](v, len, i) *)

Notation "asub[ w ]( v , len , i )" := (Lasub AAscale w len v.(gv) i)
  (in custom lval,
   w constr at level 0, v constr at level 0, len constr at level 0,
   i custom expr at level 99).

Section LvalTests.

Context (x y : gvar) (gx gy : gvar).

Goal lval:( lnone[b] ) = Lnone dummy_var_info abool. done. Qed.
Goal lval:( lnone[i] ) = Lnone dummy_var_info aint. done. Qed.
Goal lval:( lnone[U64] ) = Lnone dummy_var_info (aword U64). done. Qed.
Goal lval:( lnone[U32] ) = Lnone dummy_var_info (aword U32). done. Qed.
Goal lval:( lnone[U64, 4] ) = Lnone dummy_var_info (aarr U64 4). done. Qed.
Goal lval:( x ) = Lvar x.(gv). done. Qed.

Goal lval:( st[U64](#0) ) =
  Lmem Unaligned U64 dummy_var_info (Pconst 0). done. Qed.
Goal lval:( st[U32](#0) ) =
  Lmem Unaligned U32 dummy_var_info (Pconst 0). done. Qed.
Goal lval:( st[U64](gx) ) =
  Lmem Unaligned U64 dummy_var_info (Pvar gx). done. Qed.
Goal lval:( st[U64](gx +64u #4) ) =
  Lmem Unaligned U64 dummy_var_info
    (Papp2 (Oadd (Op_w U64)) (Pvar gx) (Pconst 4)).
done. Qed.

Goal lval:( aset[U64](x, #0) ) =
  Laset Aligned AAscale U64 x.(gv) (Pconst 0). done. Qed.
Goal lval:( aset[U32](x, #0) ) =
  Laset Aligned AAscale U32 x.(gv) (Pconst 0). done. Qed.
Goal lval:( aset[U64](x, gx) ) =
  Laset Aligned AAscale U64 x.(gv) (Pvar gx). done. Qed.
Goal lval:( aset[U64](x, gx +64u #1) ) =
  Laset Aligned AAscale U64 x.(gv)
    (Papp2 (Oadd (Op_w U64)) (Pvar gx) (Pconst 1)).
done. Qed.

Goal lval:( asub[U64](x, 4, #0) ) =
  Lasub AAscale U64 4 x.(gv) (Pconst 0). done. Qed.
Goal lval:( asub[U32](x, 8, #0) ) =
  Lasub AAscale U32 8 x.(gv) (Pconst 0). done. Qed.
Goal lval:( asub[U64](x, 4, gx) ) =
  Lasub AAscale U64 4 x.(gv) (Pvar gx). done. Qed.

End LvalTests.
