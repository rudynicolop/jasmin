From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr.

(** * Display notations for Jasmin expressions

    Wrap a [pexpr] in [expr:( e )] to view it in Jasmin-like syntax.
    Example:
      Check expr:( x +64u y *64u z ).

    Operator naming convention:
      - size suffix: 8u / 16u / 32u / 64u / 128u / 256u = word size + unsigned
      - signed suffix: 8s / 16s / 32s / 64s
      - integer (mathematical int) suffix: i
      - ld[w](e) = unaligned load of word size w from address e (address must be
                   an atom or parenthesised expression)
      - aget[w](v, e) = aligned array read of word size w at index e
      - asub[w](v, len, e) = aligned array sub-slice of word size w
      - i2w[N]   = int → word of size N
      - u2i[N]   = word N → unsigned int
      - s2i[N]   = word N → signed int
      - zext[M, N] = zero-extend from M to N
      - sext[M, N] = sign-extend from M to N

    Precedence (lower level = tighter binding):
       0  : ld[w](e) (load)
       0  : aget[w](v, e) (array read)
       0  : asub[w](v, len, e) (array sub-slice)
       2  : unary ![b], !Nu, -Nu, i2w[N], u2i[N], s2i[N],
            zext[M,N], sext[M,N], -i
       4  : *Nu, *i, /Nu, /Ns, %Nu, %Ns
       5  : <<Nu, >>Nu, >>sNu, <<rNu, >>rNu, <<i, >>si
       6  : +Nu, -Nu (binary), +i, -i (binary)
       7  : &Nu
       8  : ^Nu
       9  : |Nu
      10  : ==Nu, !=Nu, <Nu, <=Nu, >Nu, >=Nu, ==i, !=i, <i, <=i, >i, >=i, ==
      11  : &&
      12  : ||
      13  : if/then/else, ?Nu, ?b, ?i
*)

Declare Custom Entry expr.

(* -------------------------------------------------------------------------- *)
(* Entry and exit *)

Notation "expr:( e )" := e
  (e custom expr at level 99,
   format "'expr:(' e ')'").

Notation "rocq:( e )" := e
  (in custom expr at level 0, e constr at level 99).

Notation "( e )" := e
  (in custom expr at level 0, e custom expr at level 99).

(* -------------------------------------------------------------------------- *)
(* Constants and variables *)

Notation "# z" := (Pconst z)
  (in custom expr at level 0, z constr at level 0,
   format "# z").

Notation "'true'"  := (Pbool true)  (in custom expr at level 0).
Notation "'false'" := (Pbool false) (in custom expr at level 0).

Notation "x" := (Pvar x)
  (in custom expr at level 0, x constr at level 0).

(* -------------------------------------------------------------------------- *)
(* Memory loads (aligned) *)

Notation "ld[ w ]( e )" := (Pload Unaligned w e)
  (in custom expr, w constr at level 0, e custom expr at level 0).

(* -------------------------------------------------------------------------- *)
(* Array subscript — scale-indexed, aligned: aget[w](v, i) *)

Notation "aget[ w ]( v , i )" := (Pget Aligned AAscale w v i)
  (in custom expr,
   v constr at level 0, w constr at level 0, i custom expr at level 99).

(* -------------------------------------------------------------------------- *)
(* Array sub-slice — scale-indexed, aligned: asub[w](v, len, i) *)

Notation "asub[ w ]( v , len , i )" := (Psub AAscale w len v i)
  (in custom expr,
   v constr at level 0, w constr at level 0, len constr at level 0,
   i custom expr at level 99).

(* -------------------------------------------------------------------------- *)
(* Unary operators *)

Notation enot e := (Papp1 Onot e).
Notation eneg k e := (Papp1 (Oneg k) e).
Notation elnot w e := (Papp1 (Olnot w) e).

Notation "-i e" := (eneg Op_int e)
  (in custom expr at level 2, right associativity).
Notation "-8u e" := (eneg (Op_w U8) e)
  (in custom expr at level 2, right associativity).
Notation "-16u e" := (eneg (Op_w U16) e)
  (in custom expr at level 2, right associativity).
Notation "-32u e" := (eneg (Op_w U32) e)
  (in custom expr at level 2, right associativity).
Notation "-64u e" := (eneg (Op_w U64) e)
  (in custom expr at level 2, right associativity).
Notation "-128u e" := (eneg (Op_w U128) e)
  (in custom expr at level 2, right associativity).
Notation "-256u e" := (eneg (Op_w U256) e)
  (in custom expr at level 2, right associativity).

Notation "![b] e" := (enot e)
  (in custom expr at level 2, right associativity).
Notation "!8u e" := (elnot U8 e)
  (in custom expr at level 2, right associativity).
Notation "!16u e" := (elnot U16 e)
  (in custom expr at level 2, right associativity).
Notation "!32u e" := (elnot U32 e)
  (in custom expr at level 2, right associativity).
Notation "!64u e" := (elnot U64 e)
  (in custom expr at level 2, right associativity).
Notation "!128u e" := (elnot U128 e)
  (in custom expr at level 2, right associativity).
Notation "!256u e" := (elnot U256 e)
  (in custom expr at level 2, right associativity).

(* -------------------------------------------------------------------------- *)
(* Casts *)

Notation "i2w[ w ] e" := (Papp1 (Oword_of_int w) e)
  (in custom expr at level 2,
   w constr at level 0,
   right associativity,
   format "i2w[  w  ]  e").
Notation "u2i[ w ] e" := (Papp1 (Oint_of_word Unsigned w) e)
  (in custom expr at level 2,
   w constr at level 0,
   right associativity,
   format "u2i[  w  ]  e").
Notation "s2i[ w ] e" := (Papp1 (Oint_of_word Signed w) e)
  (in custom expr at level 2,
   w constr at level 0,
   right associativity,
   format "s2i[  w  ]  e").
Notation "zext[ szi , szo ] e" := (Papp1 (Ozeroext szo szi) e)
  (in custom expr at level 2,
   szi constr at level 0, szo constr at level 0,
   right associativity,
   format "zext[  szi ,  szo  ]  e").
Notation "sext[ szi , szo ] e" := (Papp1 (Osignext szo szi) e)
  (in custom expr at level 2,
   szi constr at level 0, szo constr at level 0,
   right associativity,
   format "sext[  szi ,  szo  ]  e").

(* -------------------------------------------------------------------------- *)
(* Binary arithmetic *)

Notation eadd k e1 e2 := (Papp2 (Oadd k) e1 e2).
Notation esub k e1 e2 := (Papp2 (Osub k) e1 e2).
Notation emul k e1 e2 := (Papp2 (Omul k) e1 e2).

Notation "e1 +i e2" := (eadd Op_int e1 e2)
  (in custom expr at level 6, left associativity).
Notation "e1 +8u e2" := (eadd (Op_w U8) e1 e2)
  (in custom expr at level 6, left associativity).
Notation "e1 +16u e2" := (eadd (Op_w U16) e1 e2)
  (in custom expr at level 6, left associativity).
Notation "e1 +32u e2" := (eadd (Op_w U32) e1 e2)
  (in custom expr at level 6, left associativity).
Notation "e1 +64u e2" := (eadd (Op_w U64) e1 e2)
  (in custom expr at level 6, left associativity).
Notation "e1 +128u e2" := (eadd (Op_w U128) e1 e2)
  (in custom expr at level 6, left associativity).
Notation "e1 +256u e2" := (eadd (Op_w U256) e1 e2)
  (in custom expr at level 6, left associativity).

Notation "e1 -i e2" := (esub Op_int e1 e2)
  (in custom expr at level 6, left associativity).
Notation "e1 -8u e2" := (esub (Op_w U8) e1 e2)
  (in custom expr at level 6, left associativity).
Notation "e1 -16u e2" := (esub (Op_w U16) e1 e2)
  (in custom expr at level 6, left associativity).
Notation "e1 -32u e2" := (esub (Op_w U32) e1 e2)
  (in custom expr at level 6, left associativity).
Notation "e1 -64u e2" := (esub (Op_w U64) e1 e2)
  (in custom expr at level 6, left associativity).
Notation "e1 -128u e2" := (esub (Op_w U128) e1 e2)
  (in custom expr at level 6, left associativity).
Notation "e1 -256u e2" := (esub (Op_w U256) e1 e2)
  (in custom expr at level 6, left associativity).

Notation "e1 *i e2" := (emul Op_int e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 *8u e2" := (emul (Op_w U8) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 *16u e2" := (emul (Op_w U16) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 *32u e2" := (emul (Op_w U32) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 *64u e2" := (emul (Op_w U64) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 *128u e2" := (emul (Op_w U128) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 *256u e2" := (emul (Op_w U256) e1 e2)
  (in custom expr at level 4, left associativity).

(* -------------------------------------------------------------------------- *)
(* Bitwise AND, XOR, OR *)

Notation eland w e1 e2 := (Papp2 (Oland w) e1 e2).
Notation elxor w e1 e2 := (Papp2 (Olxor w) e1 e2).
Notation elor w e1 e2 := (Papp2 (Olor w) e1 e2).

Notation "e1 &8u e2" := (eland U8 e1 e2)
  (in custom expr at level 7, left associativity).
Notation "e1 &16u e2" := (eland U16 e1 e2)
  (in custom expr at level 7, left associativity).
Notation "e1 &32u e2" := (eland U32 e1 e2)
  (in custom expr at level 7, left associativity).
Notation "e1 &64u e2" := (eland U64 e1 e2)
  (in custom expr at level 7, left associativity).
Notation "e1 &128u e2" := (eland U128 e1 e2)
  (in custom expr at level 7, left associativity).
Notation "e1 &256u e2" := (eland U256 e1 e2)
  (in custom expr at level 7, left associativity).

Notation "e1 ^8u e2" := (elxor U8 e1 e2)
  (in custom expr at level 8, left associativity).
Notation "e1 ^16u e2" := (elxor U16 e1 e2)
  (in custom expr at level 8, left associativity).
Notation "e1 ^32u e2" := (elxor U32 e1 e2)
  (in custom expr at level 8, left associativity).
Notation "e1 ^64u e2" := (elxor U64 e1 e2)
  (in custom expr at level 8, left associativity).
Notation "e1 ^128u e2" := (elxor U128 e1 e2)
  (in custom expr at level 8, left associativity).
Notation "e1 ^256u e2" := (elxor U256 e1 e2)
  (in custom expr at level 8, left associativity).

Notation "e1 |8u e2" := (elor U8 e1 e2)
  (in custom expr at level 9, left associativity).
Notation "e1 |16u e2" := (elor U16 e1 e2)
  (in custom expr at level 9, left associativity).
Notation "e1 |32u e2" := (elor U32 e1 e2)
  (in custom expr at level 9, left associativity).
Notation "e1 |64u e2" := (elor U64 e1 e2)
  (in custom expr at level 9, left associativity).
Notation "e1 |128u e2" := (elor U128 e1 e2)
  (in custom expr at level 9, left associativity).
Notation "e1 |256u e2" := (elor U256 e1 e2)
  (in custom expr at level 9, left associativity).

(* -------------------------------------------------------------------------- *)
(* Shifts and rotations *)

Notation elsl k e1 e2 := (Papp2 (Olsl k) e1 e2).
Notation elsr w e1 e2 := (Papp2 (Olsr w) e1 e2).
Notation easr k e1 e2 := (Papp2 (Oasr k) e1 e2).
Notation erol w e1 e2 := (Papp2 (Orol w) e1 e2).
Notation eror w e1 e2 := (Papp2 (Oror w) e1 e2).

Notation "e1 <<i e2" := (elsl Op_int e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 <<8u e2" := (elsl (Op_w U8) e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 <<16u e2" := (elsl (Op_w U16) e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 <<32u e2" := (elsl (Op_w U32) e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 <<64u e2" := (elsl (Op_w U64) e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 <<128u e2" := (elsl (Op_w U128) e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 <<256u e2" := (elsl (Op_w U256) e1 e2)
  (in custom expr at level 5, left associativity).

Notation "e1 >>8u e2" := (elsr U8 e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>16u e2" := (elsr U16 e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>32u e2" := (elsr U32 e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>64u e2" := (elsr U64 e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>128u e2" := (elsr U128 e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>256u e2" := (elsr U256 e1 e2)
  (in custom expr at level 5, left associativity).

Notation "e1 >>si e2" := (easr Op_int e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>s8u e2" := (easr (Op_w U8) e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>s16u e2" := (easr (Op_w U16) e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>s32u e2" := (easr (Op_w U32) e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>s64u e2" := (easr (Op_w U64) e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>s128u e2" := (easr (Op_w U128) e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>s256u e2" := (easr (Op_w U256) e1 e2)
  (in custom expr at level 5, left associativity).

Notation "e1 <<r8u e2" := (erol U8 e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 <<r16u e2" := (erol U16 e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 <<r32u e2" := (erol U32 e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 <<r64u e2" := (erol U64 e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 <<r128u e2" := (erol U128 e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 <<r256u e2" := (erol U256 e1 e2)
  (in custom expr at level 5, left associativity).

Notation "e1 >>r8u e2" := (eror U8 e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>r16u e2" := (eror U16 e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>r32u e2" := (eror U32 e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>r64u e2" := (eror U64 e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>r128u e2" := (eror U128 e1 e2)
  (in custom expr at level 5, left associativity).
Notation "e1 >>r256u e2" := (eror U256 e1 e2)
  (in custom expr at level 5, left associativity).

(* -------------------------------------------------------------------------- *)
(* Division and modulo *)

Notation ediv s k e1 e2 := (Papp2 (Odiv s k) e1 e2).
Notation emod s k e1 e2 := (Papp2 (Omod s k) e1 e2).

Notation "e1 /8u e2" := (ediv Unsigned (Op_w U8) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 /16u e2" := (ediv Unsigned (Op_w U16) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 /32u e2" := (ediv Unsigned (Op_w U32) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 /64u e2" := (ediv Unsigned (Op_w U64) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 /128u e2" := (ediv Unsigned (Op_w U128) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 /256u e2" := (ediv Unsigned (Op_w U256) e1 e2)
  (in custom expr at level 4, left associativity).

Notation "e1 /8s e2" := (ediv Signed (Op_w U8) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 /16s e2" := (ediv Signed (Op_w U16) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 /32s e2" := (ediv Signed (Op_w U32) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 /64s e2" := (ediv Signed (Op_w U64) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 /128s e2" := (ediv Signed (Op_w U128) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 /256s e2" := (ediv Signed (Op_w U256) e1 e2)
  (in custom expr at level 4, left associativity).

Notation "e1 %8u e2" := (emod Unsigned (Op_w U8) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 %16u e2" := (emod Unsigned (Op_w U16) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 %32u e2" := (emod Unsigned (Op_w U32) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 %64u e2" := (emod Unsigned (Op_w U64) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 %128u e2" := (emod Unsigned (Op_w U128) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 %256u e2" := (emod Unsigned (Op_w U256) e1 e2)
  (in custom expr at level 4, left associativity).

Notation "e1 %8s e2" := (emod Signed (Op_w U8) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 %16s e2" := (emod Signed (Op_w U16) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 %32s e2" := (emod Signed (Op_w U32) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 %64s e2" := (emod Signed (Op_w U64) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 %128s e2" := (emod Signed (Op_w U128) e1 e2)
  (in custom expr at level 4, left associativity).
Notation "e1 %256s e2" := (emod Signed (Op_w U256) e1 e2)
  (in custom expr at level 4, left associativity).

(* -------------------------------------------------------------------------- *)
(* Comparisons *)

Notation eeq k e1 e2 := (Papp2 (Oeq k) e1 e2).
Notation eneq k e1 e2 := (Papp2 (Oneq k) e1 e2).
Notation elt c e1 e2 := (Papp2 (Olt c) e1 e2).
Notation ele c e1 e2 := (Papp2 (Ole c) e1 e2).

Notation "e1 ==i e2" := (eeq Op_int e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 ==8u e2" := (eeq (Op_w U8) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 ==16u e2" := (eeq (Op_w U16) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 ==32u e2" := (eeq (Op_w U32) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 ==64u e2" := (eeq (Op_w U64) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 ==128u e2" := (eeq (Op_w U128) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 ==256u e2" := (eeq (Op_w U256) e1 e2)
  (in custom expr at level 10, no associativity).

Notation "e1 !=i e2" := (eneq Op_int e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 !=8u e2" := (eneq (Op_w U8) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 !=16u e2" := (eneq (Op_w U16) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 !=32u e2" := (eneq (Op_w U32) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 !=64u e2" := (eneq (Op_w U64) e1 e2)
  (in custom expr at level 10, no associativity).

Notation "e1 <i e2" := (elt Cmp_int e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <8u e2" := (elt (Cmp_w Unsigned U8) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <16u e2" := (elt (Cmp_w Unsigned U16) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <32u e2" := (elt (Cmp_w Unsigned U32) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <64u e2" := (elt (Cmp_w Unsigned U64) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <128u e2" := (elt (Cmp_w Unsigned U128) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <256u e2" := (elt (Cmp_w Unsigned U256) e1 e2)
  (in custom expr at level 10, no associativity).

Notation "e1 <8s e2" := (elt (Cmp_w Signed U8) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <16s e2" := (elt (Cmp_w Signed U16) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <32s e2" := (elt (Cmp_w Signed U32) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <64s e2" := (elt (Cmp_w Signed U64) e1 e2)
  (in custom expr at level 10, no associativity).

Notation "e1 <=i e2" := (ele Cmp_int e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <=8u e2" := (ele (Cmp_w Unsigned U8) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <=16u e2" := (ele (Cmp_w Unsigned U16) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <=32u e2" := (ele (Cmp_w Unsigned U32) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <=64u e2" := (ele (Cmp_w Unsigned U64) e1 e2)
  (in custom expr at level 10, no associativity).

Notation "e1 <=8s e2" := (ele (Cmp_w Signed U8) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <=16s e2" := (ele (Cmp_w Signed U16) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <=32s e2" := (ele (Cmp_w Signed U32) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 <=64s e2" := (ele (Cmp_w Signed U64) e1 e2)
  (in custom expr at level 10, no associativity).

Notation egt c e1 e2 := (Papp2 (Ogt c) e1 e2).
Notation ege c e1 e2 := (Papp2 (Oge c) e1 e2).

Notation "e1 >i e2" := (egt Cmp_int e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >8u e2" := (egt (Cmp_w Unsigned U8) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >16u e2" := (egt (Cmp_w Unsigned U16) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >32u e2" := (egt (Cmp_w Unsigned U32) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >64u e2" := (egt (Cmp_w Unsigned U64) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >128u e2" := (egt (Cmp_w Unsigned U128) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >256u e2" := (egt (Cmp_w Unsigned U256) e1 e2)
  (in custom expr at level 10, no associativity).

Notation "e1 >8s e2" := (egt (Cmp_w Signed U8) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >16s e2" := (egt (Cmp_w Signed U16) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >32s e2" := (egt (Cmp_w Signed U32) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >64s e2" := (egt (Cmp_w Signed U64) e1 e2)
  (in custom expr at level 10, no associativity).

Notation "e1 >=i e2" := (ege Cmp_int e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >=8u e2" := (ege (Cmp_w Unsigned U8) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >=16u e2" := (ege (Cmp_w Unsigned U16) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >=32u e2" := (ege (Cmp_w Unsigned U32) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >=64u e2" := (ege (Cmp_w Unsigned U64) e1 e2)
  (in custom expr at level 10, no associativity).

Notation "e1 >=8s e2" := (ege (Cmp_w Signed U8) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >=16s e2" := (ege (Cmp_w Signed U16) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >=32s e2" := (ege (Cmp_w Signed U32) e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 >=64s e2" := (ege (Cmp_w Signed U64) e1 e2)
  (in custom expr at level 10, no associativity).

(* -------------------------------------------------------------------------- *)
(* Boolean operators *)

Notation "e1 == e2" := (Papp2 Obeq e1 e2)
  (in custom expr at level 10, no associativity).
Notation "e1 && e2" := (Papp2 Oand e1 e2)
  (in custom expr at level 11, left associativity).
Notation "e1 || e2" := (Papp2 Oor e1 e2)
  (in custom expr at level 12, left associativity).

(* -------------------------------------------------------------------------- *)
(* Conditional expression *)

(* Double spaces to force printing one space. *)
Notation "e1  ?[b]  e2  :  e3" := (Pif abool e1 e2 e3)
  (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13).
Notation "e1  ?[i]  e2  :  e3" := (Pif aint e1 e2 e3)
  (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13).
Notation "e1  ?8u  e2  :  e3" := (Pif (aword U8) e1 e2 e3)
  (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13).
Notation "e1  ?16u  e2  :  e3" := (Pif (aword U16) e1 e2 e3)
  (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13).
Notation "e1  ?32u  e2  :  e3" := (Pif (aword U32) e1 e2 e3)
  (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13).
Notation "e1  ?64u  e2  :  e3" := (Pif (aword U64) e1 e2 e3)
  (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13).
Notation "e1  ?128u  e2  :  e3" := (Pif (aword U128) e1 e2 e3)
  (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13).
Notation "e1  ?256u  e2  :  e3" := (Pif (aword U256) e1 e2 e3)
  (in custom expr at level 13, e2 custom expr, e3 custom expr at level 13).

Section ExprTests.

Context (x y z b : gvar).

Goal expr:( ld[U64](x) ) = Pload Unaligned U64 (Pvar x). done. Qed.

Goal expr:( aget[U64](x, #0) ) =
  Pget Aligned AAscale U64 x (Pconst 0). done. Qed.

Goal expr:( -i #5 ) = Papp1 (Oneg Op_int) (Pconst 5). done. Qed.
Goal expr:( -64u x ) = Papp1 (Oneg (Op_w U64)) (Pvar x). done. Qed.
Goal expr:( ![b] b ) = Papp1 Onot (Pvar b). done. Qed.
Goal expr:( !64u x ) = Papp1 (Olnot U64) (Pvar x). done. Qed.
Goal expr:( i2w[U8] #42 ) =
  Papp1 (Oword_of_int U8) (Pconst 42). done. Qed.
Goal expr:( i2w[U64] #0 ) =
  Papp1 (Oword_of_int U64) (Pconst 0). done. Qed.

Goal expr:( #3 +i #7 ) =
  Papp2 (Oadd Op_int) (Pconst 3) (Pconst 7). done. Qed.
Goal expr:( x +64u y ) =
  Papp2 (Oadd (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal expr:( z *64u x +64u #3 ) =
  Papp2 (Oadd (Op_w U64))
    (Papp2 (Omul (Op_w U64)) (Pvar z) (Pvar x)) (Pconst 3).
done. Qed.
Goal expr:( #5 -i #2 ) =
  Papp2 (Osub Op_int) (Pconst 5) (Pconst 2). done. Qed.
Goal expr:( x -64u y ) =
  Papp2 (Osub (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal expr:( #2 *i #3 ) =
  Papp2 (Omul Op_int) (Pconst 2) (Pconst 3). done. Qed.
Goal expr:( x &64u y ) = Papp2 (Oland U64) (Pvar x) (Pvar y). done. Qed.
Goal expr:( x ^64u y ) = Papp2 (Olxor U64) (Pvar x) (Pvar y). done. Qed.
Goal expr:( x |64u y ) = Papp2 (Olor U64) (Pvar x) (Pvar y). done. Qed.
Goal expr:( #1 <<i #3 ) =
  Papp2 (Olsl Op_int) (Pconst 1) (Pconst 3). done. Qed.
Goal expr:( y <<64u y ) =
  Papp2 (Olsl (Op_w U64)) (Pvar y) (Pvar y). done. Qed.
Goal expr:( y >>64u y ) = Papp2 (Olsr U64) (Pvar y) (Pvar y). done. Qed.
Goal expr:( #8 >>si #1 ) =
  Papp2 (Oasr Op_int) (Pconst 8) (Pconst 1). done. Qed.
Goal expr:( x >>s64u y ) =
  Papp2 (Oasr (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal expr:( x <<r64u y ) = Papp2 (Orol U64) (Pvar x) (Pvar y). done. Qed.
Goal expr:( x >>r64u y ) = Papp2 (Oror U64) (Pvar x) (Pvar y). done. Qed.
Goal expr:( x /64u y ) =
  Papp2 (Odiv Unsigned (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal expr:( x /64s y ) =
  Papp2 (Odiv Signed (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal expr:( x %64u y ) =
  Papp2 (Omod Unsigned (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal expr:( x %64s y ) =
  Papp2 (Omod Signed (Op_w U64)) (Pvar x) (Pvar y). done. Qed.

Goal expr:( x ==64u y ) =
  Papp2 (Oeq (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal expr:( #3 !=i #4 ) =
  Papp2 (Oneq Op_int) (Pconst 3) (Pconst 4). done. Qed.
Goal expr:( #1 <i #2 ) =
  Papp2 (Olt Cmp_int) (Pconst 1) (Pconst 2). done. Qed.
Goal expr:( x <64s y ) =
  Papp2 (Olt (Cmp_w Signed U64)) (Pvar x) (Pvar y). done. Qed.
Goal expr:( #1 <=i #2 ) =
  Papp2 (Ole Cmp_int) (Pconst 1) (Pconst 2). done. Qed.
Goal expr:( x <=64s y ) =
  Papp2 (Ole (Cmp_w Signed U64)) (Pvar x) (Pvar y). done. Qed.
Goal expr:( b == b ) = Papp2 Obeq (Pvar b) (Pvar b). done. Qed.

Goal expr:( b ?[b] x : y ) =
  Pif abool (Pvar b) (Pvar x) (Pvar y). done. Qed.
Goal expr:( b ?[i] x : y ) =
  Pif aint (Pvar b) (Pvar x) (Pvar y). done. Qed.
Goal expr:( true ?32u x &32u y : z ) =
  Pif (aword U32) (Pbool true)
    (Papp2 (Oland U32) (Pvar x) (Pvar y)) (Pvar z).
done. Qed.
Goal expr:( b ?64u x : y ) =
  Pif (aword U64) (Pvar b) (Pvar x) (Pvar y). done. Qed.

Goal expr:( b && x <=64u y ) =
  Papp2 Oand (Pvar b)
    (Papp2 (Ole (Cmp_w Unsigned U64)) (Pvar x) (Pvar y)).
done. Qed.
Goal expr:( x !=64u y || x <64u y ) =
  Papp2 Oor
    (Papp2 (Oneq (Op_w U64)) (Pvar x) (Pvar y))
    (Papp2 (Olt (Cmp_w Unsigned U64)) (Pvar x) (Pvar y)).
done. Qed.
Goal expr:( true || false && (#1 -i #10) ==i false ) =
  Papp2 Oor (Pbool true)
    (Papp2 Oand (Pbool false)
      (Papp2 (Oeq Op_int)
        (Papp2 (Osub Op_int) (Pconst 1) (Pconst 10))
        (Pbool false))).
done. Qed.

Goal expr:( u2i[U8] x ) =
  Papp1 (Oint_of_word Unsigned U8) (Pvar x). done. Qed.
Goal expr:( u2i[U64] x ) =
  Papp1 (Oint_of_word Unsigned U64) (Pvar x). done. Qed.
Goal expr:( s2i[U8] x ) =
  Papp1 (Oint_of_word Signed U8) (Pvar x). done. Qed.
Goal expr:( s2i[U64] x ) =
  Papp1 (Oint_of_word Signed U64) (Pvar x). done. Qed.

Goal expr:( zext[U8, U16] x ) =
  Papp1 (Ozeroext U16 U8) (Pvar x). done. Qed.
Goal expr:( zext[U32, U64] x ) =
  Papp1 (Ozeroext U64 U32) (Pvar x). done. Qed.
Goal expr:( zext[U128, U256] x ) =
  Papp1 (Ozeroext U256 U128) (Pvar x). done. Qed.

Goal expr:( sext[U8, U16] x ) =
  Papp1 (Osignext U16 U8) (Pvar x). done. Qed.
Goal expr:( sext[U32, U64] x ) =
  Papp1 (Osignext U64 U32) (Pvar x). done. Qed.
Goal expr:( sext[U128, U256] x ) =
  Papp1 (Osignext U256 U128) (Pvar x). done. Qed.

Goal expr:( x *128u y ) =
  Papp2 (Omul (Op_w U128)) (Pvar x) (Pvar y). done. Qed.
Goal expr:( x *256u y ) =
  Papp2 (Omul (Op_w U256)) (Pvar x) (Pvar y). done. Qed.

Goal expr:( asub[U64](x, 4, #0) ) =
  Psub AAscale U64 4 x (Pconst 0). done. Qed.

Goal expr:( x >i y ) =
  Papp2 (Ogt Cmp_int) (Pvar x) (Pvar y). done. Qed.
Goal expr:( x >64u y ) =
  Papp2 (Ogt (Cmp_w Unsigned U64)) (Pvar x) (Pvar y). done. Qed.
Goal expr:( x >64s y ) =
  Papp2 (Ogt (Cmp_w Signed U64)) (Pvar x) (Pvar y). done. Qed.
Goal expr:( x >=i y ) =
  Papp2 (Oge Cmp_int) (Pvar x) (Pvar y). done. Qed.
Goal expr:( x >=64u y ) =
  Papp2 (Oge (Cmp_w Unsigned U64)) (Pvar x) (Pvar y). done. Qed.
Goal expr:( x >=64s y ) =
  Papp2 (Oge (Cmp_w Signed U64)) (Pvar x) (Pvar y). done. Qed.

Goal expr:( ld[U8](x) ) = Pload Unaligned U8 (Pvar x). done. Qed.
Goal expr:( ld[U16](x)) = Pload Unaligned U16 (Pvar x). done. Qed.
Goal expr:( ld[U32](x) ) = Pload Unaligned U32 (Pvar x). done. Qed.
Goal expr:( ld[U128](x) ) = Pload Unaligned U128 (Pvar x). done. Qed.
Goal expr:( ld[U256](x) ) = Pload Unaligned U256 (Pvar x). done. Qed.
Goal expr:( ld[U64](x +64u y) ) =
  Pload Unaligned U64
    (Papp2 (Oadd (Op_w U64)) (Pvar x) (Pvar y)).
done. Qed.

Goal expr:( aget[U8](x, #0) ) =
  Pget Aligned AAscale U8 x (Pconst 0). done. Qed.
Goal expr:( aget[U32](x, #0) ) =
  Pget Aligned AAscale U32 x (Pconst 0). done. Qed.
Goal expr:( aget[U64](x, y) ) =
  Pget Aligned AAscale U64 x (Pvar y). done. Qed.
Goal expr:( aget[U64](x, y +64u #1) ) =
  Pget Aligned AAscale U64 x
    (Papp2 (Oadd (Op_w U64)) (Pvar y) (Pconst 1)).
done. Qed.

End ExprTests.
