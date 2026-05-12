Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Stdlib Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr.

Declare Scope jexpr_scope.
Delimit Scope jexpr_scope with E.
Bind Scope jexpr_scope with pexpr.

Definition pexpr_of_Z (z : Z) : pexpr := Pconst z.
Definition Z_of_pexpr (e : pexpr) : option Z :=
  match e with Pconst z => Some z | _ => None end.
Number Notation pexpr pexpr_of_Z Z_of_pexpr : jexpr_scope.

(* TODO:
   1. create notation for [atype] as [t ::= b | i | ws]. Then change [ite[b]] to
   [ite[ t ]], etc. Change all notations that have one entry per type/size to
   take a `wsize` between square brackets.
   2. Add a format string to every notation to ensure proper spacing. Try to
   avoid spurious spaces (e.g., inside [(...)], and otherwise give symmetrical
   spacing (e.g., in [ite[ U8 ]].
   4. Replace [==e] and [!=e] with [==b] and [!=b].
   5. Reorder notation blocks in the order in which their constructors are
   defined in [pexpr].
   3. Add a docstring at the top of the file with every notation explained. Give
   an exhaustive list of all the cases that are not supported by notations.
   Here's the previous one as inspiration (needs updating):

(** * Display notations for Jasmin expressions
-
-    Wrap a [pexpr] in [expr:( e )] to view it in Jasmin-like syntax.
-    Example:
-      Check expr:( x +64u y *64u z ).
-
-    Operator naming convention:
-      - size suffix: 8u / 16u / 32u / 64u / 128u / 256u = word size + unsigned
-      - signed suffix: 8s / 16s / 32s / 64s
-      - integer (mathematical int) suffix: i
-      - mem[w](e) = unaligned load of word size w from address e (address must be
-                   an atom or parenthesised expression)
-      - aget[w](v, e) = aligned array read of word size w at index e
-      - asub[w](v, len, e) = aligned array sub-slice of word size w
-      - i2w[N]   = int -> word of size N
-      - u2i[N]   = word N -> unsigned int
-      - s2i[N]   = word N -> signed int
-      - zext[M, N] = zero-extend from M to N
-      - sext[M, N] = sign-extend from M to N
-      - wu = unsigned wint (bounded unsigned integer of word size N)
-      - ws = signed wint
-        i2wu[N] / i2ws[N]      = int -> unsigned/signed wint N
-        wu2i[N] / ws2i[N]      = unsigned/signed wint N -> int
-        wu2w[N] / ws2w[N]      = unsigned/signed wint N -> word N
-        w2wu[N] / w2ws[N]      = word N -> unsigned/signed wint N
-        wuext[M,N] / wsext[M,N] = unsigned/signed wint extension M to N
-        -wu[N]  / -ws[N]       = unsigned/signed wint negation
-      - wint binary: e1 OP wu[N] e2 / e1 OP ws[N] e2 (Owi2):
-        +wu[N] / +ws[N]   = addition       (level 6, left)
-        -wu[N] / -ws[N]   = subtraction    (level 6, left)
-        *wu[N] / *ws[N]   = multiplication (level 4, left)
-        /wu[N] / /ws[N]   = division       (level 4, left)
-        %wu[N] / %ws[N]   = modulo         (level 4, left)
-        <<wu[N] / <<ws[N] = shift left     (level 5, left)
-        >>wu[N] / >>ws[N] = shift right    (level 5, left)
-        ==wu[N] / ==ws[N] = equality       (level 10, none)
-        !=wu[N] / !=ws[N] = inequality     (level 10, none)
-        <wu[N]  / <ws[N]  = less-than      (level 10, none)
-        <=wu[N] / <=ws[N] = less-or-equal  (level 10, none)
-        >wu[N]  / >ws[N]  = greater-than   (level 10, none)
-        >=wu[N] / >=ws[N] = greater-or-equal (level 10, none)
-
-    Not supported:
-      - [Parr_init n]          : array initialisation expression
-      - [PappN o es]           : [Opack], [Oarray], [Ocombine_flags],
-                                 [Ois_arr_init], [Ois_barr_init]
-      - [Pload Aligned w e]    : aligned load ([Pload Unaligned] is covered)
-      - [Pget] or [Psub] with alignment other than [Aligned] or
-        scale other than [AAscale]
-      - [op2] vector operations: [Ovadd], [Ovsub], [Ovmul],
-        [Ovlsr], [Ovlsl], [Ovasr]
*)*)

(* ------------------------------------------------------------------ *)
(* Conditional expression *)

Notation "ite[b]( e1 , e2 , e3 )" := (Pif abool e1 e2 e3)
  (at level 0, e1 at level 99, e2 at level 99, e3 at level 99)
  : jexpr_scope.
Notation "ite[i]( e1 , e2 , e3 )" := (Pif aint e1 e2 e3)
  (at level 0, e1 at level 99, e2 at level 99, e3 at level 99)
  : jexpr_scope.
Notation "ite[8u]( e1 , e2 , e3 )" := (Pif (aword U8) e1 e2 e3)
  (at level 0, e1 at level 99, e2 at level 99, e3 at level 99)
  : jexpr_scope.
Notation "ite[16u]( e1 , e2 , e3 )" := (Pif (aword U16) e1 e2 e3)
  (at level 0, e1 at level 99, e2 at level 99, e3 at level 99)
  : jexpr_scope.
Notation "ite[32u]( e1 , e2 , e3 )" := (Pif (aword U32) e1 e2 e3)
  (at level 0, e1 at level 99, e2 at level 99, e3 at level 99)
  : jexpr_scope.
Notation "ite[64u]( e1 , e2 , e3 )" := (Pif (aword U64) e1 e2 e3)
  (at level 0, e1 at level 99, e2 at level 99, e3 at level 99)
  : jexpr_scope.
Notation "ite[128u]( e1 , e2 , e3 )" := (Pif (aword U128) e1 e2 e3)
  (at level 0, e1 at level 99, e2 at level 99, e3 at level 99)
  : jexpr_scope.
Notation "ite[256u]( e1 , e2 , e3 )" := (Pif (aword U256) e1 e2 e3)
  (at level 0, e1 at level 99, e2 at level 99, e3 at level 99)
  : jexpr_scope.

(* ------------------------------------------------------------------ *)
(* Memory load *)

Notation "mem[ w ]( e )" := (Pload Unaligned w e)
  (at level 0, w constr at level 0, e at level 99) : jexpr_scope.

(* ------------------------------------------------------------------ *)
(* Array subscript *)

Notation "aget[ w ]( v , i )" := (Pget Aligned AAscale w v i)
  (at level 0, w constr at level 0, v constr at level 0,
   i at level 99) : jexpr_scope.

(* ------------------------------------------------------------------ *)
(* Array sub-slice *)

Notation "asub[ w ]( v , len , i )" := (Psub AAscale w len v i)
  (at level 0, w constr at level 0, v constr at level 0,
   len constr at level 0, i at level 99) : jexpr_scope.

(* ------------------------------------------------------------------ *)
(* Unary operators (level 30, right assoc) *)

Notation "-i e" := (Papp1 (Oneg Op_int) e)
  (at level 30, right associativity) : jexpr_scope.
Notation "-8u e" := (Papp1 (Oneg (Op_w U8)) e)
  (at level 30, right associativity) : jexpr_scope.
Notation "-16u e" := (Papp1 (Oneg (Op_w U16)) e)
  (at level 30, right associativity) : jexpr_scope.
Notation "-32u e" := (Papp1 (Oneg (Op_w U32)) e)
  (at level 30, right associativity) : jexpr_scope.
Notation "-64u e" := (Papp1 (Oneg (Op_w U64)) e)
  (at level 30, right associativity) : jexpr_scope.
Notation "-128u e" := (Papp1 (Oneg (Op_w U128)) e)
  (at level 30, right associativity) : jexpr_scope.
Notation "-256u e" := (Papp1 (Oneg (Op_w U256)) e)
  (at level 30, right associativity) : jexpr_scope.

Notation "![b] e" := (Papp1 Onot e)
  (at level 30, right associativity) : jexpr_scope.
Notation "!8u e" := (Papp1 (Olnot U8) e)
  (at level 30, right associativity) : jexpr_scope.
Notation "!16u e" := (Papp1 (Olnot U16) e)
  (at level 30, right associativity) : jexpr_scope.
Notation "!32u e" := (Papp1 (Olnot U32) e)
  (at level 30, right associativity) : jexpr_scope.
Notation "!64u e" := (Papp1 (Olnot U64) e)
  (at level 30, right associativity) : jexpr_scope.
Notation "!128u e" := (Papp1 (Olnot U128) e)
  (at level 30, right associativity) : jexpr_scope.
Notation "!256u e" := (Papp1 (Olnot U256) e)
  (at level 30, right associativity) : jexpr_scope.

(* Casts *)
Notation "i2w[ w ] e" := (Papp1 (Oword_of_int w) e)
  (at level 30, w constr at level 0,
   right associativity) : jexpr_scope.
Notation "u2i[ w ] e" := (Papp1 (Oint_of_word Unsigned w) e)
  (at level 30, w constr at level 0,
   right associativity) : jexpr_scope.
Notation "s2i[ w ] e" := (Papp1 (Oint_of_word Signed w) e)
  (at level 30, w constr at level 0,
   right associativity) : jexpr_scope.
Notation "zext[ szi , szo ] e" := (Papp1 (Ozeroext szo szi) e)
  (at level 30, szi constr at level 0, szo constr at level 0,
   right associativity) : jexpr_scope.
Notation "sext[ szi , szo ] e" := (Papp1 (Osignext szo szi) e)
  (at level 30, szi constr at level 0, szo constr at level 0,
   right associativity) : jexpr_scope.

(* Wint unary *)
Notation "i2wu[ w ] e" := (Papp1 (Owi1 Unsigned (WIwint_of_int w)) e)
  (at level 30, w constr at level 0,
   right associativity) : jexpr_scope.
Notation "i2ws[ w ] e" := (Papp1 (Owi1 Signed (WIwint_of_int w)) e)
  (at level 30, w constr at level 0,
   right associativity) : jexpr_scope.
Notation "wu2i[ w ] e" := (Papp1 (Owi1 Unsigned (WIint_of_wint w)) e)
  (at level 30, w constr at level 0,
   right associativity) : jexpr_scope.
Notation "ws2i[ w ] e" := (Papp1 (Owi1 Signed (WIint_of_wint w)) e)
  (at level 30, w constr at level 0,
   right associativity) : jexpr_scope.
Notation "wu2w[ w ] e" := (Papp1 (Owi1 Unsigned (WIword_of_wint w)) e)
  (at level 30, w constr at level 0,
   right associativity) : jexpr_scope.
Notation "ws2w[ w ] e" := (Papp1 (Owi1 Signed (WIword_of_wint w)) e)
  (at level 30, w constr at level 0,
   right associativity) : jexpr_scope.
Notation "w2wu[ w ] e" := (Papp1 (Owi1 Unsigned (WIwint_of_word w)) e)
  (at level 30, w constr at level 0,
   right associativity) : jexpr_scope.
Notation "w2ws[ w ] e" := (Papp1 (Owi1 Signed (WIwint_of_word w)) e)
  (at level 30, w constr at level 0,
   right associativity) : jexpr_scope.
Notation "wuext[ szi , szo ] e" :=
  (Papp1 (Owi1 Unsigned (WIwint_ext szo szi)) e)
  (at level 30, szi constr at level 0, szo constr at level 0,
   right associativity) : jexpr_scope.
Notation "wsext[ szi , szo ] e" :=
  (Papp1 (Owi1 Signed (WIwint_ext szo szi)) e)
  (at level 30, szi constr at level 0, szo constr at level 0,
   right associativity) : jexpr_scope.
Notation "-wu[ w ] e" := (Papp1 (Owi1 Unsigned (WIneg w)) e)
  (at level 30, w constr at level 0,
   right associativity) : jexpr_scope.
Notation "-ws[ w ] e" := (Papp1 (Owi1 Signed (WIneg w)) e)
  (at level 30, w constr at level 0,
   right associativity) : jexpr_scope.

(* ------------------------------------------------------------------ *)
(* Multiplication / Division / Modulo (level 40, left) *)

Notation "e1 *i e2" := (Papp2 (Omul Op_int) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 *8u e2" := (Papp2 (Omul (Op_w U8)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 *16u e2" := (Papp2 (Omul (Op_w U16)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 *32u e2" := (Papp2 (Omul (Op_w U32)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 *64u e2" := (Papp2 (Omul (Op_w U64)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 *128u e2" := (Papp2 (Omul (Op_w U128)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 *256u e2" := (Papp2 (Omul (Op_w U256)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.

Notation "e1 /8u e2" := (Papp2 (Odiv Unsigned (Op_w U8)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 /16u e2" := (Papp2 (Odiv Unsigned (Op_w U16)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 /32u e2" := (Papp2 (Odiv Unsigned (Op_w U32)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 /64u e2" := (Papp2 (Odiv Unsigned (Op_w U64)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 /128u e2" := (Papp2 (Odiv Unsigned (Op_w U128)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 /256u e2" := (Papp2 (Odiv Unsigned (Op_w U256)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 /8s e2" := (Papp2 (Odiv Signed (Op_w U8)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 /16s e2" := (Papp2 (Odiv Signed (Op_w U16)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 /32s e2" := (Papp2 (Odiv Signed (Op_w U32)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 /64s e2" := (Papp2 (Odiv Signed (Op_w U64)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 /128s e2" := (Papp2 (Odiv Signed (Op_w U128)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 /256s e2" := (Papp2 (Odiv Signed (Op_w U256)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.

Notation "e1 %8u e2" := (Papp2 (Omod Unsigned (Op_w U8)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 %16u e2" := (Papp2 (Omod Unsigned (Op_w U16)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 %32u e2" := (Papp2 (Omod Unsigned (Op_w U32)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 %64u e2" := (Papp2 (Omod Unsigned (Op_w U64)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 %128u e2" := (Papp2 (Omod Unsigned (Op_w U128)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 %256u e2" := (Papp2 (Omod Unsigned (Op_w U256)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 %8s e2" := (Papp2 (Omod Signed (Op_w U8)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 %16s e2" := (Papp2 (Omod Signed (Op_w U16)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 %32s e2" := (Papp2 (Omod Signed (Op_w U32)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 %64s e2" := (Papp2 (Omod Signed (Op_w U64)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 %128s e2" := (Papp2 (Omod Signed (Op_w U128)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.
Notation "e1 %256s e2" := (Papp2 (Omod Signed (Op_w U256)) e1 e2)
  (at level 40, left associativity) : jexpr_scope.

(* Wint mult/div/mod (level 40) *)
Notation "e1 *wu[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WImul) e1 e2)
  (at level 40, left associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 *ws[ sz ] e2" := (Papp2 (Owi2 Signed sz WImul) e1 e2)
  (at level 40, left associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 /wu[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIdiv) e1 e2)
  (at level 40, left associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 /ws[ sz ] e2" := (Papp2 (Owi2 Signed sz WIdiv) e1 e2)
  (at level 40, left associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 %wu[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WImod) e1 e2)
  (at level 40, left associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 %ws[ sz ] e2" := (Papp2 (Owi2 Signed sz WImod) e1 e2)
  (at level 40, left associativity, sz constr at level 0) : jexpr_scope.

(* ------------------------------------------------------------------ *)
(* Shifts / Rotations (level 45, left) *)

Notation "e1 <<i e2" := (Papp2 (Olsl Op_int) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 <<8u e2" := (Papp2 (Olsl (Op_w U8)) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 <<16u e2" := (Papp2 (Olsl (Op_w U16)) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 <<32u e2" := (Papp2 (Olsl (Op_w U32)) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 <<64u e2" := (Papp2 (Olsl (Op_w U64)) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 <<128u e2" := (Papp2 (Olsl (Op_w U128)) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 <<256u e2" := (Papp2 (Olsl (Op_w U256)) e1 e2)
  (at level 45, left associativity) : jexpr_scope.

Notation "e1 >>8u e2" := (Papp2 (Olsr U8) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>16u e2" := (Papp2 (Olsr U16) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>32u e2" := (Papp2 (Olsr U32) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>64u e2" := (Papp2 (Olsr U64) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>128u e2" := (Papp2 (Olsr U128) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>256u e2" := (Papp2 (Olsr U256) e1 e2)
  (at level 45, left associativity) : jexpr_scope.

Notation "e1 >>si e2" := (Papp2 (Oasr Op_int) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>s8u e2" := (Papp2 (Oasr (Op_w U8)) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>s16u e2" := (Papp2 (Oasr (Op_w U16)) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>s32u e2" := (Papp2 (Oasr (Op_w U32)) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>s64u e2" := (Papp2 (Oasr (Op_w U64)) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>s128u e2" := (Papp2 (Oasr (Op_w U128)) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>s256u e2" := (Papp2 (Oasr (Op_w U256)) e1 e2)
  (at level 45, left associativity) : jexpr_scope.

Notation "e1 <<r8u e2" := (Papp2 (Orol U8) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 <<r16u e2" := (Papp2 (Orol U16) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 <<r32u e2" := (Papp2 (Orol U32) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 <<r64u e2" := (Papp2 (Orol U64) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 <<r128u e2" := (Papp2 (Orol U128) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 <<r256u e2" := (Papp2 (Orol U256) e1 e2)
  (at level 45, left associativity) : jexpr_scope.

Notation "e1 >>r8u e2" := (Papp2 (Oror U8) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>r16u e2" := (Papp2 (Oror U16) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>r32u e2" := (Papp2 (Oror U32) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>r64u e2" := (Papp2 (Oror U64) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>r128u e2" := (Papp2 (Oror U128) e1 e2)
  (at level 45, left associativity) : jexpr_scope.
Notation "e1 >>r256u e2" := (Papp2 (Oror U256) e1 e2)
  (at level 45, left associativity) : jexpr_scope.

(* Wint shifts (level 45) *)
Notation "e1 <<wu[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIshl) e1 e2)
  (at level 45, left associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 <<ws[ sz ] e2" := (Papp2 (Owi2 Signed sz WIshl) e1 e2)
  (at level 45, left associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 >>wu[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIshr) e1 e2)
  (at level 45, left associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 >>ws[ sz ] e2" := (Papp2 (Owi2 Signed sz WIshr) e1 e2)
  (at level 45, left associativity, sz constr at level 0) : jexpr_scope.

(* ------------------------------------------------------------------ *)
(* Addition / Subtraction (level 50, left) *)

Notation "e1 +i e2" := (Papp2 (Oadd Op_int) e1 e2)
  (at level 50, left associativity) : jexpr_scope.
Notation "e1 +8u e2" := (Papp2 (Oadd (Op_w U8)) e1 e2)
  (at level 50, left associativity) : jexpr_scope.
Notation "e1 +16u e2" := (Papp2 (Oadd (Op_w U16)) e1 e2)
  (at level 50, left associativity) : jexpr_scope.
Notation "e1 +32u e2" := (Papp2 (Oadd (Op_w U32)) e1 e2)
  (at level 50, left associativity) : jexpr_scope.
Notation "e1 +64u e2" := (Papp2 (Oadd (Op_w U64)) e1 e2)
  (at level 50, left associativity) : jexpr_scope.
Notation "e1 +128u e2" := (Papp2 (Oadd (Op_w U128)) e1 e2)
  (at level 50, left associativity) : jexpr_scope.
Notation "e1 +256u e2" := (Papp2 (Oadd (Op_w U256)) e1 e2)
  (at level 50, left associativity) : jexpr_scope.

Notation "e1 -i e2" := (Papp2 (Osub Op_int) e1 e2)
  (at level 50, left associativity) : jexpr_scope.
Notation "e1 -8u e2" := (Papp2 (Osub (Op_w U8)) e1 e2)
  (at level 50, left associativity) : jexpr_scope.
Notation "e1 -16u e2" := (Papp2 (Osub (Op_w U16)) e1 e2)
  (at level 50, left associativity) : jexpr_scope.
Notation "e1 -32u e2" := (Papp2 (Osub (Op_w U32)) e1 e2)
  (at level 50, left associativity) : jexpr_scope.
Notation "e1 -64u e2" := (Papp2 (Osub (Op_w U64)) e1 e2)
  (at level 50, left associativity) : jexpr_scope.
Notation "e1 -128u e2" := (Papp2 (Osub (Op_w U128)) e1 e2)
  (at level 50, left associativity) : jexpr_scope.
Notation "e1 -256u e2" := (Papp2 (Osub (Op_w U256)) e1 e2)
  (at level 50, left associativity) : jexpr_scope.

(* Wint add/sub (level 50) *)
Notation "e1 +wu[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIadd) e1 e2)
  (at level 50, left associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 +ws[ sz ] e2" := (Papp2 (Owi2 Signed sz WIadd) e1 e2)
  (at level 50, left associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 -wu[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIsub) e1 e2)
  (at level 50, left associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 -ws[ sz ] e2" := (Papp2 (Owi2 Signed sz WIsub) e1 e2)
  (at level 50, left associativity, sz constr at level 0) : jexpr_scope.

(* ------------------------------------------------------------------ *)
(* Bitwise AND (level 54, left) *)

Notation "e1 &8u e2" := (Papp2 (Oland U8) e1 e2)
  (at level 54, left associativity) : jexpr_scope.
Notation "e1 &16u e2" := (Papp2 (Oland U16) e1 e2)
  (at level 54, left associativity) : jexpr_scope.
Notation "e1 &32u e2" := (Papp2 (Oland U32) e1 e2)
  (at level 54, left associativity) : jexpr_scope.
Notation "e1 &64u e2" := (Papp2 (Oland U64) e1 e2)
  (at level 54, left associativity) : jexpr_scope.
Notation "e1 &128u e2" := (Papp2 (Oland U128) e1 e2)
  (at level 54, left associativity) : jexpr_scope.
Notation "e1 &256u e2" := (Papp2 (Oland U256) e1 e2)
  (at level 54, left associativity) : jexpr_scope.

(* ------------------------------------------------------------------ *)
(* Bitwise XOR (level 57, left) *)

Notation "e1 ^8u e2" := (Papp2 (Olxor U8) e1 e2)
  (at level 57, left associativity) : jexpr_scope.
Notation "e1 ^16u e2" := (Papp2 (Olxor U16) e1 e2)
  (at level 57, left associativity) : jexpr_scope.
Notation "e1 ^32u e2" := (Papp2 (Olxor U32) e1 e2)
  (at level 57, left associativity) : jexpr_scope.
Notation "e1 ^64u e2" := (Papp2 (Olxor U64) e1 e2)
  (at level 57, left associativity) : jexpr_scope.
Notation "e1 ^128u e2" := (Papp2 (Olxor U128) e1 e2)
  (at level 57, left associativity) : jexpr_scope.
Notation "e1 ^256u e2" := (Papp2 (Olxor U256) e1 e2)
  (at level 57, left associativity) : jexpr_scope.

(* ------------------------------------------------------------------ *)
(* Bitwise OR (level 59, left) *)

Notation "e1 |8u e2" := (Papp2 (Olor U8) e1 e2)
  (at level 59, left associativity) : jexpr_scope.
Notation "e1 |16u e2" := (Papp2 (Olor U16) e1 e2)
  (at level 59, left associativity) : jexpr_scope.
Notation "e1 |32u e2" := (Papp2 (Olor U32) e1 e2)
  (at level 59, left associativity) : jexpr_scope.
Notation "e1 |64u e2" := (Papp2 (Olor U64) e1 e2)
  (at level 59, left associativity) : jexpr_scope.
Notation "e1 |128u e2" := (Papp2 (Olor U128) e1 e2)
  (at level 59, left associativity) : jexpr_scope.
Notation "e1 |256u e2" := (Papp2 (Olor U256) e1 e2)
  (at level 59, left associativity) : jexpr_scope.

(* ------------------------------------------------------------------ *)
(* Comparisons (level 70, no associativity) *)

Notation "e1 ==i e2" := (Papp2 (Oeq Op_int) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 ==8u e2" := (Papp2 (Oeq (Op_w U8)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 ==16u e2" := (Papp2 (Oeq (Op_w U16)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 ==32u e2" := (Papp2 (Oeq (Op_w U32)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 ==64u e2" := (Papp2 (Oeq (Op_w U64)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 ==128u e2" := (Papp2 (Oeq (Op_w U128)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 ==256u e2" := (Papp2 (Oeq (Op_w U256)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.

Notation "e1 !=i e2" := (Papp2 (Oneq Op_int) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 !=8u e2" := (Papp2 (Oneq (Op_w U8)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 !=16u e2" := (Papp2 (Oneq (Op_w U16)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 !=32u e2" := (Papp2 (Oneq (Op_w U32)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 !=64u e2" := (Papp2 (Oneq (Op_w U64)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.

Notation "e1 <i e2" := (Papp2 (Olt Cmp_int) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <8u e2" := (Papp2 (Olt (Cmp_w Unsigned U8)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <16u e2" := (Papp2 (Olt (Cmp_w Unsigned U16)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <32u e2" := (Papp2 (Olt (Cmp_w Unsigned U32)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <64u e2" := (Papp2 (Olt (Cmp_w Unsigned U64)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <128u e2" := (Papp2 (Olt (Cmp_w Unsigned U128)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <256u e2" := (Papp2 (Olt (Cmp_w Unsigned U256)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <8s e2" := (Papp2 (Olt (Cmp_w Signed U8)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <16s e2" := (Papp2 (Olt (Cmp_w Signed U16)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <32s e2" := (Papp2 (Olt (Cmp_w Signed U32)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <64s e2" := (Papp2 (Olt (Cmp_w Signed U64)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.

Notation "e1 <=i e2" := (Papp2 (Ole Cmp_int) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <=8u e2" := (Papp2 (Ole (Cmp_w Unsigned U8)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <=16u e2" := (Papp2 (Ole (Cmp_w Unsigned U16)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <=32u e2" := (Papp2 (Ole (Cmp_w Unsigned U32)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <=64u e2" := (Papp2 (Ole (Cmp_w Unsigned U64)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <=8s e2" := (Papp2 (Ole (Cmp_w Signed U8)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <=16s e2" := (Papp2 (Ole (Cmp_w Signed U16)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <=32s e2" := (Papp2 (Ole (Cmp_w Signed U32)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 <=64s e2" := (Papp2 (Ole (Cmp_w Signed U64)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.

Notation "e1 >i e2" := (Papp2 (Ogt Cmp_int) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >8u e2" := (Papp2 (Ogt (Cmp_w Unsigned U8)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >16u e2" := (Papp2 (Ogt (Cmp_w Unsigned U16)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >32u e2" := (Papp2 (Ogt (Cmp_w Unsigned U32)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >64u e2" := (Papp2 (Ogt (Cmp_w Unsigned U64)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >128u e2" := (Papp2 (Ogt (Cmp_w Unsigned U128)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >256u e2" := (Papp2 (Ogt (Cmp_w Unsigned U256)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >8s e2" := (Papp2 (Ogt (Cmp_w Signed U8)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >16s e2" := (Papp2 (Ogt (Cmp_w Signed U16)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >32s e2" := (Papp2 (Ogt (Cmp_w Signed U32)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >64s e2" := (Papp2 (Ogt (Cmp_w Signed U64)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.

Notation "e1 >=i e2" := (Papp2 (Oge Cmp_int) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >=8u e2" := (Papp2 (Oge (Cmp_w Unsigned U8)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >=16u e2" := (Papp2 (Oge (Cmp_w Unsigned U16)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >=32u e2" := (Papp2 (Oge (Cmp_w Unsigned U32)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >=64u e2" := (Papp2 (Oge (Cmp_w Unsigned U64)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >=8s e2" := (Papp2 (Oge (Cmp_w Signed U8)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >=16s e2" := (Papp2 (Oge (Cmp_w Signed U16)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >=32s e2" := (Papp2 (Oge (Cmp_w Signed U32)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 >=64s e2" := (Papp2 (Oge (Cmp_w Signed U64)) e1 e2)
  (at level 70, no associativity) : jexpr_scope.

(* Wint comparisons (level 70) *)
Notation "e1 ==wu[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIeq) e1 e2)
  (at level 70, no associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 ==ws[ sz ] e2" := (Papp2 (Owi2 Signed sz WIeq) e1 e2)
  (at level 70, no associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 !=wu[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIneq) e1 e2)
  (at level 70, no associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 !=ws[ sz ] e2" := (Papp2 (Owi2 Signed sz WIneq) e1 e2)
  (at level 70, no associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 <wu[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIlt) e1 e2)
  (at level 70, no associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 <ws[ sz ] e2" := (Papp2 (Owi2 Signed sz WIlt) e1 e2)
  (at level 70, no associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 <=wu[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIle) e1 e2)
  (at level 70, no associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 <=ws[ sz ] e2" := (Papp2 (Owi2 Signed sz WIle) e1 e2)
  (at level 70, no associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 >wu[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIgt) e1 e2)
  (at level 70, no associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 >ws[ sz ] e2" := (Papp2 (Owi2 Signed sz WIgt) e1 e2)
  (at level 70, no associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 >=wu[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIge) e1 e2)
  (at level 70, no associativity, sz constr at level 0) : jexpr_scope.
Notation "e1 >=ws[ sz ] e2" := (Papp2 (Owi2 Signed sz WIge) e1 e2)
  (at level 70, no associativity, sz constr at level 0) : jexpr_scope.

(* ------------------------------------------------------------------ *)
(* Boolean operators (renamed to avoid stdlib level conflicts)
   Levels 80 and 85 are right-assoc from Prop /\ and \/ so we use 82, 86. *)

Notation "e1 ==e e2" := (Papp2 Obeq e1 e2)
  (at level 70, no associativity) : jexpr_scope.
Notation "e1 &&e e2" := (Papp2 Oand e1 e2)
  (at level 82, left associativity) : jexpr_scope.
Notation "e1 ||e e2" := (Papp2 Oor e1 e2)
  (at level 86, left associativity) : jexpr_scope.

(* ------------------------------------------------------------------ *)

Section ExprTests.

Context (x y z b : gvar).

Goal (mem[U64](x))%E = Pload Unaligned U64 (Pvar x). done. Qed.

Goal (aget[U64](x, 0))%E =
  Pget Aligned AAscale U64 x (Pconst 0). done. Qed.

Goal (-i 5)%E = Papp1 (Oneg Op_int) (Pconst 5). done. Qed.
Goal (-64u x)%E = Papp1 (Oneg (Op_w U64)) (Pvar x). done. Qed.
Goal (![b] b)%E = Papp1 Onot (Pvar b). done. Qed.
Goal (!64u x)%E = Papp1 (Olnot U64) (Pvar x). done. Qed.
Goal (i2w[U8] 42)%E =
  Papp1 (Oword_of_int U8) (Pconst 42). done. Qed.
Goal (i2w[U64] 0)%E =
  Papp1 (Oword_of_int U64) (Pconst 0). done. Qed.

Goal (3 +i 7)%E =
  Papp2 (Oadd Op_int) (Pconst 3) (Pconst 7). done. Qed.
Goal (x +64u y)%E =
  Papp2 (Oadd (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal (z *64u x +64u 3)%E =
  Papp2 (Oadd (Op_w U64))
    (Papp2 (Omul (Op_w U64)) (Pvar z) (Pvar x)) (Pconst 3).
done. Qed.
Goal (5 -i 2)%E =
  Papp2 (Osub Op_int) (Pconst 5) (Pconst 2). done. Qed.
Goal (x -64u y)%E =
  Papp2 (Osub (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal (2 *i 3)%E =
  Papp2 (Omul Op_int) (Pconst 2) (Pconst 3). done. Qed.
Goal (x &64u y)%E = Papp2 (Oland U64) (Pvar x) (Pvar y). done. Qed.
Goal (x ^64u y)%E = Papp2 (Olxor U64) (Pvar x) (Pvar y). done. Qed.
Goal (x |64u y)%E = Papp2 (Olor U64) (Pvar x) (Pvar y). done. Qed.
Goal (1 <<i 3)%E =
  Papp2 (Olsl Op_int) (Pconst 1) (Pconst 3). done. Qed.
Goal (y <<64u y)%E =
  Papp2 (Olsl (Op_w U64)) (Pvar y) (Pvar y). done. Qed.
Goal (y >>64u y)%E = Papp2 (Olsr U64) (Pvar y) (Pvar y). done. Qed.
Goal (8 >>si 1)%E =
  Papp2 (Oasr Op_int) (Pconst 8) (Pconst 1). done. Qed.
Goal (x >>s64u y)%E =
  Papp2 (Oasr (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal (x <<r64u y)%E = Papp2 (Orol U64) (Pvar x) (Pvar y). done. Qed.
Goal (x >>r64u y)%E = Papp2 (Oror U64) (Pvar x) (Pvar y). done. Qed.
Goal (x /64u y)%E =
  Papp2 (Odiv Unsigned (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal (x /64s y)%E =
  Papp2 (Odiv Signed (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal (x %64u y)%E =
  Papp2 (Omod Unsigned (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal (x %64s y)%E =
  Papp2 (Omod Signed (Op_w U64)) (Pvar x) (Pvar y). done. Qed.

Goal (x ==64u y)%E =
  Papp2 (Oeq (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal (3 !=i 4)%E =
  Papp2 (Oneq Op_int) (Pconst 3) (Pconst 4). done. Qed.
Goal (1 <i 2)%E =
  Papp2 (Olt Cmp_int) (Pconst 1) (Pconst 2). done. Qed.
Goal (x <64s y)%E =
  Papp2 (Olt (Cmp_w Signed U64)) (Pvar x) (Pvar y). done. Qed.
Goal (1 <=i 2)%E =
  Papp2 (Ole Cmp_int) (Pconst 1) (Pconst 2). done. Qed.
Goal (x <=64s y)%E =
  Papp2 (Ole (Cmp_w Signed U64)) (Pvar x) (Pvar y). done. Qed.
Goal (b ==e b)%E = Papp2 Obeq (Pvar b) (Pvar b). done. Qed.

Goal (ite[b](b, x, y))%E =
  Pif abool (Pvar b) (Pvar x) (Pvar y). done. Qed.
Goal (ite[i](b, x, y))%E =
  Pif aint (Pvar b) (Pvar x) (Pvar y). done. Qed.
Goal (ite[32u](true, x &32u y, z))%E =
  Pif (aword U32) (Pbool true)
    (Papp2 (Oland U32) (Pvar x) (Pvar y)) (Pvar z).
done. Qed.
Goal (ite[64u](b, x, y))%E =
  Pif (aword U64) (Pvar b) (Pvar x) (Pvar y). done. Qed.

Goal (b &&e x <=64u y)%E =
  Papp2 Oand (Pvar b)
    (Papp2 (Ole (Cmp_w Unsigned U64)) (Pvar x) (Pvar y)).
done. Qed.
Goal (x !=64u y ||e x <64u y)%E =
  Papp2 Oor
    (Papp2 (Oneq (Op_w U64)) (Pvar x) (Pvar y))
    (Papp2 (Olt (Cmp_w Unsigned U64)) (Pvar x) (Pvar y)).
done. Qed.
Goal (true ||e false &&e 1 -i 10 ==i false)%E =
  Papp2 Oor (Pbool true)
    (Papp2 Oand (Pbool false)
      (Papp2 (Oeq Op_int)
        (Papp2 (Osub Op_int) (Pconst 1) (Pconst 10))
        (Pbool false))).
done. Qed.

Goal (u2i[U8] x)%E =
  Papp1 (Oint_of_word Unsigned U8) (Pvar x). done. Qed.
Goal (u2i[U64] x)%E =
  Papp1 (Oint_of_word Unsigned U64) (Pvar x). done. Qed.
Goal (s2i[U8] x)%E =
  Papp1 (Oint_of_word Signed U8) (Pvar x). done. Qed.
Goal (s2i[U64] x)%E =
  Papp1 (Oint_of_word Signed U64) (Pvar x). done. Qed.

Goal (zext[U8, U16] x)%E =
  Papp1 (Ozeroext U16 U8) (Pvar x). done. Qed.
Goal (zext[U32, U64] x)%E =
  Papp1 (Ozeroext U64 U32) (Pvar x). done. Qed.
Goal (zext[U128, U256] x)%E =
  Papp1 (Ozeroext U256 U128) (Pvar x). done. Qed.

Goal (sext[U8, U16] x)%E =
  Papp1 (Osignext U16 U8) (Pvar x). done. Qed.
Goal (sext[U32, U64] x)%E =
  Papp1 (Osignext U64 U32) (Pvar x). done. Qed.
Goal (sext[U128, U256] x)%E =
  Papp1 (Osignext U256 U128) (Pvar x). done. Qed.

Goal (x *128u y)%E =
  Papp2 (Omul (Op_w U128)) (Pvar x) (Pvar y). done. Qed.
Goal (x *256u y)%E =
  Papp2 (Omul (Op_w U256)) (Pvar x) (Pvar y). done. Qed.

Goal (asub[U64](x, 4, 0))%E =
  Psub AAscale U64 4 x (Pconst 0). done. Qed.

Goal (x >i y)%E =
  Papp2 (Ogt Cmp_int) (Pvar x) (Pvar y). done. Qed.
Goal (x >64u y)%E =
  Papp2 (Ogt (Cmp_w Unsigned U64)) (Pvar x) (Pvar y). done. Qed.
Goal (x >64s y)%E =
  Papp2 (Ogt (Cmp_w Signed U64)) (Pvar x) (Pvar y). done. Qed.
Goal (x >=i y)%E =
  Papp2 (Oge Cmp_int) (Pvar x) (Pvar y). done. Qed.
Goal (x >=64u y)%E =
  Papp2 (Oge (Cmp_w Unsigned U64)) (Pvar x) (Pvar y). done. Qed.
Goal (x >=64s y)%E =
  Papp2 (Oge (Cmp_w Signed U64)) (Pvar x) (Pvar y). done. Qed.

Goal (mem[U8](x))%E = Pload Unaligned U8 (Pvar x). done. Qed.
Goal (mem[U16](x))%E = Pload Unaligned U16 (Pvar x). done. Qed.
Goal (mem[U32](x))%E = Pload Unaligned U32 (Pvar x). done. Qed.
Goal (mem[U128](x))%E = Pload Unaligned U128 (Pvar x). done. Qed.
Goal (mem[U256](x))%E = Pload Unaligned U256 (Pvar x). done. Qed.
Goal (mem[U64](x +64u y))%E =
  Pload Unaligned U64
    (Papp2 (Oadd (Op_w U64)) (Pvar x) (Pvar y)).
done. Qed.

Goal (aget[U8](x, 0))%E =
  Pget Aligned AAscale U8 x (Pconst 0). done. Qed.
Goal (aget[U32](x, 0))%E =
  Pget Aligned AAscale U32 x (Pconst 0). done. Qed.
Goal (aget[U64](x, y))%E =
  Pget Aligned AAscale U64 x (Pvar y). done. Qed.
Goal (aget[U64](x, y +64u 1))%E =
  Pget Aligned AAscale U64 x
    (Papp2 (Oadd (Op_w U64)) (Pvar y) (Pconst 1)).
done. Qed.

Goal (i2wu[U64] 42)%E =
  Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst 42). done. Qed.
Goal (i2ws[U32] 0)%E =
  Papp1 (Owi1 Signed (WIwint_of_int U32)) (Pconst 0). done. Qed.
Goal (wu2i[U64] x)%E =
  Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar x). done. Qed.
Goal (ws2i[U32] x)%E =
  Papp1 (Owi1 Signed (WIint_of_wint U32)) (Pvar x). done. Qed.
Goal (wu2w[U64] x)%E =
  Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar x). done. Qed.
Goal (ws2w[U32] x)%E =
  Papp1 (Owi1 Signed (WIword_of_wint U32)) (Pvar x). done. Qed.
Goal (w2wu[U64] x)%E =
  Papp1 (Owi1 Unsigned (WIwint_of_word U64)) (Pvar x). done. Qed.
Goal (w2ws[U32] x)%E =
  Papp1 (Owi1 Signed (WIwint_of_word U32)) (Pvar x). done. Qed.
Goal (wuext[U32, U64] x)%E =
  Papp1 (Owi1 Unsigned (WIwint_ext U64 U32)) (Pvar x). done. Qed.
Goal (wsext[U32, U64] x)%E =
  Papp1 (Owi1 Signed (WIwint_ext U64 U32)) (Pvar x). done. Qed.
Goal (-wu[U64] x)%E =
  Papp1 (Owi1 Unsigned (WIneg U64)) (Pvar x). done. Qed.
Goal (-ws[U32] x)%E =
  Papp1 (Owi1 Signed (WIneg U32)) (Pvar x). done. Qed.

Goal (x +wu[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIadd) (Pvar x) (Pvar y). done. Qed.
Goal (x +ws[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIadd) (Pvar x) (Pvar y). done. Qed.
Goal (x -wu[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIsub) (Pvar x) (Pvar y). done. Qed.
Goal (x -ws[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIsub) (Pvar x) (Pvar y). done. Qed.
Goal (x *wu[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WImul) (Pvar x) (Pvar y). done. Qed.
Goal (x *ws[U32] y)%E =
  Papp2 (Owi2 Signed U32 WImul) (Pvar x) (Pvar y). done. Qed.
Goal (x /wu[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIdiv) (Pvar x) (Pvar y). done. Qed.
Goal (x /ws[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIdiv) (Pvar x) (Pvar y). done. Qed.
Goal (x %wu[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WImod) (Pvar x) (Pvar y). done. Qed.
Goal (x %ws[U32] y)%E =
  Papp2 (Owi2 Signed U32 WImod) (Pvar x) (Pvar y). done. Qed.
Goal (x <<wu[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIshl) (Pvar x) (Pvar y). done. Qed.
Goal (x <<ws[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIshl) (Pvar x) (Pvar y). done. Qed.
Goal (x >>wu[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIshr) (Pvar x) (Pvar y). done. Qed.
Goal (x >>ws[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIshr) (Pvar x) (Pvar y). done. Qed.
Goal (x ==wu[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIeq) (Pvar x) (Pvar y). done. Qed.
Goal (x ==ws[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIeq) (Pvar x) (Pvar y). done. Qed.
Goal (x !=wu[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIneq) (Pvar x) (Pvar y). done. Qed.
Goal (x !=ws[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIneq) (Pvar x) (Pvar y). done. Qed.
Goal (x <wu[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIlt) (Pvar x) (Pvar y). done. Qed.
Goal (x <ws[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIlt) (Pvar x) (Pvar y). done. Qed.
Goal (x <=wu[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIle) (Pvar x) (Pvar y). done. Qed.
Goal (x <=ws[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIle) (Pvar x) (Pvar y). done. Qed.
Goal (x >wu[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIgt) (Pvar x) (Pvar y). done. Qed.
Goal (x >ws[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIgt) (Pvar x) (Pvar y). done. Qed.
Goal (x >=wu[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIge) (Pvar x) (Pvar y). done. Qed.
Goal (x >=ws[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIge) (Pvar x) (Pvar y). done. Qed.

Goal (42 +64u x)%E =
  Papp2 (Oadd (Op_w U64)) (Pconst 42) (Pvar x). done. Qed.

End ExprTests.
