(* Display notations for Jasmin expressions (scope [%E])

  Activate with [e%E] or [Open Scope jexpr_scope].
  Integer literals are interpreted with a [Number Notation].
  [bool] and [gvar] values coerce to [pexpr] via [Pbool] and [Pvar].

* Memory and arrays

  - [mget[w](e)]             unaligned memory load, word size [w], address [e]
  - [aget[w](v, i)]          aligned array read, word size [w], index [i]
  - [sget[w](v, len, i)]     aligned array slice, word size [w], length [len],
                             index [i]

* Unary operators (Papp1) — level 30, right-associative

  Type conversions:
  - [i2w[w] e]               int -> word [w]           (Oword_of_int)
  - [u2i[w] e]               word [w] -> unsigned int  (Oint_of_word Unsigned)
  - [s2i[w] e]               word [w] -> signed int    (Oint_of_word Signed)
  - [zext[szi, szo] e]       zero-extend from [szi] to [szo]
  - [sext[szi, szo] e]       sign-extend from [szi] to [szo]

  Negation and bitwise not:
  - [![b] e]                 boolean not                  (Onot)
  - [![w] e]                 bitwise NOT, word size [w]   (Olnot)
  - [-[i] e]                 integer negation             (Oneg Op_int)
  - [-[w] e]                 word negation, size [w]      (Oneg (Op_w w))

  Wint (bounded word-size integer) conversions and unary ops:
  - [i2ui[w] e]              int -> unsigned wint [w]
  - [i2si[w] e]              int -> signed wint [w]
  - [ui2i[w] e]              unsigned wint [w] -> int
  - [si2i[w] e]              signed wint [w] -> int
  - [ui2w[w] e]              unsigned wint [w] -> word [w]
  - [si2w[w] e]              signed wint [w] -> word [w]
  - [w2ui[w] e]              word [w] -> unsigned wint [w]
  - [w2si[w] e]              word [w] -> signed wint [w]
  - [uiext[szi, szo] e]      unsigned wint extension from [szi] to [szo]
  - [siext[szi, szo] e]      signed wint extension from [szi] to [szo]
  - [-ui[w] e]               unsigned wint negation
  - [-si[w] e]               signed wint negation

* Binary operators (Papp2)

  Boolean:
  - [e1 ==[b] e2]            equality              (level 70, none)
  - [e1 &&[b] e2]            and                   (level 82, left)
  - [e1 ||[b] e2]            or                    (level 86, left)

  Integer (suffix [i]):
  - [e1 +[i] e2]             addition              (level 50, left)
  - [e1 -[i] e2]             subtraction           (level 50, left)
  - [e1 *[i] e2]             multiplication        (level 40, left)
  - [e1 /u[i] e2]            unsigned division     (level 40, left)
  - [e1 /s[i] e2]            signed division       (level 40, left)
  - [e1 %u[i] e2]            unsigned modulo       (level 40, left)
  - [e1 %s[i] e2]            signed modulo         (level 40, left)
  - [e1 <<[i] e2]            logical shift left    (level 45, left)
  - [e1 >>s[i] e2]           arithmetic shift right (level 45, left)
  - [e1 ==[i] e2]  [e1 !=[i] e2]  equality/inequality (level 70, none)
  - [e1 <[i] e2]   [e1 <=[i] e2]  less / less-or-equal       (level 70, none)
  - [e1 >[i] e2]   [e1 >=[i] e2]  greater / greater-or-equal (level 70, none)

  Word (suffix [w] for word size; [u]/[s] for unsigned/signed):
  - [e1 +[w] e2]             addition              (level 50, left)
  - [e1 -[w] e2]             subtraction           (level 50, left)
  - [e1 *[w] e2]             multiplication        (level 40, left)
  - [e1 /u[w] e2]            unsigned division     (level 40, left)
  - [e1 /s[w] e2]            signed division       (level 40, left)
  - [e1 %u[w] e2]            unsigned modulo       (level 40, left)
  - [e1 %s[w] e2]            signed modulo         (level 40, left)
  - [e1 &[w] e2]             bitwise AND           (level 54, left)
  - [e1 ^[w] e2]             bitwise XOR           (level 57, left)
  - [e1 |[w] e2]             bitwise OR            (level 59, left)
  - [e1 <<[w] e2]            logical shift left    (level 45, left)
  - [e1 >>[w] e2]            logical shift right   (level 45, left)
  - [e1 >>s[w] e2]           arithmetic shift right (level 45, left)
  - [e1 <<r[w] e2]           rotate left           (level 45, left)
  - [e1 >>r[w] e2]           rotate right          (level 45, left)
  - [e1 ==[w] e2]  [e1 !=[w] e2]  equality/inequality (level 70, none)
  - [e1 <u[w] e2]  [e1 <=u[w] e2] unsigned comparison (level 70, none)
  - [e1 <s[w] e2]  [e1 <=s[w] e2] signed comparison   (level 70, none)
  - [e1 >u[w] e2]  [e1 >=u[w] e2] unsigned comparison (level 70, none)
  - [e1 >s[w] e2]  [e1 >=s[w] e2] signed comparison   (level 70, none)

  Wint binary (suffix [ui[N]]/[si[N]] for unsigned/signed wint of size [N]):
  - [e1 +ui[N] e2]           addition              (level 50, left)
  - [e1 -ui[N] e2]           subtraction           (level 50, left)
  - [e1 *ui[N] e2]           multiplication        (level 40, left)
  - [e1 /ui[N] e2]           division              (level 40, left)
  - [e1 %ui[N] e2]           modulo                (level 40, left)
  - [e1 <<ui[N] e2]          shift left            (level 45, left)
  - [e1 >>ui[N] e2]          shift right           (level 45, left)
  - [e1 ==ui[N] e2]  [e1 !=ui[N] e2]  equality/inequality (level 70, none)
  - [e1 <ui[N] e2]   [e1 <=ui[N] e2]  less / less-or-equal       (level 70, none)
  - [e1 >ui[N] e2]   [e1 >=ui[N] e2]  greater / greater-or-equal (level 70, none)
  (Replace [ui] with [si] for the signed wint variants.)

* Conditional (Pif)

  - [ite[t](e1, e2, e3)]     if [e1] then [e2] else [e3], type annotation [t]
    where [t] is [b] (bool), [i] (int), or a word size (e.g. [U64])

* Not supported

  pexpr constructors:
  - [Parr_init w n]               array initialisation expression

  - [Pget Aligned AAdirect w v e]   unscaled aligned array read
  - [Pget Unaligned AAscale w v e]  scaled unaligned array read
  - [Pget Unaligned AAdirect w v e] unscaled unaligned array read

  - [Psub AAdirect w len v e]     unscaled array slice

  - [Pload Aligned w e]           aligned memory load

  - [Opack w pe]                  pack values into a word
  - [Oarray n]                    array literal of length [n]
  - [Ocombine_flags cf]           combine processor flags

  - [Ovadd ve w]                  vector addition
  - [Ovsub ve w]                  vector subtraction
  - [Ovmul ve w]                  vector multiplication
  - [Ovlsr ve w]                  vector logical shift right
  - [Ovlsl ve w]                  vector logical shift left
  - [Ovasr ve w]                  vector arithmetic shift right *)

From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr.

Declare Scope jexpr_scope.
Delimit Scope jexpr_scope with E.
Bind Scope jexpr_scope with pexpr.

(* Custom entry for wsize: accepts any wsize constructor or variable. *)
Declare Custom Entry jwsize.
Notation "w" := w
  (in custom jwsize at level 0, w constr at level 0).

(* Custom entry for annotated types: b = abool, i = aint,
   ws = aword ws, or ws , len = aarr ws len. *)
Declare Custom Entry jatype.
Notation "'b'" := abool (in custom jatype at level 0).
Notation "'i'" := aint (in custom jatype at level 0).
Notation "ws" := (aword ws)
  (in custom jatype at level 0, ws custom jwsize at level 0).
Notation "ws , len" := (aarr ws len)
  (in custom jatype at level 1,
   ws custom jwsize at level 0, len constr at level 0).

(* -------------------------------------------------------------------------- *)
(* Constants *)

Number Notation pexpr Pconst is_const : jexpr_scope.

(* -------------------------------------------------------------------------- *)
(* Memory and arrays. *)

Notation "aget[ w ]( v , i )" := (Pget Aligned AAscale w v i%E)
  (at level 0, w constr at level 0, v constr at level 0,
   i at level 99,
   format "aget[ w ]( v ,  i )") : jexpr_scope.

Notation "sget[ w ]( v , len , i )" := (Psub AAscale w len v i%E)
  (at level 0, w constr at level 0, v constr at level 0,
   len constr at level 0, i at level 99,
   format "sget[ w ]( v ,  len ,  i )") : jexpr_scope.

Notation "mget[ w ]( e )" := (Pload Unaligned w e%E)
  (at level 0, w constr at level 0, e at level 99,
   format "mget[ w ]( e )") : jexpr_scope.

(* -------------------------------------------------------------------------- *)
(* Papp1 — Unary operators (level 30, right assoc) *)

Notation "i2w[ w ] e" := (Papp1 (Oword_of_int w) e%E)
  (at level 30, w constr at level 0,
   right associativity,
   format "i2w[ w ]  e") : jexpr_scope.

Notation "u2i[ w ] e" := (Papp1 (Oint_of_word Unsigned w) e%E)
  (at level 30, w constr at level 0,
   right associativity,
   format "u2i[ w ]  e") : jexpr_scope.
Notation "s2i[ w ] e" := (Papp1 (Oint_of_word Signed w) e%E)
  (at level 30, w constr at level 0,
   right associativity,
   format "s2i[ w ]  e") : jexpr_scope.

Notation "sext[ szi , szo ] e" := (Papp1 (Osignext szo szi) e%E)
  (at level 30, szi constr at level 0, szo constr at level 0,
   right associativity,
   format "sext[ szi ,  szo ]  e") : jexpr_scope.

Notation "zext[ szi , szo ] e" := (Papp1 (Ozeroext szo szi) e%E)
  (at level 30, szi constr at level 0, szo constr at level 0,
   right associativity,
   format "zext[ szi ,  szo ]  e") : jexpr_scope.

Notation "![b] e" := (Papp1 Onot e%E)
  (at level 30, right associativity,
   format "![b]  e") : jexpr_scope.

Notation "![ w ] e" := (Papp1 (Olnot w) e%E)
  (at level 30, w custom jwsize at level 0,
   right associativity,
   format "![ w ]  e") : jexpr_scope.

Notation "-[i] e" := (Papp1 (Oneg Op_int) e%E)
  (at level 30, right associativity,
   format "-[i]  e") : jexpr_scope.
Notation "-[ w ] e" := (Papp1 (Oneg (Op_w w)) e%E)
  (at level 30, w custom jwsize at level 0,
   right associativity,
   format "-[ w ]  e") : jexpr_scope.

Notation "i2ui[ w ] e" := (Papp1 (Owi1 Unsigned (WIwint_of_int w)) e%E)
  (at level 30, w constr at level 0,
   right associativity,
   format "i2ui[ w ]  e") : jexpr_scope.
Notation "i2si[ w ] e" := (Papp1 (Owi1 Signed (WIwint_of_int w)) e%E)
  (at level 30, w constr at level 0,
   right associativity,
   format "i2si[ w ]  e") : jexpr_scope.
Notation "ui2i[ w ] e" := (Papp1 (Owi1 Unsigned (WIint_of_wint w)) e%E)
  (at level 30, w constr at level 0,
   right associativity,
   format "ui2i[ w ]  e") : jexpr_scope.
Notation "si2i[ w ] e" := (Papp1 (Owi1 Signed (WIint_of_wint w)) e%E)
  (at level 30, w constr at level 0,
   right associativity,
   format "si2i[ w ]  e") : jexpr_scope.
Notation "ui2w[ w ] e" := (Papp1 (Owi1 Unsigned (WIword_of_wint w)) e%E)
  (at level 30, w constr at level 0,
   right associativity,
   format "ui2w[ w ]  e") : jexpr_scope.
Notation "si2w[ w ] e" := (Papp1 (Owi1 Signed (WIword_of_wint w)) e%E)
  (at level 30, w constr at level 0,
   right associativity,
   format "si2w[ w ]  e") : jexpr_scope.
Notation "w2ui[ w ] e" := (Papp1 (Owi1 Unsigned (WIwint_of_word w)) e%E)
  (at level 30, w constr at level 0,
   right associativity,
   format "w2ui[ w ]  e") : jexpr_scope.
Notation "w2si[ w ] e" := (Papp1 (Owi1 Signed (WIwint_of_word w)) e%E)
  (at level 30, w constr at level 0,
   right associativity,
   format "w2si[ w ]  e") : jexpr_scope.
Notation "uiext[ szi , szo ] e" :=
  (Papp1 (Owi1 Unsigned (WIwint_ext szo szi)) e%E)
  (at level 30, szi constr at level 0, szo constr at level 0,
   right associativity,
   format "uiext[ szi ,  szo ]  e") : jexpr_scope.
Notation "siext[ szi , szo ] e" :=
  (Papp1 (Owi1 Signed (WIwint_ext szo szi)) e%E)
  (at level 30, szi constr at level 0, szo constr at level 0,
   right associativity,
   format "siext[ szi ,  szo ]  e") : jexpr_scope.
Notation "-ui[ w ] e" := (Papp1 (Owi1 Unsigned (WIneg w)) e%E)
  (at level 30, w constr at level 0,
   right associativity,
   format "-ui[ w ]  e") : jexpr_scope.
Notation "-si[ w ] e" := (Papp1 (Owi1 Signed (WIneg w)) e%E)
  (at level 30, w constr at level 0,
   right associativity,
   format "-si[ w ]  e") : jexpr_scope.

(* -------------------------------------------------------------------------- *)
(* Papp2 — Binary operators *)

Notation "e1 ==[b] e2" := (Papp2 Obeq e1%E e2%E)
  (at level 70, no associativity,
   format "e1  ==[b]  e2") : jexpr_scope.

Notation "e1 &&[b] e2" := (Papp2 Oand e1%E e2%E)
  (at level 82, left associativity,
   format "e1  &&[b]  e2") : jexpr_scope.

Notation "e1 ||[b] e2" := (Papp2 Oor e1%E e2%E)
  (at level 86, left associativity,
   format "e1  ||[b]  e2") : jexpr_scope.

Notation "e1 +[i] e2" := (Papp2 (Oadd Op_int) e1%E e2%E)
  (at level 50, left associativity,
   format "e1  +[i]  e2") : jexpr_scope.
Notation "e1 +[ w ] e2" := (Papp2 (Oadd (Op_w w)) e1%E e2%E)
  (at level 50, left associativity,
   w custom jwsize at level 0,
   format "e1  +[ w ]  e2") : jexpr_scope.

Notation "e1 *[i] e2" := (Papp2 (Omul Op_int) e1%E e2%E)
  (at level 40, left associativity,
   format "e1  *[i]  e2") : jexpr_scope.
Notation "e1 *[ w ] e2" := (Papp2 (Omul (Op_w w)) e1%E e2%E)
  (at level 40, left associativity,
   w custom jwsize at level 0,
   format "e1  *[ w ]  e2") : jexpr_scope.

Notation "e1 -[i] e2" := (Papp2 (Osub Op_int) e1%E e2%E)
  (at level 50, left associativity,
   format "e1  -[i]  e2") : jexpr_scope.
Notation "e1 -[ w ] e2" := (Papp2 (Osub (Op_w w)) e1%E e2%E)
  (at level 50, left associativity,
   w custom jwsize at level 0,
   format "e1  -[ w ]  e2") : jexpr_scope.

Notation "e1 /u[i] e2" := (Papp2 (Odiv Unsigned Op_int) e1%E e2%E)
  (at level 40, left associativity,
   format "e1  /u[i]  e2") : jexpr_scope.
Notation "e1 /s[i] e2" := (Papp2 (Odiv Signed Op_int) e1%E e2%E)
  (at level 40, left associativity,
   format "e1  /s[i]  e2") : jexpr_scope.

Notation "e1 /u[ w ] e2" := (Papp2 (Odiv Unsigned (Op_w w)) e1%E e2%E)
  (at level 40, left associativity,
   w custom jwsize at level 0,
   format "e1  /u[ w ]  e2") : jexpr_scope.
Notation "e1 /s[ w ] e2" := (Papp2 (Odiv Signed (Op_w w)) e1%E e2%E)
  (at level 40, left associativity,
   w custom jwsize at level 0,
   format "e1  /s[ w ]  e2") : jexpr_scope.

Notation "e1 %u[i] e2" := (Papp2 (Omod Unsigned Op_int) e1%E e2%E)
  (at level 40, left associativity,
   format "e1  %u[i]  e2") : jexpr_scope.
Notation "e1 %s[i] e2" := (Papp2 (Omod Signed Op_int) e1%E e2%E)
  (at level 40, left associativity,
   format "e1  %s[i]  e2") : jexpr_scope.

Notation "e1 %u[ w ] e2" := (Papp2 (Omod Unsigned (Op_w w)) e1%E e2%E)
  (at level 40, left associativity,
   w custom jwsize at level 0,
   format "e1  %u[ w ]  e2") : jexpr_scope.
Notation "e1 %s[ w ] e2" := (Papp2 (Omod Signed (Op_w w)) e1%E e2%E)
  (at level 40, left associativity,
   w custom jwsize at level 0,
   format "e1  %s[ w ]  e2") : jexpr_scope.

Notation "e1 &[ w ] e2" := (Papp2 (Oland w) e1%E e2%E)
  (at level 54, left associativity,
   w custom jwsize at level 0,
   format "e1  &[ w ]  e2") : jexpr_scope.

Notation "e1 |[ w ] e2" := (Papp2 (Olor w) e1%E e2%E)
  (at level 59, left associativity,
   w custom jwsize at level 0,
   format "e1  |[ w ]  e2") : jexpr_scope.

Notation "e1 ^[ w ] e2" := (Papp2 (Olxor w) e1%E e2%E)
  (at level 57, left associativity,
   w custom jwsize at level 0,
   format "e1  ^[ w ]  e2") : jexpr_scope.

Notation "e1 >>[ w ] e2" := (Papp2 (Olsr w) e1%E e2%E)
  (at level 45, left associativity,
   w custom jwsize at level 0,
   format "e1  >>[ w ]  e2") : jexpr_scope.

Notation "e1 <<[i] e2" := (Papp2 (Olsl Op_int) e1%E e2%E)
  (at level 45, left associativity,
   format "e1  <<[i]  e2") : jexpr_scope.
Notation "e1 <<[ w ] e2" := (Papp2 (Olsl (Op_w w)) e1%E e2%E)
  (at level 45, left associativity,
   w custom jwsize at level 0,
   format "e1  <<[ w ]  e2") : jexpr_scope.

Notation "e1 >>s[i] e2" := (Papp2 (Oasr Op_int) e1%E e2%E)
  (at level 45, left associativity,
   format "e1  >>s[i]  e2") : jexpr_scope.
Notation "e1 >>s[ w ] e2" := (Papp2 (Oasr (Op_w w)) e1%E e2%E)
  (at level 45, left associativity,
   w custom jwsize at level 0,
   format "e1  >>s[ w ]  e2") : jexpr_scope.

Notation "e1 >>r[ w ] e2" := (Papp2 (Oror w) e1%E e2%E)
  (at level 45, left associativity,
   w custom jwsize at level 0,
   format "e1  >>r[ w ]  e2") : jexpr_scope.

Notation "e1 <<r[ w ] e2" := (Papp2 (Orol w) e1%E e2%E)
  (at level 45, left associativity,
   w custom jwsize at level 0,
   format "e1  <<r[ w ]  e2") : jexpr_scope.

Notation "e1 ==[i] e2" := (Papp2 (Oeq Op_int) e1%E e2%E)
  (at level 70, no associativity,
   format "e1  ==[i]  e2") : jexpr_scope.
Notation "e1 ==[ w ] e2" := (Papp2 (Oeq (Op_w w)) e1%E e2%E)
  (at level 70, no associativity,
   w custom jwsize at level 0,
   format "e1  ==[ w ]  e2") : jexpr_scope.

Notation "e1 !=[i] e2" := (Papp2 (Oneq Op_int) e1%E e2%E)
  (at level 70, no associativity,
   format "e1  !=[i]  e2") : jexpr_scope.
Notation "e1 !=[ w ] e2" := (Papp2 (Oneq (Op_w w)) e1%E e2%E)
  (at level 70, no associativity,
   w custom jwsize at level 0,
   format "e1  !=[ w ]  e2") : jexpr_scope.

Notation "e1 <[i] e2" := (Papp2 (Olt Cmp_int) e1%E e2%E)
  (at level 70, no associativity,
   format "e1  <[i]  e2") : jexpr_scope.
Notation "e1 <u[ w ] e2" := (Papp2 (Olt (Cmp_w Unsigned w)) e1%E e2%E)
  (at level 70, no associativity,
   w custom jwsize at level 0,
   format "e1  <u[ w ]  e2") : jexpr_scope.
Notation "e1 <s[ w ] e2" := (Papp2 (Olt (Cmp_w Signed w)) e1%E e2%E)
  (at level 70, no associativity,
   w custom jwsize at level 0,
   format "e1  <s[ w ]  e2") : jexpr_scope.

Notation "e1 <=[i] e2" := (Papp2 (Ole Cmp_int) e1%E e2%E)
  (at level 70, no associativity,
   format "e1  <=[i]  e2") : jexpr_scope.
Notation "e1 <=u[ w ] e2" := (Papp2 (Ole (Cmp_w Unsigned w)) e1%E e2%E)
  (at level 70, no associativity,
   w custom jwsize at level 0,
   format "e1  <=u[ w ]  e2") : jexpr_scope.
Notation "e1 <=s[ w ] e2" := (Papp2 (Ole (Cmp_w Signed w)) e1%E e2%E)
  (at level 70, no associativity,
   w custom jwsize at level 0,
   format "e1  <=s[ w ]  e2") : jexpr_scope.

Notation "e1 >[i] e2" := (Papp2 (Ogt Cmp_int) e1%E e2%E)
  (at level 70, no associativity,
   format "e1  >[i]  e2") : jexpr_scope.
Notation "e1 >u[ w ] e2" := (Papp2 (Ogt (Cmp_w Unsigned w)) e1%E e2%E)
  (at level 70, no associativity,
   w custom jwsize at level 0,
   format "e1  >u[ w ]  e2") : jexpr_scope.
Notation "e1 >s[ w ] e2" := (Papp2 (Ogt (Cmp_w Signed w)) e1%E e2%E)
  (at level 70, no associativity,
   w custom jwsize at level 0,
   format "e1  >s[ w ]  e2") : jexpr_scope.

Notation "e1 >=[i] e2" := (Papp2 (Oge Cmp_int) e1%E e2%E)
  (at level 70, no associativity,
   format "e1  >=[i]  e2") : jexpr_scope.
Notation "e1 >=u[ w ] e2" := (Papp2 (Oge (Cmp_w Unsigned w)) e1%E e2%E)
  (at level 70, no associativity,
   w custom jwsize at level 0,
   format "e1  >=u[ w ]  e2") : jexpr_scope.
Notation "e1 >=s[ w ] e2" := (Papp2 (Oge (Cmp_w Signed w)) e1%E e2%E)
  (at level 70, no associativity,
   w custom jwsize at level 0,
   format "e1  >=s[ w ]  e2") : jexpr_scope.

Notation "e1 +ui[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIadd) e1%E e2%E)
  (at level 50, left associativity, sz constr at level 0,
   format "e1  +ui[ sz ]  e2") : jexpr_scope.
Notation "e1 +si[ sz ] e2" := (Papp2 (Owi2 Signed sz WIadd) e1%E e2%E)
  (at level 50, left associativity, sz constr at level 0,
   format "e1  +si[ sz ]  e2") : jexpr_scope.
Notation "e1 *ui[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WImul) e1%E e2%E)
  (at level 40, left associativity, sz constr at level 0,
   format "e1  *ui[ sz ]  e2") : jexpr_scope.
Notation "e1 *si[ sz ] e2" := (Papp2 (Owi2 Signed sz WImul) e1%E e2%E)
  (at level 40, left associativity, sz constr at level 0,
   format "e1  *si[ sz ]  e2") : jexpr_scope.
Notation "e1 -ui[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIsub) e1%E e2%E)
  (at level 50, left associativity, sz constr at level 0,
   format "e1  -ui[ sz ]  e2") : jexpr_scope.
Notation "e1 -si[ sz ] e2" := (Papp2 (Owi2 Signed sz WIsub) e1%E e2%E)
  (at level 50, left associativity, sz constr at level 0,
   format "e1  -si[ sz ]  e2") : jexpr_scope.
Notation "e1 /ui[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIdiv) e1%E e2%E)
  (at level 40, left associativity, sz constr at level 0,
   format "e1  /ui[ sz ]  e2") : jexpr_scope.
Notation "e1 /si[ sz ] e2" := (Papp2 (Owi2 Signed sz WIdiv) e1%E e2%E)
  (at level 40, left associativity, sz constr at level 0,
   format "e1  /si[ sz ]  e2") : jexpr_scope.
Notation "e1 %ui[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WImod) e1%E e2%E)
  (at level 40, left associativity, sz constr at level 0,
   format "e1  %ui[ sz ]  e2") : jexpr_scope.
Notation "e1 %si[ sz ] e2" := (Papp2 (Owi2 Signed sz WImod) e1%E e2%E)
  (at level 40, left associativity, sz constr at level 0,
   format "e1  %si[ sz ]  e2") : jexpr_scope.
Notation "e1 <<ui[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIshl) e1%E e2%E)
  (at level 45, left associativity, sz constr at level 0,
   format "e1  <<ui[ sz ]  e2") : jexpr_scope.
Notation "e1 <<si[ sz ] e2" := (Papp2 (Owi2 Signed sz WIshl) e1%E e2%E)
  (at level 45, left associativity, sz constr at level 0,
   format "e1  <<si[ sz ]  e2") : jexpr_scope.
Notation "e1 >>ui[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIshr) e1%E e2%E)
  (at level 45, left associativity, sz constr at level 0,
   format "e1  >>ui[ sz ]  e2") : jexpr_scope.
Notation "e1 >>si[ sz ] e2" := (Papp2 (Owi2 Signed sz WIshr) e1%E e2%E)
  (at level 45, left associativity, sz constr at level 0,
   format "e1  >>si[ sz ]  e2") : jexpr_scope.
Notation "e1 ==ui[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIeq) e1%E e2%E)
  (at level 70, no associativity, sz constr at level 0,
   format "e1  ==ui[ sz ]  e2") : jexpr_scope.
Notation "e1 ==si[ sz ] e2" := (Papp2 (Owi2 Signed sz WIeq) e1%E e2%E)
  (at level 70, no associativity, sz constr at level 0,
   format "e1  ==si[ sz ]  e2") : jexpr_scope.
Notation "e1 !=ui[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIneq) e1%E e2%E)
  (at level 70, no associativity, sz constr at level 0,
   format "e1  !=ui[ sz ]  e2") : jexpr_scope.
Notation "e1 !=si[ sz ] e2" := (Papp2 (Owi2 Signed sz WIneq) e1%E e2%E)
  (at level 70, no associativity, sz constr at level 0,
   format "e1  !=si[ sz ]  e2") : jexpr_scope.
Notation "e1 <ui[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIlt) e1%E e2%E)
  (at level 70, no associativity, sz constr at level 0,
   format "e1  <ui[ sz ]  e2") : jexpr_scope.
Notation "e1 <si[ sz ] e2" := (Papp2 (Owi2 Signed sz WIlt) e1%E e2%E)
  (at level 70, no associativity, sz constr at level 0,
   format "e1  <si[ sz ]  e2") : jexpr_scope.
Notation "e1 <=ui[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIle) e1%E e2%E)
  (at level 70, no associativity, sz constr at level 0,
   format "e1  <=ui[ sz ]  e2") : jexpr_scope.
Notation "e1 <=si[ sz ] e2" := (Papp2 (Owi2 Signed sz WIle) e1%E e2%E)
  (at level 70, no associativity, sz constr at level 0,
   format "e1  <=si[ sz ]  e2") : jexpr_scope.
Notation "e1 >ui[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIgt) e1%E e2%E)
  (at level 70, no associativity, sz constr at level 0,
   format "e1  >ui[ sz ]  e2") : jexpr_scope.
Notation "e1 >si[ sz ] e2" := (Papp2 (Owi2 Signed sz WIgt) e1%E e2%E)
  (at level 70, no associativity, sz constr at level 0,
   format "e1  >si[ sz ]  e2") : jexpr_scope.
Notation "e1 >=ui[ sz ] e2" := (Papp2 (Owi2 Unsigned sz WIge) e1%E e2%E)
  (at level 70, no associativity, sz constr at level 0,
   format "e1  >=ui[ sz ]  e2") : jexpr_scope.
Notation "e1 >=si[ sz ] e2" := (Papp2 (Owi2 Signed sz WIge) e1%E e2%E)
  (at level 70, no associativity, sz constr at level 0,
   format "e1  >=si[ sz ]  e2") : jexpr_scope.

(* -------------------------------------------------------------------------- *)
(* Conditional *)

Notation "ite[ t ]( e1 , e2 , e3 )" := (Pif t e1%E e2%E e3%E)
  (at level 0, t custom jatype at level 0,
   e1 at level 99, e2 at level 99, e3 at level 99,
   format "ite[ t ]( e1 ,  e2 ,  e3 )") : jexpr_scope.

(* -------------------------------------------------------------------------- *)

Section ExprTests.

Context (x y z b : gvar).

Goal (mget[U64](x))%E = Pload Unaligned U64 (Pvar x). done. Qed.

Goal (aget[U64](x, 0))%E =
  Pget Aligned AAscale U64 x (Pconst 0). done. Qed.

Goal (-[i] 5)%E = Papp1 (Oneg Op_int) (Pconst 5). done. Qed.
Goal (-[U64] x)%E = Papp1 (Oneg (Op_w U64)) (Pvar x). done. Qed.
Goal (![b] b)%E = Papp1 Onot (Pvar b). done. Qed.
Goal (![U64] x)%E = Papp1 (Olnot U64) (Pvar x). done. Qed.
Goal (i2w[U8] 42)%E =
  Papp1 (Oword_of_int U8) (Pconst 42). done. Qed.
Goal (i2w[U64] 0)%E =
  Papp1 (Oword_of_int U64) (Pconst 0). done. Qed.

Goal (3 +[i] 7)%E =
  Papp2 (Oadd Op_int) (Pconst 3) (Pconst 7). done. Qed.
Goal (x +[U64] y)%E =
  Papp2 (Oadd (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal (z *[U64] x +[U64] 3)%E =
  Papp2 (Oadd (Op_w U64))
    (Papp2 (Omul (Op_w U64)) (Pvar z) (Pvar x)) (Pconst 3).
done. Qed.
Goal (5 -[i] 2)%E =
  Papp2 (Osub Op_int) (Pconst 5) (Pconst 2). done. Qed.
Goal (x -[U64] y)%E =
  Papp2 (Osub (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal (2 *[i] 3)%E =
  Papp2 (Omul Op_int) (Pconst 2) (Pconst 3). done. Qed.
Goal (x &[U64] y)%E = Papp2 (Oland U64) (Pvar x) (Pvar y). done. Qed.
Goal (x ^[U64] y)%E = Papp2 (Olxor U64) (Pvar x) (Pvar y). done. Qed.
Goal (x |[U64] y)%E = Papp2 (Olor U64) (Pvar x) (Pvar y). done. Qed.
Goal (1 <<[i] 3)%E =
  Papp2 (Olsl Op_int) (Pconst 1) (Pconst 3). done. Qed.
Goal (y <<[U64] y)%E =
  Papp2 (Olsl (Op_w U64)) (Pvar y) (Pvar y). done. Qed.
Goal (y >>[U64] y)%E = Papp2 (Olsr U64) (Pvar y) (Pvar y). done. Qed.
Goal (8 >>s[i] 1)%E =
  Papp2 (Oasr Op_int) (Pconst 8) (Pconst 1). done. Qed.
Goal (x >>s[U64] y)%E =
  Papp2 (Oasr (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal (x <<r[U64] y)%E = Papp2 (Orol U64) (Pvar x) (Pvar y). done. Qed.
Goal (x >>r[U64] y)%E = Papp2 (Oror U64) (Pvar x) (Pvar y). done. Qed.
Goal (x /u[U64] y)%E =
  Papp2 (Odiv Unsigned (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal (x /s[U64] y)%E =
  Papp2 (Odiv Signed (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal (x %u[U64] y)%E =
  Papp2 (Omod Unsigned (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal (x %s[U64] y)%E =
  Papp2 (Omod Signed (Op_w U64)) (Pvar x) (Pvar y). done. Qed.

Goal (x ==[U64] y)%E =
  Papp2 (Oeq (Op_w U64)) (Pvar x) (Pvar y). done. Qed.
Goal (3 !=[i] 4)%E =
  Papp2 (Oneq Op_int) (Pconst 3) (Pconst 4). done. Qed.
Goal (1 <[i] 2)%E =
  Papp2 (Olt Cmp_int) (Pconst 1) (Pconst 2). done. Qed.
Goal (x <s[U64] y)%E =
  Papp2 (Olt (Cmp_w Signed U64)) (Pvar x) (Pvar y). done. Qed.
Goal (1 <=[i] 2)%E =
  Papp2 (Ole Cmp_int) (Pconst 1) (Pconst 2). done. Qed.
Goal (x <=s[U64] y)%E =
  Papp2 (Ole (Cmp_w Signed U64)) (Pvar x) (Pvar y). done. Qed.
Goal (b ==[b] b)%E = Papp2 Obeq (Pvar b) (Pvar b). done. Qed.

Goal (ite[b](b, x, y))%E =
  Pif abool (Pvar b) (Pvar x) (Pvar y). done. Qed.
Goal (ite[i](b, x, y))%E =
  Pif aint (Pvar b) (Pvar x) (Pvar y). done. Qed.
Goal (ite[U32](true, x &[U32] y, z))%E =
  Pif (aword U32) (Pbool true)
    (Papp2 (Oland U32) (Pvar x) (Pvar y)) (Pvar z).
done. Qed.
Goal (ite[U64](b, x, y))%E =
  Pif (aword U64) (Pvar b) (Pvar x) (Pvar y). done. Qed.

Goal (b &&[b] x <=u[U64] y)%E =
  Papp2 Oand (Pvar b)
    (Papp2 (Ole (Cmp_w Unsigned U64)) (Pvar x) (Pvar y)).
done. Qed.
Goal (x !=[U64] y ||[b] x <u[U64] y)%E =
  Papp2 Oor
    (Papp2 (Oneq (Op_w U64)) (Pvar x) (Pvar y))
    (Papp2 (Olt (Cmp_w Unsigned U64)) (Pvar x) (Pvar y)).
done. Qed.
Goal (true ||[b] false &&[b] 1 -[i] 10 ==[i] false)%E =
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

Goal (x *[U128] y)%E =
  Papp2 (Omul (Op_w U128)) (Pvar x) (Pvar y). done. Qed.
Goal (x *[U256] y)%E =
  Papp2 (Omul (Op_w U256)) (Pvar x) (Pvar y). done. Qed.

Goal (sget[U64](x, 4, 0))%E =
  Psub AAscale U64 4 x (Pconst 0). done. Qed.

Goal (x >[i] y)%E =
  Papp2 (Ogt Cmp_int) (Pvar x) (Pvar y). done. Qed.
Goal (x >u[U64] y)%E =
  Papp2 (Ogt (Cmp_w Unsigned U64)) (Pvar x) (Pvar y). done. Qed.
Goal (x >s[U64] y)%E =
  Papp2 (Ogt (Cmp_w Signed U64)) (Pvar x) (Pvar y). done. Qed.
Goal (x >=[i] y)%E =
  Papp2 (Oge Cmp_int) (Pvar x) (Pvar y). done. Qed.
Goal (x >=u[U64] y)%E =
  Papp2 (Oge (Cmp_w Unsigned U64)) (Pvar x) (Pvar y). done. Qed.
Goal (x >=s[U64] y)%E =
  Papp2 (Oge (Cmp_w Signed U64)) (Pvar x) (Pvar y). done. Qed.

Goal (mget[U8](x))%E = Pload Unaligned U8 (Pvar x). done. Qed.
Goal (mget[U16](x))%E = Pload Unaligned U16 (Pvar x). done. Qed.
Goal (mget[U32](x))%E = Pload Unaligned U32 (Pvar x). done. Qed.
Goal (mget[U128](x))%E = Pload Unaligned U128 (Pvar x). done. Qed.
Goal (mget[U256](x))%E = Pload Unaligned U256 (Pvar x). done. Qed.
Goal (mget[U64](x +[U64] y))%E =
  Pload Unaligned U64
    (Papp2 (Oadd (Op_w U64)) (Pvar x) (Pvar y)).
done. Qed.

Goal (aget[U8](x, 0))%E =
  Pget Aligned AAscale U8 x (Pconst 0). done. Qed.
Goal (aget[U32](x, 0))%E =
  Pget Aligned AAscale U32 x (Pconst 0). done. Qed.
Goal (aget[U64](x, y))%E =
  Pget Aligned AAscale U64 x (Pvar y). done. Qed.
Goal (aget[U64](x, y +[U64] 1))%E =
  Pget Aligned AAscale U64 x
    (Papp2 (Oadd (Op_w U64)) (Pvar y) (Pconst 1)).
done. Qed.

Goal (i2ui[U64] 42)%E =
  Papp1 (Owi1 Unsigned (WIwint_of_int U64)) (Pconst 42). done. Qed.
Goal (i2si[U32] 0)%E =
  Papp1 (Owi1 Signed (WIwint_of_int U32)) (Pconst 0). done. Qed.
Goal (ui2i[U64] x)%E =
  Papp1 (Owi1 Unsigned (WIint_of_wint U64)) (Pvar x). done. Qed.
Goal (si2i[U32] x)%E =
  Papp1 (Owi1 Signed (WIint_of_wint U32)) (Pvar x). done. Qed.
Goal (ui2w[U64] x)%E =
  Papp1 (Owi1 Unsigned (WIword_of_wint U64)) (Pvar x). done. Qed.
Goal (si2w[U32] x)%E =
  Papp1 (Owi1 Signed (WIword_of_wint U32)) (Pvar x). done. Qed.
Goal (w2ui[U64] x)%E =
  Papp1 (Owi1 Unsigned (WIwint_of_word U64)) (Pvar x). done. Qed.
Goal (w2si[U32] x)%E =
  Papp1 (Owi1 Signed (WIwint_of_word U32)) (Pvar x). done. Qed.
Goal (uiext[U32, U64] x)%E =
  Papp1 (Owi1 Unsigned (WIwint_ext U64 U32)) (Pvar x). done. Qed.
Goal (siext[U32, U64] x)%E =
  Papp1 (Owi1 Signed (WIwint_ext U64 U32)) (Pvar x). done. Qed.
Goal (-ui[U64] x)%E =
  Papp1 (Owi1 Unsigned (WIneg U64)) (Pvar x). done. Qed.
Goal (-si[U32] x)%E =
  Papp1 (Owi1 Signed (WIneg U32)) (Pvar x). done. Qed.

Goal (x +ui[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIadd) (Pvar x) (Pvar y). done. Qed.
Goal (x +si[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIadd) (Pvar x) (Pvar y). done. Qed.
Goal (x -ui[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIsub) (Pvar x) (Pvar y). done. Qed.
Goal (x -si[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIsub) (Pvar x) (Pvar y). done. Qed.
Goal (x *ui[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WImul) (Pvar x) (Pvar y). done. Qed.
Goal (x *si[U32] y)%E =
  Papp2 (Owi2 Signed U32 WImul) (Pvar x) (Pvar y). done. Qed.
Goal (x /ui[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIdiv) (Pvar x) (Pvar y). done. Qed.
Goal (x /si[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIdiv) (Pvar x) (Pvar y). done. Qed.
Goal (x %ui[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WImod) (Pvar x) (Pvar y). done. Qed.
Goal (x %si[U32] y)%E =
  Papp2 (Owi2 Signed U32 WImod) (Pvar x) (Pvar y). done. Qed.
Goal (x <<ui[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIshl) (Pvar x) (Pvar y). done. Qed.
Goal (x <<si[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIshl) (Pvar x) (Pvar y). done. Qed.
Goal (x >>ui[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIshr) (Pvar x) (Pvar y). done. Qed.
Goal (x >>si[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIshr) (Pvar x) (Pvar y). done. Qed.
Goal (x ==ui[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIeq) (Pvar x) (Pvar y). done. Qed.
Goal (x ==si[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIeq) (Pvar x) (Pvar y). done. Qed.
Goal (x !=ui[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIneq) (Pvar x) (Pvar y). done. Qed.
Goal (x !=si[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIneq) (Pvar x) (Pvar y). done. Qed.
Goal (x <ui[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIlt) (Pvar x) (Pvar y). done. Qed.
Goal (x <si[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIlt) (Pvar x) (Pvar y). done. Qed.
Goal (x <=ui[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIle) (Pvar x) (Pvar y). done. Qed.
Goal (x <=si[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIle) (Pvar x) (Pvar y). done. Qed.
Goal (x >ui[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIgt) (Pvar x) (Pvar y). done. Qed.
Goal (x >si[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIgt) (Pvar x) (Pvar y). done. Qed.
Goal (x >=ui[U64] y)%E =
  Papp2 (Owi2 Unsigned U64 WIge) (Pvar x) (Pvar y). done. Qed.
Goal (x >=si[U32] y)%E =
  Papp2 (Owi2 Signed U32 WIge) (Pvar x) (Pvar y). done. Qed.

Goal (42 +[U64] x)%E =
  Papp2 (Oadd (Op_w U64)) (Pconst 42) (Pvar x). done. Qed.

Goal (10 /u[i] 3)%E =
  Papp2 (Odiv Unsigned Op_int) (Pconst 10) (Pconst 3). done. Qed.
Goal (10 /s[i] 3)%E =
  Papp2 (Odiv Signed Op_int) (Pconst 10) (Pconst 3). done. Qed.
Goal (10 %u[i] 3)%E =
  Papp2 (Omod Unsigned Op_int) (Pconst 10) (Pconst 3). done. Qed.
Goal (10 %s[i] 3)%E =
  Papp2 (Omod Signed Op_int) (Pconst 10) (Pconst 3). done. Qed.

End ExprTests.
