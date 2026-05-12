(* Display notations for Jasmin commands (scope [%C])

  Activate with [cmd%C] or [Open Scope jcmd_scope].
  Each notation wraps [instr_r] in [MkI dummy_instr_info].
  Expressions are parsed in scope [%E]; lvals in scope [%L].
  Sequences use [<{ ... }>] brackets.

* Assignments (Cassgn AT_none, level 90, no associativity)

  - [lv :=[b] e]               bool assignment
  - [lv :=[i] e]               int assignment
  - [lv :=[ws] e]              word [ws] assignment
  - [lv :=[ws, n] e]           array [ws × n] assignment

* Syscalls (level 90, no associativity)

  - [lv := randombytes[ws, n](e)]    [RandomBytes ws n] syscall, one input [e],
                                     one output [lv]

* Conditionals (level 90, no associativity)

  - [If (e) c1 Else c2]         if-then-else              (Cif)
  - [IfT (e) c]                 if-then (empty else)

* Loops (level 90, no associativity)

  - [For v = lo to hi do c]       upward for loop           (Cfor UpTo)
  - [For v = hi downto lo do c]   downward for loop         (Cfor DownTo)
  - [While c1 (e) c2]             while loop, aligned       (Cwhile Align)

* Function call (level 90, no associativity)

  - [Call lvs := f es]            function call             (Ccall)
    In [es], bare [gvar] values must be wrapped: [Pvar x].
    In [lvs], bare [gvar] values must be wrapped: [lvar_of_gvar x].

* Command sequences

  - [<{ }>]                       empty sequence            ([::])
  - [<{ i }>]                     single instruction        ([:: i])
  - [<{ i1 ; i2 ; .. ; in }>]     instruction sequence
                                  (i1 :: i2 :: .. [:: in] ..)

* Not supported

  - [Copn lvs t o es]             assembly-operation instructions
  - [Cassert (l, e)]              assertion
  - [Csyscall]                    with a syscall other than [RandomBytes], or
                                  with more than one input or output
  - [Cwhile NoAlign c1 e ii c2]   only [Cwhile Align] is covered
  - [Cassgn lv t ty e] with [t]   other than [AT_none]
  - The [instr_info] field is always [dummy_instr_info] *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Stdlib Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr.
Require Import expr_notations lval_notations.

Declare Scope jcmd_scope.
Delimit Scope jcmd_scope with C.
Bind Scope jcmd_scope with instr.
Bind Scope jcmd_scope with cmd.

Notation "lv :=[b] e" :=
  (MkI dummy_instr_info (Cassgn lv%L AT_none abool e%E))
  (at level 90, e at level 99,
   format "lv  :=[b]  e") : jcmd_scope.

Notation "lv :=[i] e" :=
  (MkI dummy_instr_info (Cassgn lv%L AT_none aint e%E))
  (at level 90, e at level 99,
   format "lv  :=[i]  e") : jcmd_scope.

Notation "lv :=[ ws ] e" :=
  (MkI dummy_instr_info (Cassgn lv%L AT_none (aword ws) e%E))
  (at level 90, ws constr at level 0, e at level 99,
   format "lv  :=[ ws ]  e") : jcmd_scope.

Notation "lv :=[ ws , n ] e" :=
  (MkI dummy_instr_info (Cassgn lv%L AT_none (aarr ws n) e%E))
  (at level 90, ws constr at level 0, n constr at level 0,
   e at level 99,
   format "lv  :=[ ws ,  n ]  e") : jcmd_scope.

Notation "lv := randombytes[ ws , n ]( e )" :=
  (MkI dummy_instr_info (Csyscall [:: lv%L] (RandomBytes ws n) [:: (e%E : pexpr)]))
  (at level 90, ws constr at level 0, n constr at level 0,
   e at level 99,
   format "lv  :=  randombytes[ ws ,  n ]( e )") : jcmd_scope.

Notation "'If' '(' e ')' c1 'Else' c2" :=
  (MkI dummy_instr_info (Cif e%E c1%C c2%C))
  (at level 90, e at level 99,
   c1 at level 99, c2 at level 99,
   format "'[hv' 'If'  '(' e ')' '/'   '[v' c1 ']' '/' 'Else' '/'   '[v' c2 ']' ']'")
  : jcmd_scope.

Notation "'IfT' '(' e ')' c" :=
  (MkI dummy_instr_info (Cif e%E c%C [::]))
  (at level 90, e at level 99, c at level 99,
   format "'[hv' 'IfT'  '(' e ')' '/'  '[v' c ']' ']'") : jcmd_scope.

Notation "'For' v '=' lo 'to' hi 'do' c" :=
  (MkI dummy_instr_info (Cfor v.(gv) (UpTo, lo%E, hi%E) c%C))
  (at level 90, v constr at level 0,
   lo at level 99, hi at level 99, c at level 99,
   format "'[hv' 'For'  v  '='  lo  'to'  hi  'do' '/'  '[v' c ']' ']'")
  : jcmd_scope.

Notation "'For' v '=' hi 'downto' lo 'do' c" :=
  (MkI dummy_instr_info (Cfor v.(gv) (DownTo, lo%E, hi%E) c%C))
  (at level 90, v constr at level 0,
   hi at level 99, lo at level 99, c at level 99,
   format "'[hv' 'For'  v  '='  hi  'downto'  lo  'do' '/'  '[v' c ']' ']'")
  : jcmd_scope.

Notation "'While' c1 '(' e ')' c2" :=
  (MkI dummy_instr_info (Cwhile Align c1%C e%E dummy_instr_info c2%C))
  (at level 90, c1 at level 0, e at level 99, c2 at level 99,
   format "'[hv' 'While' '/'  '[v' c1 ']' '/'  '(' e ')' '/'  '[v' c2 ']' ']'")
  : jcmd_scope.

Notation "'Call' lvs ':=' f es" :=
  (MkI dummy_instr_info (Ccall lvs%L f es%E))
  (at level 90, lvs at level 99,
   f constr at level 0, es at level 99,
   format "'Call'  lvs  ':='  f  es") : jcmd_scope.

Notation "<{ }>" :=
  ([::])
  (at level 0, format "<{ }>") : jcmd_scope.

Notation "<{ i }>" :=
  [:: i]
  (at level 0, i at level 90,
   format "<{  i  }>") : jcmd_scope.

Notation "<{ i1 ; i2 ; .. ; xn }>" :=
  (i1 :: i2 :: .. [:: xn] ..)
  (at level 0, i1 at level 90, i2 at level 90, xn at level 90,
   format "<{ '[v'  '/'  i1 ;  '/'  i2 ;  '/'  .. ;  '/'  xn ']' '/' }>") : jcmd_scope.

Section CmdTests.

Context
  {asm_op: Type}
  {asmop : asmOp asm_op}
.

Context (x y : gvar).
Context (f : funname).

Goal (x :=[b] 1 ==[i] 1)%C =
  MkI dummy_instr_info
    (Cassgn (Lvar x.(gv)) AT_none abool
      (Papp2 (Oeq Op_int) (Pconst 1) (Pconst 1))).
done. Qed.

Goal (x :=[i] 42)%C =
  MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 42)).
done. Qed.

Goal (x :=[U64] x)%C =
  MkI dummy_instr_info
    (Cassgn (Lvar x.(gv)) AT_none (aword U64) (Pvar x)).
done. Qed.

Goal (x :=[U64] x +[U64] 1)%C =
  MkI dummy_instr_info
    (Cassgn (Lvar x.(gv)) AT_none (aword U64)
      (Papp2 (Oadd (Op_w U64)) (Pvar x) (Pconst 1))).
done. Qed.

Goal (aset[U64](x, 0) :=[U64, 4] x)%C =
  MkI dummy_instr_info
    (Cassgn (Laset Aligned AAscale U64 x.(gv) (Pconst 0))
      AT_none (aarr U64 4) (Pvar x)).
done. Qed.

Goal (aset[U64](x, 0) := randombytes[U64, 4](x))%C =
  MkI dummy_instr_info
    (Csyscall [:: Laset Aligned AAscale U64 x.(gv) (Pconst 0)]
      (RandomBytes U64 4) [:: Pvar x]).
done. Qed.

Goal (If (x ==[i] y) <{ }> Else <{ }>)%C =
  MkI dummy_instr_info
    (Cif (Papp2 (Oeq Op_int) (Pvar x) (Pvar y)) [::] [::]).
done. Qed.

Goal (IfT (x <[i] y) <{ }>)%C =
  MkI dummy_instr_info
    (Cif (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y)) [::] [::]).
done. Qed.

Goal (For x = 0 to 10 do <{ }>)%C =
  MkI dummy_instr_info (Cfor x.(gv) (UpTo, Pconst 0, Pconst 10) [::]).
done. Qed.

Goal (For x = 10 downto 0 do <{ }>)%C =
  MkI dummy_instr_info (Cfor x.(gv) (DownTo, Pconst 0, Pconst 10) [::]).
done. Qed.

Goal (While <{ }> ( x <[i] y ) <{ }>)%C =
  MkI dummy_instr_info
    (Cwhile Align [::] (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y))
      dummy_instr_info [::]).
done. Qed.

Goal (<{ x :=[i] 0 }>)%C =
  [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0))].
done. Qed.

Goal (<{ x :=[i] 0; y :=[i] 1 }>)%C =
  [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0));
      MkI dummy_instr_info (Cassgn (Lvar y.(gv)) AT_none aint (Pconst 1))].
done. Qed.

Goal (<{ x :=[U64] y; y :=[U64] x }>)%C =
  [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none (aword U64) (Pvar y));
      MkI dummy_instr_info (Cassgn (Lvar y.(gv)) AT_none (aword U64) (Pvar x))].
done. Qed.

Goal (IfT (x <[i] y) <{ x :=[i] 0 }>)%C =
  MkI dummy_instr_info
    (Cif (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y))
      [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0))]
      [::]).
done. Qed.

Goal (While <{ x :=[i] 0 }> ( x <[i] y ) <{ y :=[i] 1 }>)%C =
  MkI dummy_instr_info
    (Cwhile Align
      [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0))]
      (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y))
      dummy_instr_info
      [:: MkI dummy_instr_info (Cassgn (Lvar y.(gv)) AT_none aint (Pconst 1))]).
done. Qed.

Goal (Call [::] := f [::])%C =
  MkI dummy_instr_info (Ccall [::] f [::]).
done. Qed.

Goal (Call [:: lvar_of_gvar x] := f [:: Pconst 0])%C =
  MkI dummy_instr_info (Ccall [:: Lvar x.(gv)] f [:: Pconst 0]).
done. Qed.

Goal (Call [:: lvar_of_gvar x; lvar_of_gvar y] :=
       f [:: Pvar x; Pvar y])%C =
  MkI dummy_instr_info
    (Ccall [:: Lvar x.(gv); Lvar y.(gv)] f [:: Pvar x; Pvar y]).
done. Qed.

Goal (Call [:: lvar_of_gvar x] := f [:: x +[U64] 1; Pvar y])%C =
  MkI dummy_instr_info
    (Ccall [:: Lvar x.(gv)] f
      [:: Papp2 (Oadd (Op_w U64)) (Pvar x) (Pconst 1); Pvar y]).
done. Qed.

Goal (Call [:: aset[U64](x, 0)] := f [:: Pvar x])%C =
  MkI dummy_instr_info
    (Ccall [:: Laset Aligned AAscale U64 x.(gv) (Pconst 0)] f [:: Pvar x]).
done. Qed.

Goal (<{ }>)%C = ([::] : cmd). done. Qed.

End CmdTests.
