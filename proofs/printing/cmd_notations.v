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

* Assembly operations (level 90, no associativity)

  - [Opn lvs := o es]           base assembly operation            (Copn)
    [o] is the [asm_op] operation.
    In [es], bare [gvar] values must be wrapped: [Pvar x].
    In [lvs], bare [gvar] values must be wrapped: [Lvar x].

  - [OpnE lvs := o es]          extended assembly operation        (Copn)
    [o] is the [extra_op] operation.
    In [es], bare [gvar] values must be wrapped: [Pvar x].
    In [lvs], bare [gvar] values must be wrapped: [Lvar x].

* Syscalls (level 90, no associativity)

  - [lv := randombytes[ws, n](e)]    [RandomBytes ws n] syscall, one input [e],
                                     one output [lv]

* Conditionals (level 90, no associativity)

  - [If (e) c1 Else c2 fi]      if-then-else              (Cif)
  - [IfT (e) c fi]              if-then (empty else)

* Loops (level 90, no associativity)

  - [For (v = lo to hi) c od]      upward for loop             (Cfor UpTo)
  - [For (v = hi downto lo) c od]   downward for loop           (Cfor DownTo)
  - [While (e) c od]               while loop, empty first body   (Cwhile Align)
  - [While2 c1 (e) c2 od]          while loop, aligned            (Cwhile Align)

* Function call (level 90, no associativity)

  - [Call lvs := f es]            function call             (Ccall)
    In [es], bare [gvar] values must be wrapped: [Pvar x].
    In [lvs], bare [gvar] values must be wrapped: [Lvar x].

* Assertions (Cassert, level 90, no associativity)

  - [Assert l a]                  assert: label [l], assertion [a]    (Cassert)
    [a] is an [eassert]: [Pexpr e], [PappN_safety op es], [Pis_var_init v],
    [Pis_mem_init e1 e2], or [Pand a1 a2].

* Command sequences

  - [skip]                        empty sequence            ([::])
  - [<{ i }>]                     single instruction        ([:: i])
  - [<{ i1 ; i2 ; .. ; iN }>]     instruction sequence
                                  (i1 :: i2 :: .. [:: iN] ..)

* Not supported

  - [Csyscall]                    with a syscall other than [RandomBytes], or
                                  with more than one input or output
  - [Cwhile NoAlign c1 e ii c2]   only [Cwhile Align] is covered
  - [Cassgn lv t ty e] with [t]   other than [AT_none]
  - The [instr_info] field is always [dummy_instr_info] *)

From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import arch_decl arch_extra expr.
Require Import expr_notations lval_notations.

Declare Scope jcmd_scope.
Delimit Scope jcmd_scope with C.
Bind Scope jcmd_scope with instr.
Bind Scope jcmd_scope with cmd.

Notation "lv :=[b] e" :=
  (MkI dummy_instr_info (Cassgn lv%L AT_none abool e%E))
  (at level 90, e at level 99,
   format "'[hv' lv  :=[b]  e ']'") : jcmd_scope.

Notation "lv :=[i] e" :=
  (MkI dummy_instr_info (Cassgn lv%L AT_none aint e%E))
  (at level 90, e at level 99,
   format "'[hv' lv  :=[i]  e ']'") : jcmd_scope.

Notation "lv :=[ ws ] e" :=
  (MkI dummy_instr_info (Cassgn lv%L AT_none (aword ws) e%E))
  (at level 90, ws constr at level 0, e at level 99,
   format "'[hv' lv  :=[ ws ]  e ']'") : jcmd_scope.

Notation "lv :=[ ws , n ] e" :=
  (MkI dummy_instr_info (Cassgn lv%L AT_none (aarr ws n) e%E))
  (at level 90, ws constr at level 0, n constr at level 0,
   e at level 99,
   format "'[hv' lv  :=[ ws ,  n ]  e ']'") : jcmd_scope.

Notation "'Opn' lvs ':=' o es" :=
  (MkI dummy_instr_info (Copn lvs%L AT_none (Oasm (BaseOp (None, o))) es%E))
  (at level 90, lvs at level 99,
   o constr at level 0, es at level 99,
   format "'[hv' 'Opn'  lvs  ':='  o  es ']'") : jcmd_scope.

Notation "'OpnE' lvs ':=' o es" :=
  (MkI dummy_instr_info (Copn lvs%L AT_none (Oasm (ExtOp o)) es%E))
  (at level 90, lvs at level 99,
   o constr at level 0, es at level 99,
   format "'[hv' 'OpnE'  lvs  ':='  o  es ']'") : jcmd_scope.

Notation "lv := randombytes[ ws , n ]( e )" :=
  (MkI dummy_instr_info (Csyscall [:: lv%L] (RandomBytes ws n) [:: (e%E : pexpr)]))
  (at level 90, ws constr at level 0, n constr at level 0,
   e at level 99,
   format "'[hv' lv  :=  randombytes[ ws ,  n ]( e ) ']'") : jcmd_scope.

Notation "'If' '(' e ')' c1 'Else' c2 'fi'" :=
  (MkI dummy_instr_info (Cif e%E c1%C c2%C))
  (at level 90, e at level 99,
   c1 at level 99, c2 at level 99,
   format "'[hv' 'If'  '(' e ')' '/'   '[v' c1 ']' '/' 'Else' '/'   '[v' c2 ']'  'fi' ']'")
  : jcmd_scope.

Notation "'IfT' '(' e ')' c 'fi'" :=
  (MkI dummy_instr_info (Cif e%E c%C [::]))
  (at level 90, e at level 99, c at level 99,
   format "'[hv' 'IfT'  '(' e ')' '/'   '[v' c ']'  'fi' ']'") : jcmd_scope.

Notation "'For' '(' v '=' lo 'to' hi ')' c 'od'" :=
  (MkI dummy_instr_info (Cfor v.(gv) (UpTo, lo%E, hi%E) c%C))
  (at level 90, v constr at level 0,
   lo at level 99, hi at level 99, c at level 99,
   format "'[hv' 'For'  '(' v  '='  lo  'to'  hi ')' '/'   '[v' c ']'  'od' ']'")
  : jcmd_scope.

Notation "'For' '(' v '=' hi 'downto' lo ')' c 'od'" :=
  (MkI dummy_instr_info (Cfor v.(gv) (DownTo, lo%E, hi%E) c%C))
  (at level 90, v constr at level 0,
   hi at level 99, lo at level 99, c at level 99,
   format "'[hv' 'For'  '(' v  '='  hi  'downto'  lo ')' '/'   '[v' c ']'  'od' ']'")
  : jcmd_scope.

Notation "'While' '(' e ')' c 'od'" :=
  (MkI dummy_instr_info (Cwhile Align [::] e%E dummy_instr_info c%C))
  (at level 90, e at level 99, c at level 99,
   format "'[hv' 'While'  '(' e ')' '/'   '[v' c ']'  'od' ']'")
  : jcmd_scope.

Notation "'While2' c1 '(' e ')' c2 'od'" :=
  (MkI dummy_instr_info (Cwhile Align c1%C e%E dummy_instr_info c2%C))
  (at level 90, c1 at level 0, e at level 99, c2 at level 99,
   format "'[hv' 'While2' '/'   '[v' c1 ']' '/'  '(' e ')' '/'   '[v' c2 ']'  'od' ']'")
  : jcmd_scope.

Notation "'Call' lvs ':=' f es" :=
  (MkI dummy_instr_info (Ccall lvs%L f es%E))
  (at level 90, lvs at level 99,
   f constr at level 0, es at level 99,
   format "'[hv' 'Call'  lvs  ':='  f  es ']'") : jcmd_scope.

Notation "'Assert' l a" :=
  (MkI dummy_instr_info (Cassert (l%string, a)))
  (at level 90, l constr at level 0, a constr at level 0,
   format "'[hv' 'Assert'  l  a ']'") : jcmd_scope.

(* Differentiate parsing and printing to only trigger the printing for [cmd]
   (and not in, e.g., in the [pexprs] or [lvals] function calls). *)

Notation "'skip'" :=
  ([::])
  (at level 0, only parsing) : jcmd_scope.

Notation "'skip'" :=
  (nil (T := instr))
  (at level 0, only printing,
   format "skip") : jcmd_scope.

Notation "<{ i }>" :=
  [:: i]
  (at level 0, i at level 90, only parsing) : jcmd_scope.

Notation "<{ i }>" :=
  (cons (T := instr) i nil)
  (at level 0, i at level 90, only printing,
   format "<{  i  }>") : jcmd_scope.

Notation "<{ i1 ; i2 ; .. ; iN }>" :=
  (i1 :: i2 :: .. [:: iN] ..)
  (at level 0, i1 at level 90, i2 at level 90, iN at level 90,
   only parsing) : jcmd_scope.

Notation "<{ i1 ; i2 ; .. ; iN }>" :=
  (cons (T := instr) i1 (cons (T := instr) i2 ( .. (cons (T := instr) iN nil) ..)))
  (at level 0, i1 at level 90, i2 at level 90, iN at level 90,
   only printing,
   format "<{ '[v'  '/'  i1 ;  '/'  i2 ;  '/'  .. ;  '/'  iN ']' '/' }>") : jcmd_scope.

Section CmdTests.

Context
  {reg regx xreg rflag cond asm_op extra_op : Type}
  {asm_e : asm_extra reg regx xreg rflag cond asm_op extra_op}
.

Context
  (x y : gvar)
  (f : funname)
  (o : asm_op)
  (eo : extra_op)
.

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

Goal (If (x ==[i] y) skip Else skip fi)%C =
  MkI dummy_instr_info
    (Cif (Papp2 (Oeq Op_int) (Pvar x) (Pvar y)) [::] [::]).
done. Qed.

Goal (IfT (x <[i] y) skip fi)%C =
  MkI dummy_instr_info
    (Cif (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y)) [::] [::]).
done. Qed.

Goal (For (x = 0 to 10) skip od)%C =
  MkI dummy_instr_info (Cfor x.(gv) (UpTo, Pconst 0, Pconst 10) [::]).
done. Qed.

Goal (For (x = 10 downto 0) skip od)%C =
  MkI dummy_instr_info (Cfor x.(gv) (DownTo, Pconst 0, Pconst 10) [::]).
done. Qed.

Goal (While ( x <[i] y ) skip od)%C =
  MkI dummy_instr_info
    (Cwhile Align [::] (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y))
      dummy_instr_info [::]).
done. Qed.

Goal (While2 skip ( x <[i] y ) skip od)%C =
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

Goal (IfT (x <[i] y) <{ x :=[i] 0 }> fi)%C =
  MkI dummy_instr_info
    (Cif (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y))
      [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0))]
      [::]).
done. Qed.

Goal (While2 <{ x :=[i] 0 }> ( x <[i] y ) <{ y :=[i] 1 }> od)%C =
  MkI dummy_instr_info
    (Cwhile Align
      [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0))]
      (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y))
      dummy_instr_info
      [:: MkI dummy_instr_info (Cassgn (Lvar y.(gv)) AT_none aint (Pconst 1))]).
done. Qed.

Goal (Opn [::] := o [::])%C =
  MkI dummy_instr_info (Copn [::] AT_none (Oasm (BaseOp (None, o))) [::]).
done. Qed.

Goal (Opn [:: Lvar x ] := o [:: Pvar x])%C =
  MkI dummy_instr_info (Copn [:: Lvar x.(gv)] AT_none (Oasm (BaseOp (None, o))) [:: Pvar x]).
done. Qed.

Goal (Opn [:: Lvar x; Lvar y] :=
       o [:: Pvar x; Pvar y])%C =
  MkI dummy_instr_info
    (Copn [:: Lvar x.(gv); Lvar y.(gv)] AT_none (Oasm (BaseOp (None, o))) [:: Pvar x; Pvar y]).
done. Qed.

Goal (OpnE [::] := eo [::])%C =
  MkI dummy_instr_info (Copn [::] AT_none (Oasm (ExtOp eo)) [::]).
done. Qed.

Goal (OpnE [:: Lvar x] := eo [:: Pvar x])%C =
  MkI dummy_instr_info (Copn [:: Lvar x.(gv)] AT_none (Oasm (ExtOp eo)) [:: Pvar x]).
done. Qed.

Goal (OpnE [:: Lvar x; Lvar y] :=
       eo [:: Pvar x; Pvar y])%C =
  MkI dummy_instr_info
    (Copn [:: Lvar x.(gv); Lvar y.(gv)] AT_none (Oasm (ExtOp eo)) [:: Pvar x; Pvar y]).
done. Qed.

Goal (Call [::] := f [::])%C =
  MkI dummy_instr_info (Ccall [::] f [::]).
done. Qed.

Goal (Call [:: Lvar x] := f [:: Pconst 0])%C =
  MkI dummy_instr_info (Ccall [:: Lvar x.(gv)] f [:: Pconst 0]).
done. Qed.

Goal (Call [:: Lvar x; Lvar y] :=
       f [:: Pvar x; Pvar y])%C =
  MkI dummy_instr_info
    (Ccall [:: Lvar x.(gv); Lvar y.(gv)] f [:: Pvar x; Pvar y]).
done. Qed.

Goal (Call [:: Lvar x] := f [:: x +[U64] 1; Pvar y])%C =
  MkI dummy_instr_info
    (Ccall [:: Lvar x.(gv)] f
      [:: Papp2 (Oadd (Op_w U64)) (Pvar x) (Pconst 1); Pvar y]).
done. Qed.

Goal (Call [:: aset[U64](x, 0)] := f [:: Pvar x])%C =
  MkI dummy_instr_info
    (Ccall [:: Laset Aligned AAscale U64 x.(gv) (Pconst 0)] f [:: Pvar x]).
done. Qed.

Goal (Assert "foo" (Pexpr (x <[i] y)%E))%C =
  MkI dummy_instr_info (Cassert ("foo"%string, Pexpr (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y)))).
done. Qed.

Goal (Assert "bar" (Pand (Pexpr (x <[i] y)%E) (Pexpr (y <[i] 10)%E)))%C =
  MkI dummy_instr_info
    (Cassert ("bar"%string, Pand
      (Pexpr (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y)))
      (Pexpr (Papp2 (Olt Cmp_int) (Pvar y) (Pconst 10))))).
done. Qed.

Goal (skip)%C = ([::] : cmd). done. Qed.

End CmdTests.
