
From Coq Require Import ZArith.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.

Require Import expr.
Require Import expr_notations lval_notations.

(** * Display notations for Jasmin instructions

    Wrap an [instr] in [cmd:( i )] to view it in Jasmin-like syntax.
    Each notation wraps [instr_r] in [MkI dummy_instr_info].

    Notation summary:
      - lv :=[b] e            = bool assignment
      - lv :=[i] e            = int assignment
      - lv :=[ ws ] e      = word assignment
      - lv :=[ ws , n ] e  = array assignment
      - lv := randombytes[ ws , n ]( e )
                            = random-bytes syscall (one input, one output)
      - if ( e ) { c1 } else { c2 } = conditional (Cif)
      - if ( e ) { c }              = conditional with empty else branch
      - for v = lo to hi do { c }     = upward for loop (Cfor, UpTo)
      - for v = hi downto lo do { c } = downward for loop (Cfor, DownTo)
      - while { c1 } ( e ) { c2 }   = while loop (Cwhile Align)
      - skip                         = empty command ([::])
      - i1 ;; i2 ;; ... ;; skip     = instruction sequence (cmd)
      - [;; ]                        = empty command (same as [skip])
      - [;; i]                       = single-instruction program
      - [;; i1; i2; ...; in]         = instruction sequence (no trailing skip)
      - call [:: lv1; ...; lvn] := f ( [:: e1; ...; em] )
                                   = function call (Ccall)

    Individual instruction notations produce [instr]; use [;;] to build
    a [cmd] from a sequence.  Terminate every sequence with [skip].
    Example: [x :=[i] #0 ;; y :=[U64] x ;; skip].
    To embed an arbitrary [cmd], use [rocq:( ... )].

    List-style sequence notation mirrors [:: ...] from MathComp seq and
    avoids the trailing [skip].  The [;;] tag distinguishes it from the
    constr-level [:: ...] seq notation:
      [;; ]               = empty sequence (same as skip)
      [;; i]              = one-instruction sequence
      [;; i1; i2; ..; in] = multi-instruction sequence
    These can appear anywhere a [cmd] is expected, including inside
    if/for/while bodies.

    Function call notation uses two auxiliary custom entries, [lval_list]
    and [expr_list], whose elements are parsed in the [lval] and [expr]
    entries respectively.  These entries carry proper [:: ...] MathComp-
    style list syntax without the ambiguity present at the [cmd] level:
      [lval_list]:  [ :: ]  /  [ :: lv ]  /  [ :: lv1; lv2; ..; lvj ]
      [expr_list]:  [ :: ]  /  [ :: e ]   /  [ :: e1; e2; ..; ej ]
    The call notation starts with the keyword [call] to avoid the cmd-
    level parser committing to an assignment path before seeing [:=]:
      call [:: lv1; ..; lvn] := f ( [:: e1; ..; em] )

    Not supported:
      - [Copn lvs t o es]         : assembly-operation instructions
      - [Cassert (l, e)]          : assertions
      - [Csyscall] with other than one input and one output, or with a
        syscall other than [RandomBytes]
      - [Cwhile NoAlign c1 e ii c2]: only [Cwhile Align] is covered
      - [Cassgn lv t ty e] with [t] other than [AT_none]
      - The [instr_info] field is always [dummy_instr_info]

    In if/for/while bodies write sequences as [i1 ;; i2 ;; ... ;; skip]
    or as [[;; i1; i2; ...; in]]; use [rocq:( ... )] to embed arbitrary
    [cmd] terms.
*)

Declare Custom Entry cmd.

Notation "cmd:( c )" := c
  (c custom cmd at level 99, only parsing).

Notation "rocq:( e )" := e
  (in custom cmd at level 0, e constr at level 99).

Notation "lv  :=[b]  e" :=
  (MkI dummy_instr_info (Cassgn lv AT_none abool e))
  (in custom cmd at level 90,
   lv custom lval at level 99, e custom expr at level 99).

Notation "lv :=[i]  e" :=
  (MkI dummy_instr_info (Cassgn lv AT_none aint e))
  (in custom cmd at level 90,
   lv custom lval at level 99, e custom expr at level 99).

Notation "lv  :=[  ws  ]  e" :=
  (MkI dummy_instr_info (Cassgn lv AT_none (aword ws) e))
  (in custom cmd at level 90,
   ws constr at level 0,
   lv custom lval at level 99, e custom expr at level 99).

Notation "lv  :=[  ws , n  ]  e" :=
  (MkI dummy_instr_info (Cassgn lv AT_none (aarr ws n) e))
  (in custom cmd at level 90,
   ws constr at level 0, n constr at level 0,
   lv custom lval at level 99, e custom expr at level 99).

Notation "lv  :=  randombytes[ ws , n ]( e )" :=
  (MkI dummy_instr_info (Csyscall [:: lv] (RandomBytes ws n) [:: e]))
  (in custom cmd at level 90,
   ws constr at level 0, n constr at level 0,
   lv custom lval at level 99, e custom expr at level 99).

Notation "'if' '(' e ')' '{' c1 '}' 'else' '{' c2 '}'" :=
  (MkI dummy_instr_info (Cif e c1 c2))
  (in custom cmd at level 90,
   e custom expr at level 99,
   c1 custom cmd at level 99, c2 custom cmd at level 99,
   format "'if'  '('  e  ')'  '{'  c1  '}'  'else'  '{'  c2  '}'").

Notation "'if' '(' e ')' '{' c '}'" :=
  (MkI dummy_instr_info (Cif e c [::]))
  (in custom cmd at level 90,
   e custom expr at level 99,
   c custom cmd at level 99,
   format "'if'  '('  e  ')'  '{'  c  '}'").

Notation "'for' v '=' lo 'to' hi 'do' '{' c '}'" :=
  (MkI dummy_instr_info (Cfor v.(gv) (UpTo, lo, hi) c))
  (in custom cmd at level 90,
   v constr at level 0,
   lo custom expr at level 99, hi custom expr at level 99,
   c custom cmd at level 99,
   format "'for'  v  '='  lo  'to'  hi  'do'  '{'  c  '}'").

Notation "'for' v '=' hi 'downto' lo 'do' '{' c '}'" :=
  (MkI dummy_instr_info (Cfor v.(gv) (DownTo, lo, hi) c))
  (in custom cmd at level 90,
   v constr at level 0,
   hi custom expr at level 99, lo custom expr at level 99,
   c custom cmd at level 99,
   format "'for'  v  '='  hi  'downto'  lo  'do'  '{'  c  '}'").

Notation "'while' '{' c1 '}' '(' e ')' '{' c2 '}'" :=
  (MkI dummy_instr_info (Cwhile Align c1 e dummy_instr_info c2))
  (in custom cmd at level 90,
   c1 custom cmd at level 99,
   e custom expr at level 99,
   c2 custom cmd at level 99,
   format "'while'  '{'  c1  '}'  '('  e  ')'  '{'  c2  '}'").

Notation "'skip'" := ([::] : cmd)
  (in custom cmd at level 90).

Notation "i ;; c" := (i :: c)
  (in custom cmd at level 95,
   c custom cmd at level 95,
   right associativity).

(* Fresh custom entries for lval/pexpr lists in call arguments.
   Declared here (not in lval_notations/expr_notations) so they live
   alongside the call notation.  Using [:: ...] is safe because these
   entries carry no "x constr at level 0" variable notation that would
   greedily consume a MathComp seq literal. *)

Declare Custom Entry lval_list.
Declare Custom Entry expr_list.

Notation "[ :: ]" := ([::] : lvals)
  (in custom lval_list at level 0).

Notation "[ :: lv ]" := [:: lv]
  (in custom lval_list at level 0,
   lv custom lval at level 99).

Notation "[ :: lv1 ; lv2 ; .. ; lvj ]" := (lv1 :: lv2 :: .. [:: lvj] ..)
  (in custom lval_list at level 0,
   lv1 custom lval at level 99,
   lv2 custom lval at level 99,
   lvj custom lval at level 99).

Notation "[ :: ]" := ([::] : pexprs)
  (in custom expr_list at level 0).

Notation "[ :: e ]" := [:: e]
  (in custom expr_list at level 0,
   e custom expr at level 99).

Notation "[ :: e1 ; e2 ; .. ; ej ]" := (e1 :: e2 :: .. [:: ej] ..)
  (in custom expr_list at level 0,
   e1 custom expr at level 99,
   e2 custom expr at level 99,
   ej custom expr at level 99).

Notation "'call' lvl ':=' f '(' el ')'" :=
  (MkI dummy_instr_info (Ccall lvl f el))
  (in custom cmd at level 90,
   lvl custom lval_list at level 99,
   f constr at level 0,
   el custom expr_list at level 99).

(* Constr-level only-printing notations so instr terms display with these
   notations directly in the proof state, without [cmd:(...)]. *)

Notation "lv  :=[b]  e" :=
  (MkI dummy_instr_info (Cassgn lv AT_none abool e))
  (only printing, at level 90,
   lv custom lval at level 99, e custom expr at level 99).

Notation "lv :=[i]  e" :=
  (MkI dummy_instr_info (Cassgn lv AT_none aint e))
  (only printing, at level 90,
   lv custom lval at level 99, e custom expr at level 99).

Notation "lv  :=[  ws  ]  e" :=
  (MkI dummy_instr_info (Cassgn lv AT_none (aword ws) e))
  (only printing, at level 90,
   ws constr at level 0,
   lv custom lval at level 99, e custom expr at level 99).

Notation "lv  :=[  ws , n  ]  e" :=
  (MkI dummy_instr_info (Cassgn lv AT_none (aarr ws n) e))
  (only printing, at level 90,
   ws constr at level 0, n constr at level 0,
   lv custom lval at level 99, e custom expr at level 99).

Notation "lv  :=  randombytes[ ws , n ]( e )" :=
  (MkI dummy_instr_info (Csyscall [:: lv] (RandomBytes ws n) [:: e]))
  (only printing, at level 90,
   ws constr at level 0, n constr at level 0,
   lv custom lval at level 99, e custom expr at level 99).

Notation "'if' '(' e ')' '{' c1 '}' 'else' '{' c2 '}'" :=
  (MkI dummy_instr_info (Cif e c1 c2))
  (only printing, at level 90,
   e custom expr at level 99,
   c1 custom cmd at level 99, c2 custom cmd at level 99,
   format "'if'  '('  e  ')'  '{'  c1  '}'  'else'  '{'  c2  '}'").

Notation "'if' '(' e ')' '{' c '}'" :=
  (MkI dummy_instr_info (Cif e c [::]))
  (only printing, at level 90,
   e custom expr at level 99,
   c custom cmd at level 99,
   format "'if'  '('  e  ')'  '{'  c  '}'").

Notation "'for' v '=' lo 'to' hi 'do' '{' c '}'" :=
  (MkI dummy_instr_info (Cfor v.(gv) (UpTo, lo, hi) c))
  (only printing, at level 90,
   v constr at level 0,
   lo custom expr at level 99, hi custom expr at level 99,
   c custom cmd at level 99,
   format "'for'  v  '='  lo  'to'  hi  'do'  '{'  c  '}'").

Notation "'for' v '=' hi 'downto' lo 'do' '{' c '}'" :=
  (MkI dummy_instr_info (Cfor v.(gv) (DownTo, lo, hi) c))
  (only printing, at level 90,
   v constr at level 0,
   hi custom expr at level 99, lo custom expr at level 99,
   c custom cmd at level 99,
   format "'for'  v  '='  hi  'downto'  lo  'do'  '{'  c  '}'").

Notation "'while' '{' c1 '}' '(' e ')' '{' c2 '}'" :=
  (MkI dummy_instr_info (Cwhile Align c1 e dummy_instr_info c2))
  (only printing, at level 90,
   c1 custom cmd at level 99,
   e custom expr at level 99,
   c2 custom cmd at level 99,
   format "'while'  '{'  c1  '}'  '('  e  ')'  '{'  c2  '}'").

Notation "'skip'" := ([::] : cmd)
  (only printing, at level 90).

Notation "i ;; c" := (i :: c : cmd)
  (only printing, at level 95, right associativity).

Notation "'call' lvl ':=' f '(' el ')'" :=
  (MkI dummy_instr_info (Ccall lvl f el))
  (only printing, at level 90,
   lvl custom lval_list at level 99,
   f constr at level 0,
   el custom expr_list at level 99).

Section CmdTests.

Context
  {asm_op: Type}
  {asmop : asmOp asm_op}
.

Context (x y : gvar).
Context (f : funname).

Goal cmd:( x :=[b]#1 ==i #1 ) =
  MkI dummy_instr_info
    (Cassgn (Lvar x.(gv)) AT_none abool
      (Papp2 (Oeq Op_int) (Pconst 1) (Pconst 1))).
done. Qed.

Goal cmd:( x :=[i] #42 ) =
  MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 42)).
done. Qed.

Goal cmd:( x :=[U64] x ) =
  MkI dummy_instr_info
    (Cassgn (Lvar x.(gv)) AT_none (aword U64) (Pvar x)).
done. Qed.

Goal cmd:( x :=[U64] x +64u #1 ) =
  MkI dummy_instr_info
    (Cassgn (Lvar x.(gv)) AT_none (aword U64)
      (Papp2 (Oadd (Op_w U64)) (Pvar x) (Pconst 1))).
done. Qed.

Goal cmd:( aset[U64](x, #0) :=[U64, 4] x ) =
  MkI dummy_instr_info
    (Cassgn (Laset Aligned AAscale U64 x.(gv) (Pconst 0))
      AT_none (aarr U64 4) (Pvar x)).
done. Qed.

Goal cmd:( aset[U64](x, #0) := randombytes[U64, 4](x) ) =
  MkI dummy_instr_info
    (Csyscall [:: Laset Aligned AAscale U64 x.(gv) (Pconst 0)]
      (RandomBytes U64 4) [:: Pvar x]).
done. Qed.

Goal cmd:( if (x ==i y) { skip } else { skip } ) =
  MkI dummy_instr_info
    (Cif (Papp2 (Oeq Op_int) (Pvar x) (Pvar y)) [::] [::]).
done. Qed.

Goal cmd:( if (x <i y) { skip } ) =
  MkI dummy_instr_info
    (Cif (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y)) [::] [::]).
done. Qed.

Goal cmd:( for x = #0 to #10 do { skip } ) =
  MkI dummy_instr_info (Cfor x.(gv) (UpTo, Pconst 0, Pconst 10) [::]).
done. Qed.

Goal cmd:( for x = #10 downto #0 do { skip } ) =
  MkI dummy_instr_info (Cfor x.(gv) (DownTo, Pconst 0, Pconst 10) [::]).
done. Qed.

Goal cmd:( while { skip } ( x <i y ) { skip } ) =
  MkI dummy_instr_info
    (Cwhile Align [::] (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y))
      dummy_instr_info [::]).
done. Qed.

Goal cmd:( x :=[i] #0 ;; skip ) =
  [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0))].
done. Qed.

Goal cmd:( x :=[i] #0 ;; y :=[i] #1 ;; skip ) =
  [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0));
      MkI dummy_instr_info (Cassgn (Lvar y.(gv)) AT_none aint (Pconst 1))].
done. Qed.

Goal cmd:( x :=[U64] y ;; y :=[U64] x ;; skip ) =
  [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none (aword U64) (Pvar y));
      MkI dummy_instr_info (Cassgn (Lvar y.(gv)) AT_none (aword U64) (Pvar x))].
done. Qed.

Goal cmd:( if (x <i y) { x :=[i] #0 ;; skip } ) =
  MkI dummy_instr_info
    (Cif (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y))
      [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0))]
      [::]).
done. Qed.

Goal cmd:( while { x :=[i] #0 ;; skip } ( x <i y ) { y :=[i] #1 ;; skip } ) =
  MkI dummy_instr_info
    (Cwhile Align
      [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0))]
      (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y))
      dummy_instr_info
      [:: MkI dummy_instr_info (Cassgn (Lvar y.(gv)) AT_none aint (Pconst 1))]).
done. Qed.

Goal cmd:( if (x <i y) { x :=[i] #0 ;; skip } ) =
  MkI dummy_instr_info
    (Cif (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y))
      [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0))]
      [::]).
done. Qed.

Goal cmd:( while { x :=[i] #0 ;; skip } ( x <i y ) { y :=[i] #1 ;; skip } ) =
  MkI dummy_instr_info
    (Cwhile Align
      [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0))]
      (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y))
      dummy_instr_info
      [:: MkI dummy_instr_info (Cassgn (Lvar y.(gv)) AT_none aint (Pconst 1))]).
done. Qed.

Goal cmd:( call [:: ] := f ( [:: ] ) ) =
  MkI dummy_instr_info (Ccall [::] f [::]).
done. Qed.

Goal cmd:( call [:: x ] := f ( [:: #0 ] ) ) =
  MkI dummy_instr_info (Ccall [:: Lvar x.(gv)] f [:: Pconst 0]).
done. Qed.

Goal cmd:( call [:: x ; y ] := f ( [:: x ; y ] ) ) =
  MkI dummy_instr_info
    (Ccall [:: Lvar x.(gv); Lvar y.(gv)] f [:: Pvar x; Pvar y]).
done. Qed.

Goal cmd:( call [:: x ] := f ( [:: x +64u #1 ; y ] ) ) =
  MkI dummy_instr_info
    (Ccall [:: Lvar x.(gv)] f
      [:: Papp2 (Oadd (Op_w U64)) (Pvar x) (Pconst 1); Pvar y]).
done. Qed.

Goal cmd:( call [:: aset[U64](x, #0) ] := f ( [:: x ] ) ) =
  MkI dummy_instr_info
    (Ccall [:: Laset Aligned AAscale U64 x.(gv) (Pconst 0)] f [:: Pvar x]).
done. Qed.

End CmdTests.
