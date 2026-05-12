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

(* TODO
   1. Add a docstring at the top of the file with every notation explained. Give
   an exhaustive list of all the cases that are not supported by notations.
   Here's the previous one as inspiration (needs updating):


-(** * Display notations for Jasmin instructions
-
-    Wrap an [instr] in [cmd:( i )] to view it in Jasmin-like syntax.
-    Each notation wraps [instr_r] in [MkI dummy_instr_info].
-
-    Notation summary:
-      - lv :=[b] e            = bool assignment
-      - lv :=[i] e            = int assignment
-      - lv :=[ ws ] e      = word assignment
-      - lv :=[ ws , n ] e  = array assignment
-      - lv := randombytes[ ws , n ]( e )
-                            = random-bytes syscall (one input, one output)
-      - if ( e ) { c1 } else { c2 } = conditional (Cif)
-      - if ( e ) { c }              = conditional with empty else branch
-      - for v = lo to hi do { c }     = upward for loop (Cfor, UpTo)
-      - for v = hi downto lo do { c } = downward for loop (Cfor, DownTo)
-      - lv :=[ ws , n ] e  = array assignment
-      - lv := randombytes[ ws , n ]( e )
-                            = random-bytes syscall (one input, one output)
-      - if ( e ) { c1 } else { c2 } = conditional (Cif)
-      - if ( e ) { c }              = conditional with empty else branch
-      - for v = lo to hi do { c }     = upward for loop (Cfor, UpTo)
-      - for v = hi downto lo do { c } = downward for loop (Cfor, DownTo)
-      - while { c1 } ( e ) { c2 }   = while loop (Cwhile Align)
-      - skip                         = empty command ([::])
-      - i1 ;; i2 ;; ... ;; skip     = instruction sequence (cmd)
-      - [;; ]                        = empty command (same as [skip])
-      - [;; i]                       = single-instruction program
-      - [;; i1; i2; ...; in]         = instruction sequence (no trailing skip)
-      - call [:: lv1; ...; lvn] := f ( [:: e1; ...; em] )
-                                   = function call (Ccall)
-
-    Individual instruction notations produce [instr]; use [;;] to build
-    a [cmd] from a sequence.  Terminate every sequence with [skip].
-    Example: [x :=[i] #0 ;; y :=[U64] x ;; skip].
-    To embed an arbitrary [cmd], use [rocq:( ... )].
-
-    List-style sequence notation mirrors [:: ...] from MathComp seq and
-    avoids the trailing [skip].  The [;;] tag distinguishes it from the
-    constr-level [:: ...] seq notation:
-      [;; ]               = empty sequence (same as skip)
-      [;; i]              = one-instruction sequence
-      [;; i1; i2; ..; in] = multi-instruction sequence
-    These can appear anywhere a [cmd] is expected, including inside
-    if/for/while bodies.
-
-    Function call notation uses two auxiliary custom entries, [lval_list]
-    and [expr_list], whose elements are parsed in the [lval] and [expr]
-    entries respectively.  These entries carry proper [:: ...] MathComp-
-    style list syntax without the ambiguity present at the [cmd] level:
-      [lval_list]:  [ :: ]  /  [ :: lv ]  /  [ :: lv1; lv2; ..; lvj ]
-      [expr_list]:  [ :: ]  /  [ :: e ]   /  [ :: e1; e2; ..; ej ]
-    The call notation starts with the keyword [call] to avoid the cmd-
-    level parser committing to an assignment path before seeing [:=]:
-      call [:: lv1; ..; lvn] := f ( [:: e1; ..; em] )
-
-    Not supported:
-      - [Copn lvs t o es]         : assembly-operation instructions
-      - [Cassert (l, e)]          : assertions
-      - [Csyscall] with other than one input and one output, or with a
-        syscall other than [RandomBytes]
-      - [Cwhile NoAlign c1 e ii c2]: only [Cwhile Align] is covered
-      - [Cassgn lv t ty e] with [t] other than [AT_none]
-      - The [instr_info] field is always [dummy_instr_info]
-
-    In if/for/while bodies write sequences as [i1 ;; i2 ;; ... ;; skip]
-    or as [[;; i1; i2; ...; in]]; use [rocq:( ... )] to embed arbitrary
-    [cmd] terms.
-*)

  2. study the notations in @../../formosa-crypto.xhl/pwhile/notations.v and
  @../../formosa-crypto.xhl/pwhile.v . The notations for code in Jasmin should
  be similar: you should add `[v` boxes to if/for/while, keywords
  if/for/while/call should be capitalized, the if-then construction be called
  `IfT`. Then, introduce notations for sequencing as is done with `<< >>` , `<<
  i >>` and `<< ... ; ... >`.


 *)
(* Assignments (level 90, no associativity) *)

Notation "lv :=[b] e" :=
  (MkI dummy_instr_info (Cassgn lv%L AT_none abool e%E))
  (at level 90, e at level 99) : jcmd_scope.

Notation "lv :=[i] e" :=
  (MkI dummy_instr_info (Cassgn lv%L AT_none aint e%E))
  (at level 90, e at level 99) : jcmd_scope.

Notation "lv :=[ ws ] e" :=
  (MkI dummy_instr_info (Cassgn lv%L AT_none (aword ws) e%E))
  (at level 90, ws constr at level 0, e at level 99) : jcmd_scope.

Notation "lv :=[ ws , n ] e" :=
  (MkI dummy_instr_info (Cassgn lv%L AT_none (aarr ws n) e%E))
  (at level 90, ws constr at level 0, n constr at level 0,
   e at level 99) : jcmd_scope.

(* Random-bytes syscall *)

Notation "lv := randombytes[ ws , n ]( e )" :=
  (MkI dummy_instr_info (Csyscall [:: lv%L] (RandomBytes ws n) [:: (e%E : pexpr)]))
  (at level 90, ws constr at level 0, n constr at level 0,
   e at level 99) : jcmd_scope.

(* Conditionals *)

Notation "'if' '(' e ')' '{{' c1 '}}' 'else' '{{' c2 '}}'" :=
  (MkI dummy_instr_info (Cif e%E c1%C c2%C))
  (at level 90, e at level 99,
   c1 at level 99, c2 at level 99,
   format "'if'  '('  e  ')'  '{{'  c1  '}}'  'else'  '{{'  c2  '}}'")
  : jcmd_scope.

Notation "'if' '(' e ')' '{{' c '}}'" :=
  (MkI dummy_instr_info (Cif e%E c%C [::]))
  (at level 90, e at level 99, c at level 99,
   format "'if'  '('  e  ')'  '{{'  c  '}}'") : jcmd_scope.

(* For loops *)

Notation "'for' v '=' lo 'to' hi 'do' '{{' c '}}'" :=
  (MkI dummy_instr_info (Cfor v.(gv) (UpTo, lo%E, hi%E) c%C))
  (at level 90, v constr at level 0,
   lo at level 99, hi at level 99, c at level 99,
   format "'for'  v  '='  lo  'to'  hi  'do'  '{{'  c  '}}'")
  : jcmd_scope.

Notation "'for' v '=' hi 'downto' lo 'do' '{{' c '}}'" :=
  (MkI dummy_instr_info (Cfor v.(gv) (DownTo, lo%E, hi%E) c%C))
  (at level 90, v constr at level 0,
   hi at level 99, lo at level 99, c at level 99,
   format "'for'  v  '='  hi  'downto'  lo  'do'  '{{'  c  '}}'")
  : jcmd_scope.

(* While loops *)

Notation "'while' '{{' c1 '}}' '(' e ')' '{{' c2 '}}'" :=
  (MkI dummy_instr_info (Cwhile Align c1%C e%E dummy_instr_info c2%C))
  (at level 90, c1 at level 99, e at level 99, c2 at level 99,
   format "'while'  '{{'  c1  '}}'  '('  e  ')'  '{{'  c2  '}}'")
  : jcmd_scope.

(* Function call.
   In [pexprs] lists, bare gvar elements must be wrapped: [Pvar x].
   In [lvals] lists, bare gvar elements must be wrapped: [lvar_of_gvar]. *)

Notation "'call' lvs ':=' f '(' es ')'" :=
  (MkI dummy_instr_info (Ccall lvs%L f es%E))
  (at level 90, lvs at level 99,
   f constr at level 0, es at level 99) : jcmd_scope.

Section CmdTests.

Context
  {asm_op: Type}
  {asmop : asmOp asm_op}
.

Context (x y : gvar).
Context (f : funname).

Goal (x :=[b] 1 ==i 1)%C =
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

Goal (x :=[U64] x +64u 1)%C =
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

Goal (if (x ==i y) {{ [::] }} else {{ [::] }})%C =
  MkI dummy_instr_info
    (Cif (Papp2 (Oeq Op_int) (Pvar x) (Pvar y)) [::] [::]).
done. Qed.

Goal (if (x <i y) {{ [::] }})%C =
  MkI dummy_instr_info
    (Cif (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y)) [::] [::]).
done. Qed.

Goal (for x = 0 to 10 do {{ [::] }})%C =
  MkI dummy_instr_info (Cfor x.(gv) (UpTo, Pconst 0, Pconst 10) [::]).
done. Qed.

Goal (for x = 10 downto 0 do {{ [::] }})%C =
  MkI dummy_instr_info (Cfor x.(gv) (DownTo, Pconst 0, Pconst 10) [::]).
done. Qed.

Goal (while {{ [::] }} ( x <i y ) {{ [::] }})%C =
  MkI dummy_instr_info
    (Cwhile Align [::] (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y))
      dummy_instr_info [::]).
done. Qed.

Goal ([:: x :=[i] 0])%C =
  [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0))].
done. Qed.

Goal ([:: x :=[i] 0; y :=[i] 1])%C =
  [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0));
      MkI dummy_instr_info (Cassgn (Lvar y.(gv)) AT_none aint (Pconst 1))].
done. Qed.

Goal ([:: x :=[U64] y; y :=[U64] x])%C =
  [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none (aword U64) (Pvar y));
      MkI dummy_instr_info (Cassgn (Lvar y.(gv)) AT_none (aword U64) (Pvar x))].
done. Qed.

Goal (if (x <i y) {{ [:: x :=[i] 0] }})%C =
  MkI dummy_instr_info
    (Cif (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y))
      [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0))]
      [::]).
done. Qed.

Goal (while {{ [:: x :=[i] 0] }} ( x <i y ) {{ [:: y :=[i] 1] }})%C =
  MkI dummy_instr_info
    (Cwhile Align
      [:: MkI dummy_instr_info (Cassgn (Lvar x.(gv)) AT_none aint (Pconst 0))]
      (Papp2 (Olt Cmp_int) (Pvar x) (Pvar y))
      dummy_instr_info
      [:: MkI dummy_instr_info (Cassgn (Lvar y.(gv)) AT_none aint (Pconst 1))]).
done. Qed.

Goal (call [::] := f ( [::] ))%C =
  MkI dummy_instr_info (Ccall [::] f [::]).
done. Qed.

Goal (call [:: lvar_of_gvar x] := f ( [:: Pconst 0] ))%C =
  MkI dummy_instr_info (Ccall [:: Lvar x.(gv)] f [:: Pconst 0]).
done. Qed.

Goal (call [:: lvar_of_gvar x; lvar_of_gvar y] :=
       f ( [:: Pvar x; Pvar y] ))%C =
  MkI dummy_instr_info
    (Ccall [:: Lvar x.(gv); Lvar y.(gv)] f [:: Pvar x; Pvar y]).
done. Qed.

Goal (call [:: lvar_of_gvar x] := f ( [:: x +64u 1; Pvar y] ))%C =
  MkI dummy_instr_info
    (Ccall [:: Lvar x.(gv)] f
      [:: Papp2 (Oadd (Op_w U64)) (Pvar x) (Pconst 1); Pvar y]).
done. Qed.

Goal (call [:: aset[U64](x, 0)] := f ( [:: Pvar x] ))%C =
  MkI dummy_instr_info
    (Ccall [:: Laset Aligned AAscale U64 x.(gv) (Pconst 0)] f [:: Pvar x]).
done. Qed.

End CmdTests.
