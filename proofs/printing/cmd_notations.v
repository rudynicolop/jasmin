
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
      - lv = randombytes[ ws , n ]( e )
                            = random-bytes syscall (one input, one output)
      - if e { c1 } else { c2 } = conditional (Cif)
      - if e { c }              = conditional with empty else branch
      - for v = lo to hi do { c }     = upward for loop (Cfor, UpTo)
      - for v = hi downto lo do { c } = downward for loop (Cfor, DownTo)
      - while { c1 } ( e ) { c2 }   = while loop (Cwhile Align)
      - skip                         = empty command ([::])

    In if/for/while, the cmd bodies are in the cmd entry; use [skip] for
    empty bodies or [rocq:( ... )] to inject arbitrary cmd terms.
*)

Declare Custom Entry cmd.

Notation "cmd:( c )" := c
  (c custom cmd at level 99).

Notation "rocq:( e )" := e
  (in custom cmd at level 0, e constr at level 99).

Notation "lv  =[b]  e" :=
  (MkI dummy_instr_info (Cassgn lv AT_none abool e))
  (in custom cmd at level 90,
   lv custom lval at level 99, e custom expr at level 99).

Notation "lv =[i]  e" :=
  (MkI dummy_instr_info (Cassgn lv AT_none aint e))
  (in custom cmd at level 90,
   lv custom lval at level 99, e custom expr at level 99).

Notation "lv  =[  ws  ]  e" :=
  (MkI dummy_instr_info (Cassgn lv AT_none (aword ws) e))
  (in custom cmd at level 90,
   ws constr at level 0,
   lv custom lval at level 99, e custom expr at level 99).

Notation "lv  =[  ws , n  ]  e" :=
  (MkI dummy_instr_info (Cassgn lv AT_none (aarr ws n) e))
  (in custom cmd at level 90,
   ws constr at level 0, n constr at level 0,
   lv custom lval at level 99, e custom expr at level 99).

Notation "lv  =  randombytes[ ws , n ]( e )" :=
  (MkI dummy_instr_info (Csyscall [:: lv] (RandomBytes ws n) [:: e]))
  (in custom cmd at level 90,
   ws constr at level 0, n constr at level 0,
   lv custom lval at level 99, e custom expr at level 99).

Notation "'if' e '{' c1 '}' 'else' '{' c2 '}'" :=
  (MkI dummy_instr_info (Cif e c1 c2))
  (in custom cmd at level 90,
   e custom expr at level 99,
   c1 custom cmd at level 99, c2 custom cmd at level 99,
   format "'if'  e  '{'  c1  '}'  'else'  '{'  c2  '}'").

Notation "'if' e '{' c '}'" :=
  (MkI dummy_instr_info (Cif e c [::]))
  (in custom cmd at level 90,
   e custom expr at level 99,
   c custom cmd at level 99,
   format "'if'  e  '{'  c  '}'").

Notation "'for' v '=' lo 'to' hi 'do' '{' c '}'" :=
  (MkI dummy_instr_info (Cfor v (UpTo, lo, hi) c))
  (in custom cmd at level 90,
   v constr at level 0,
   lo custom expr at level 99, hi custom expr at level 99,
   c custom cmd at level 99,
   format "'for'  v  '='  lo  'to'  hi  'do'  '{'  c  '}'").

Notation "'for' v '=' hi 'downto' lo 'do' '{' c '}'" :=
  (MkI dummy_instr_info (Cfor v (DownTo, lo, hi) c))
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

Section CmdTests.

Context
  {asm_op: Type}
  {asmop : asmOp asm_op}
.

Context (x y : var_i) (gx gy : gvar).

Goal cmd:( x =[b] #1 ==i #1 ) =
  MkI dummy_instr_info
    (Cassgn (Lvar x) AT_none abool
      (Papp2 (Oeq Op_int) (Pconst 1) (Pconst 1))).
done. Qed.

Goal cmd:( x =[i] #42 ) =
  MkI dummy_instr_info (Cassgn (Lvar x) AT_none aint (Pconst 42)).
done. Qed.

Goal cmd:( x =[U64] gx ) =
  MkI dummy_instr_info
    (Cassgn (Lvar x) AT_none (aword U64) (Pvar gx)).
done. Qed.

Goal cmd:( x =[U64] gx +64u #1 ) =
  MkI dummy_instr_info
    (Cassgn (Lvar x) AT_none (aword U64)
      (Papp2 (Oadd (Op_w U64)) (Pvar gx) (Pconst 1))).
done. Qed.

Goal cmd:( aset[U64](x, #0) =[U64, 4] gx ) =
  MkI dummy_instr_info
    (Cassgn (Laset Aligned AAscale U64 x (Pconst 0))
      AT_none (aarr U64 4) (Pvar gx)).
done. Qed.

Goal cmd:( aset[U64](x, #0) = randombytes[U64, 4](gx) ) =
  MkI dummy_instr_info
    (Csyscall [:: Laset Aligned AAscale U64 x (Pconst 0)]
      (RandomBytes U64 4) [:: Pvar gx]).
done. Qed.

Goal cmd:( if gx ==i gy { skip } else { skip } ) =
  MkI dummy_instr_info
    (Cif (Papp2 (Oeq Op_int) (Pvar gx) (Pvar gy)) [::] [::]).
done. Qed.

Goal cmd:( if gx <i gy { skip } ) =
  MkI dummy_instr_info
    (Cif (Papp2 (Olt Cmp_int) (Pvar gx) (Pvar gy)) [::] [::]).
done. Qed.

Goal cmd:( for x = #0 to #10 do { skip } ) =
  MkI dummy_instr_info (Cfor x (UpTo, Pconst 0, Pconst 10) [::]).
done. Qed.

Goal cmd:( for x = #10 downto #0 do { skip } ) =
  MkI dummy_instr_info (Cfor x (DownTo, Pconst 0, Pconst 10) [::]).
done. Qed.

Goal cmd:( while { skip } ( gx <i gy ) { skip } ) =
  MkI dummy_instr_info
    (Cwhile Align [::] (Papp2 (Olt Cmp_int) (Pvar gx) (Pvar gy))
      dummy_instr_info [::]).
done. Qed.

End CmdTests.
