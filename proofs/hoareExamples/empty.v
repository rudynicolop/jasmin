From Jasmin Require Export hoare_logic.
From Jasmin Require Import it_sems_core core_logics.
From Jasmin Require Import expr oseq psem_core.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import Stdlib.micromega.Lia.

Section prog.
  Context {pd: PointerData}.
  Context `{asmop:asmOp}.

  Definition empty_prog : _uprog :=
    {|
      p_funcs := [::];
      (* No globals *)
      p_globs := [::];
      p_extra := tt;

  |}.
End prog.
