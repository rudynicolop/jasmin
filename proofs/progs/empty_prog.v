From Jasmin Require Export oracles.

Section prog.
  Context {pd: PointerData} `{asmop:asmOp}.

  (** NOTE: empty program does not use extraction oracles.
      But since it lacks a "main" function, it does not
      compile anyway. *)
  Definition empty_prog (_ : oracles) : _uprog :=
    {|
      p_funcs := [::];
      (* No globals *)
      p_globs := [::];
      p_extra := tt;

  |}.
End prog.
