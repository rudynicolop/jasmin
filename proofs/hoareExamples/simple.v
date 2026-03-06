Require Export hoare_logic.
Require Import it_sems_core core_logics.
Require Import expr oseq psem_core (*compiler_util*).

(*** Short Hoare Logic Examples. *)

Section programs.

  (** ** Collection of programs for examples.  *)

  Context `{asmop:asmOp}.

  (** Infinite loop. *)
  Definition while_true i1 i2 al : cmd :=
    [:: MkI i1 (Cwhile al [::] (Pbool true) i2 [::])].

End programs.

Section proofs_whoare.

  (** ** Proofs about programs.

    NOTE: Here I don't care about errors so I use [whoare]. *)

  (** Generic parameters. *)
  Context
    {syscall_state : Type}
      {ep : EstateParams syscall_state}
      {spp : SemPexprParams}
      {asm_op: Type}
      {wa: WithAssert}
      {sip : SemInstrParams asm_op syscall_state}
      {pT : progT}
      {wsw : WithSubWord}
      {scP : semCallParams}
      {dc : DirectCall}.

  (** Generic parameters for [whoare].*)
  Context {E E0: Type -> Type}.
  Context {sem_F : sem_Fun E} {wE: with_Error E E0} {iE0 : InvEvent E0}.
  Context (p : prog) (ev: extra_val_t).

  (** Copied from test section in [proofs/lang/hoare_logic.v] *)
  #[local] Existing Instance trivial_invErr.
  #[local] Existing Instance trivial_invEvent.
  (* #[local] Notation pre := (fun s0 s => s = s0). *)
  (* #[local] Notation post X := (fun s0 s => s0.(evm) =[\ X] s.(evm)). *)
  #[local] Existing Instance trivial_spec.

  (** Factor out common section parameters. *)
  #[local] Notation WHoare := (whoare p ev).

  Lemma whoare_while_true_basic i1 i2 al :
    WHoare (fun _ => True) (while_true i1 i2 al) (fun _ => True).
  Proof.
    apply whoare_while; auto.
    all: apply hoare_skip; auto.
  Qed.

  Lemma whoare_while_diverge i1 i2 al Q :
    WHoare (fun _ => True) (while_true i1 i2 al) Q.
  Proof.
    eapply hoare_weaken1 with (P2:=fun _ => True);
      last apply whoare_while_full; simpl; auto.
    all: try solve [intuition].
    - apply hoare_skip.
      (* TODO: impossible, maybe I need
         to unfold, run interpreter, and manually
         apply [khoare_iter]... *)
      admit.
    - apply hoare_skip. intuition.
  Abort.
End proofs_whoare.
