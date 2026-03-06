Require Export hoare_logic.
Require Import it_sems_core core_logics.
Require Import expr oseq psem_core (*compiler_util*).

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

(** NOTE: Jéremy's recommendation, since mathcomp disables bullets. *)
Set Bullet Behavior "Strict Subproofs".
(* Set Default Goal Selector "!". *)

(*** Short Hoare Logic Examples. *)

Section programs.

  (** ** Collection of programs for examples.  *)

  Context `{asmop:asmOp}.

  (** Infinite loop.

      NOTE: coercions for [Pbool] are defined at the
      declaration of [pexpr]. *)
  Definition while_true i1 i2 al : cmd :=
    [:: MkI i1 (Cwhile al [::] true i2 [::])].

  (** Assert [false]. *)
  Definition assert_false i msg : cmd :=
    [:: MkI i (Cassert (msg, Pbool false))].

  (** Assign [0 + 0] to a local variable.

      NOTE: Using [AT_keep] to avoid shenanigans.
      NOTE: For simplicity, just integer arithmetic.
      NOTE: Coercions for [Pconst] are defined at the
      declaration of [pexpr]. *)
  Definition assgn_int_zero_plus_zero_local i x : cmd :=
    [:: MkI i
       (Cassgn (Lvar x) AT_keep aint
          (Papp2 (Oadd Op_int) 0%Z 0%Z))].

  (** Assign to array at index.

      We make things simple by just scaling the
      index implicitly with the word size, and we
      use a word size of [U32].

      NOTE: Using [AT_keep] to avoid shenanigans.
      NOTE: I believe that [arr_access] controls if the index
      is scaled by the word size?
   *)
  Definition assgn_u32_array i al (idx :Z) x : cmd :=
    [:: MkI i
       (Cassgn (Laset al AAscale U32 x idx) AT_keep aint 5%Z)].

End programs.

(* TODO: I think [whoare] is too weak... *)

Section proofs_whoare.

  (** ** Proofs about programs.

    NOTE: Here I don't care about errors so I use [whoare].
    TODO: I think I actually want to completely rule out errors... *)

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
    all: by apply hoare_skip.
  Qed.

  Lemma whoare_while_diverge i1 i2 al Q :
    WHoare (fun _ => True) (while_true i1 i2 al) Q.
  Proof.
    rewrite /WHoare /isem_cmd_ /=. apply khoare_bind with Q.
    2:{ (* Intros everything *)
      move => >.
      (* The same as [refine (@khoare_ret _ _ _ _ _ _ _ _ _ _ _ _).] *)
      apply: khoare_ret.
      done. }
    apply khoare_iter, khoare_bind with (fun _ => True);
      first by apply khoare_ret.
    (* Why do I need to apply this? *)
    apply khoare_eq_pred => s.
    apply khoare_read with
      (fun b => sem_cond (p_globs p) true s = ok b).
    { rewrite /isem_cond /sem_cond /=. by apply khoare_ret. }
    rewrite /sem_cond /= => ? [= <-].
    apply khoare_bind with (fun s' => s' = s /\ True).
    all: by apply khoare_ret.
  Qed.

  Lemma whoare_assert_false i msg Q :
    WHoare (fun _ => False) (assert_false i msg) Q.
  Proof. apply whoare_assert; intuition. Qed.

  Lemma whoare_assgn_int_zero_plus_zero_local i x :
    WHoare
      (fun _ => True)
      (assgn_int_zero_plus_zero_local i x)
      (fun s => get_gvar true (p_globs p) s.(evm) (mk_lvar x)
             = ok (Vint 0%Z)).
  Proof.
    apply whoare_assgn with
      (Rv:=fun v => v = Vint 0%Z)
      (Rtr:=fun v => v = Vint 0%Z); simpl.
    { (* NOTE: Is this the best way? *)
      rewrite /sem_sop2 /=.
      apply (@rhoare_ok error) with (QE:=PredT); auto. }
    { rewrite /truncate_val /= => _ _.
      apply rhoare_read with (R:=eq 0%Z).
      - rewrite wrhoareP => v z -> /= [= <-] //.
      - intros ? <-. rewrite /rhoare /rhoare_io //. }
    intros ? ->. rewrite wrhoareP => s1 s2 _.
    intros [Hdb Htrunc Hget]%(write_get_gvarP_eq (p_globs p)).
    simpl in *.
    destruct (eval_atype (vtype x)); simpl in *;
      discriminate || assumption.
  Qed.

  (* TODO: how to write this spec? *)
  Lemma whoare_assgn_u32_array_trivial i al idx x (*vs*) :
    WHoare
      (fun s : estate => True)
      (assgn_u32_array i al idx x)
      (fun s : estate => True).
  Proof.
    apply whoare_assgn with
      (Rv:=eq (Vint 5%Z)) (Rtr:=eq (Vint 5%Z)); simpl.
    (* NOTE: Why does it not care about memory safety? *)
    all: auto.
    - rewrite /rhoare /rhoare_io //.
    - rewrite /rhoare /rhoare_io // => _ _ ? <- /= //.
  Qed.

End proofs_whoare.
