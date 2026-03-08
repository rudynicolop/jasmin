From Jasmin Require Export hoare_logic.
From Jasmin Require Import it_sems_core core_logics.
From Jasmin Require Import expr oseq psem_core.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

(** NOTE: Jéremy's recommendation, since mathcomp disables bullets. *)
Set Bullet Behavior "Strict Subproofs".

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
      NOTE: We need to explicitly convert the value
      to be stored in the array to a word, otherwise
      we get a type error.
   *)
  Definition assgn_u32_array i al (idx :Z) x : cmd :=
    [:: MkI i
       (Cassgn (Laset al AAscale U32 x idx) AT_keep (aword U32)
          (Papp1 (Oword_of_int U32) 5%Z))].

End programs.

(** NOTE: To rule out bad behavior, we set the conditions for error
    events to [False].
    TODO: Do we want to do this for the precondition too, or just
    the postcondition? *)
Definition impossible_invEvent (E0 : Type -> Type) : InvEvent E0 :=
  {| preInv0_ := fun _ _ => False
  ; postInv0_ := fun _ _ _ => False |}.
Definition impossible_invErr : InvErr :=
  {| invErr_ := fun _ => False |}.

Section proofs_hoare.

  (** ** Proofs about programs.

      NOTE: We use [False] for the predicate for error cases,
      in order to completely rule out bad behavior. *)

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

  (** Generic parameters for [hoare].*)
  Context {E E0: Type -> Type}.
  Context {sem_F : sem_Fun E} {wE: with_Error E E0} {iE0 : InvEvent E0}.
  Context (p : prog) (ev: extra_val_t).

  (** We need to create the instances for the error pre/postconditions
      so they are discoverable by our [hoare] triple uses. *)
  Local Existing Instance impossible_invEvent.
  Local Existing Instance impossible_invErr.

  (** Factor out common section parameters. *)
  Local Notation Hoare := (hoare p ev).

  Lemma hoare_while_true_basic i1 i2 al :
    Hoare (fun _ => True) (while_true i1 i2 al) (fun _ => True).
  Proof.
    apply hoare_while with (Qerr := fun _ => False); simpl; auto.
    1, 3: by apply hoare_skip.
    rewrite /sem_cond /= => _ //.
  Qed.

  Lemma hoare_while_diverge i1 i2 al Q :
    Hoare (fun _ => True) (while_true i1 i2 al) Q.
  Proof.
    rewrite /Hoare /isem_cmd_ /=. apply khoare_bind with Q.
    2:{ (* Intros everything *)
      move => >.
      (* The same as [refine (@khoare_ret _ _ _ _ _ _ _ _ _ _ _ _).] *)
      apply: khoare_ret. done. }
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

  Lemma hoare_assert_false i msg Q :
    Hoare (fun _ => False) (assert_false i msg) Q.
  Proof. apply hoare_assert with (Qerr:=fun _ => False); intuition. Qed.

  (** NOTE the differences between the applications of
      [rhoare_bind], [rhoare_read], and [rhoare_write]. *)
  Lemma whoare_assgn_int_zero_plus_zero_local i x :
    eval_atype (vtype x.(v_var)) = cint ->
    Hoare
      (fun _ => True)
      (assgn_int_zero_plus_zero_local i x)
      (fun s : estate => s.(evm).[x] = Vint 0%Z).
  Proof.
    intros Hx_type.
    apply hoare_assgn with
      (Rv:=fun v => v = Vint 0%Z)
      (Rtr:=fun v => v = Vint 0%Z)
      (Qerr:=fun _ => False); simpl; auto.
    { (* NOTE: Is this the best way? *)
      rewrite /sem_sop2 /=.
      by apply rhoare_ok with (QE:=fun _ : error => False). }
    { rewrite /truncate_val /= => _ _.
      apply rhoare_bind with (R:=eq 0%Z) (QET:=fun _ => False); auto.
      { move => ? -> /= //. }
      apply rhoare_ok with (QE:=fun _ : error => False) => ? <- //. }
    intros ? ->.
    (* NOTE: Since we use both [s] and [vm], we need [rhoare_read]. *)
    apply rhoare_read with (fun s => s.[x] = Vint 0%Z).
    { rewrite /set_var /= Hx_type /= => s _.
      rewrite Vm.setP_eq Hx_type /= //. }
    intros vm Hvm_get.
    apply rhoare_ok with (QE:=fun _ : error => False) => s _ /= //.
  Qed.

  (* TODO: how to write this spec? *)
  Lemma hoare_assgn_u32_array i al
    (idx : Z) (x : var_i) (n : positive) (arr : WArray.array n) :
    (idx < n)%Z ->
    Hoare
      (fun s : estate => s.(evm).[x] = Varr arr)
      (assgn_u32_array i al idx x)
      (fun s : estate => True).
  Proof.
    intros Hidx.
    eapply hoare_assgn with (Rv:=eq (Vword _))
      (Rtr:=eq (Vword _)) (Qerr:=fun _ => False) => /= //.
    { rewrite /truncate_val /= => _ _.
      eapply rhoare_bind with (R:=eq _) (QET:=fun _ : error => False) => /= //.
      { intros ? <-. rewrite /= truncate_word_u //. }
      apply rhoare_ok with (QE:=fun _ : error => False) => ? <- //. }
    (* TODO: Is there no lemma to show [write_lval] succeeds? *)
    intros ? <-.
    rewrite /write_lval /= truncate_word_u /=.
    apply rhoare_read with (R:=eq (Varr arr)).
    { rewrite /get_var /= => s Hs. rewrite Hs /= //. }
    intros ? <-.
    apply rhoare_bind_eval with
      (R:=fun arr' => WArray.set arr al AAscale idx (wrepr U32 5) = ok arr').
    { intros s Hsx.
      apply rhoare_ok with (QE:=fun _ : error => False) => _ ->.
      (* TODO: Is there no lemma to show that [WArray.set] succeeds? *)
      destruct (WArray.set arr al AAscale idx (wrepr U32 5))
        as [arr' |] eqn:Hset; auto.
      Search (WArray.set _ _ _ _ _ = Error _).
      (* TODO: Is there no lemma to infer from [WArray.set] failing? *)
      rewrite /WArray.set in Hset.
      rewrite /write /= in Hset.
      pose proof WArray.is_align_scale idx U32 as HisAlign.
      apply is_aligned_if_is_align with (al:=al) in HisAlign.
      rewrite HisAlign /= in Hset.
      Search WArray.set8.
      destruct (WArray.valid8P arr)
      Search (Result.bind _ _ = ok _).
      Search is_align.
      Search (write _ _ _ _ = Error _).
      (* TODO: Is there no lemma to show that [write] succeeds for arrays? *)
      rewrite /write /=.
      Search (is_aligned_if _ _ _).
      Search (write _ _ _ _ = ok _).
      destruct (writeV (wrepr U32 5) arr al (idx * mk_scale AAscale U32)%Z).
      Search (WArray.set _ _ _ _ _ = ok _).
    }
    intros s _. simpl.
    rewrite /on_arr_var /=.
    (* Print WArray.set. *)
  (* TODO: need to do the following:
     - [x] needs to map to an array in memory [Varr n t], ow it's a type error.
     - The actual array of values is [t : WArray.array n].
     - Do we need [idx < n]?
   *)
  Abort.

End proofs_hoare.
