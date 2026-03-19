From Jasmin Require Export hoare_logic.
From Jasmin Require Import it_sems_core core_logics.
From Jasmin Require Import expr oseq psem_core.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import Stdlib.micromega.Lia.

(** NOTE: Jéremy's recommendation, since mathcomp disables bullets. *)
Set Bullet Behavior "Strict Subproofs".

(*** Short Hoare Logic Examples. *)

Section helpers_pointers.
  Context {pointer: eqType} {Pointer: pointer_op pointer}.

  Lemma disjoint_range_sym ℓ1 ℓ2 w1 w2 :
    CoreMem.disjoint_range ℓ1 w1 ℓ2 w2 ->
    CoreMem.disjoint_range ℓ2 w2 ℓ1 w1.
  Proof.
    rewrite /CoreMem.disjoint_range => Hdisj z1 z2 Hz1 Hz2 Hadd.
    by apply Hdisj with (1:=Hz2) (2:=Hz1).
  Qed.

  Lemma disjoint_range_sym_iff ℓ1 ℓ2 w1 w2 :
    CoreMem.disjoint_range ℓ1 w1 ℓ2 w2 <-> CoreMem.disjoint_range ℓ2 w2 ℓ1 w1.
  Proof. split; apply disjoint_range_sym. Qed.

  Section helpers_coremem.
    Context {core_mem} {CM : coreMem pointer core_mem}.

    (* NOTE: no good lemmas for [write]. *)
    Lemma validw_impl_write [s : wsize] (w : word s)
      (m : core_mem) (al: aligned) (p : pointer) :
      validw m al p s = true ->
      exists m' : core_mem, write m al p w = ok m'.
    Proof.
      intros Hvalid.
      pose proof writeV w m al p as Hwrite.
      rewrite Hvalid in Hwrite.
      by apply elimT with (2:=is_true_true) in Hwrite.
    Qed.
  End helpers_coremem.
End helpers_pointers.

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

      For an array stored at variable [x],
      we assign index [idx] value [v].

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
  Definition assgn_u32_array i al (idx v : Z) x : cmd :=
    [:: MkI i
       (Cassgn (Laset al AAscale U32 x idx) AT_keep (aword U32)
          (Papp1 (Oword_of_int U32) v))].

  (** Assign to a location in memory.

      We assign memory location [ℓ] value [v].
      We use 32-bit words.

      NOTE: We need to explicitly cast the address [ℓ]
      to a word of size [Uptr] (an unknown parameter?),
      and [v] to a 32-bit word.

      TODO: What is [x] used for?? It seems ignored in [write_lval]
      for the [Lmem] case...?

   *)
  Definition store_in_memory `{PointerData} i al x (ℓ v : Z) : cmd := 
    [:: MkI i
       (Cassgn
          (Lmem al U32 x (Papp1 (Oword_of_int Uptr) ℓ))
          AT_keep (aword U32)
          (Papp1 (Oword_of_int U32) v))].

  (** Load an array from a pointer, then read from the array. *)
  (* TODO: *)
  (* Definition load_array_then_get i x n al : cmd := *)
  (*   [:: MkI i *)
  (*      (Cassgn (Lvar x) AT_keep (aarr U32 n) (Pload al U32)) *)
  (*   ] *)

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

  Section array_stores.

  Lemma hoare_assgn5_u32_array i al
    (idx : Z) (x : var_i) (n : positive) (arr : WArray.array n) :
    (* Variable needs to have the correct array type. *)
    eval_atype (vtype x.(v_var)) = carr n ->
    (* Index needs to be non-negative. *)
    (0 <= idx)%Z ->
    (* TODO: Why do I need a [_ + 3]? *)
    (idx * wsize_size U32 + 3 < n)%Z ->
    Hoare
      (fun s : estate => s.(evm).[x] = Varr arr)
      (assgn_u32_array i al idx 5%Z x)
      (fun s : estate => exists arr',
           (* TODO: but does this show that the rest of [s] is unchanged? *)
           WArray.set arr al AAscale idx (wrepr U32 5) = ok arr'
           /\ s.(evm).[x] = Varr arr').
  Proof.
    intros Hxtype Hidx0 Hidxn.
    eapply hoare_assgn with (Rv:=eq (Vword _))
      (Rtr:=eq (Vword _)) (Qerr:=fun _ => False) => /= //.
    { rewrite /truncate_val /= => _ _.
      eapply rhoare_bind with (R:=eq _) (QET:=fun _ : error => False) => /= //.
      { intros ? <- => /=. rewrite truncate_word_u //. }
      apply rhoare_ok with (QE:=fun _ : error => False) => ? <- //. }
    (* TODO: Is there no lemma to show [write_lval] succeeds? *)
    intros ? <-. rewrite /write_lval /= truncate_word_u /=.
    apply rhoare_read with (R:=eq (Varr arr)).
    { rewrite /get_var /= => s Hs. rewrite Hs /= //. }
    intros ? <-.
    apply rhoare_bind_eval with
      (R:=fun arr' => WArray.set arr al AAscale idx (wrepr U32 5) = ok arr').
    { intros s Hsx.
      apply rhoare_ok with (QE:=fun _ : error => False) => _ ->.
      (* TODO: Is there no lemma to show that [WArray.set] succeeds? *)
      rewrite /WArray.set.
      enough (validw (Pointer:=WArray.PointerZ) arr al
                  (idx * mk_scale AAscale U32)%Z U32 = true) as Hvalid.
      { destruct (validw_impl_write (wrepr U32 5) Hvalid) as [arr' Hset].
        rewrite Hset //. }
      rewrite /validw is_aligned_if_is_align ?WArray.is_align_scale // /=.
      rewrite ziota_recP /= !WArray.addE /WArray.in_bound Z.add_0_r.
      rewrite !Bool.andb_true_iff /= !Z.leb_le !Z.ltb_lt.
      rewrite /wsize_size in Hidxn *.
      repeat split; try lia. }
    intros arr' Hset.
    rewrite /write_var.
    apply rhoare_read with (R:=fun t : Vm.t => t.[x] = Varr arr').
    { intros s Hsx.
      rewrite /set_var /= Hxtype /= eq_refl /= Vm.setP_eq /=.
      rewrite Hxtype eq_refl //. }
    intros t Ht.
    apply rhoare_ok with (QE:=fun _ : error => False).
    intros s Hsx. exists arr'. split; auto.
  Qed.

  Lemma hoare_assgn5_clément i al n (arr : WArray.array n) (x : var_i) :
    (* Variable needs to have the correct array type. *)
    eval_atype (vtype x.(v_var)) = carr n ->
    (* requirement for write to succeed: enough space in array *)
    (7 < n)%Z ->
    Hoare
      (fun (s : estate) =>
         s.(evm).[x] = Varr arr
         /\ WArray.get al AAscale U32 arr 0%Z = ok (wrepr U32 1%Z)
         /\ WArray.get al AAscale U32 arr 1%Z = ok (wrepr U32 3%Z))
      (assgn_u32_array i al 1%Z 5%Z x)
      (fun (s : estate) => exists arr' : WArray.array n,
           s.(evm).[x] = Varr arr'
           /\ WArray.get al AAscale U32 arr' 0%Z = ok (wrepr U32 1%Z) 
           /\ WArray.get al AAscale U32 arr' 1%Z = ok (wrepr U32 5%Z)).
  Proof.
    intros Heval_atype Hn7.
    eapply hoare_assgn with
      (Rv:=eq (Vword _)) (Rtr:=eq (Vword _)) (Qerr:=fun _ => False) => /= //.
    { rewrite /truncate_val /= => _ _.
      eapply rhoare_bind with (R:=eq _) (QET:=fun _ : error => False) => /= //.
      { intros ? <-. rewrite /= truncate_word_u //. }
      apply rhoare_ok with (QE:=fun _ : error => False) => ? <- //. }
    intros ? <-.
    rewrite /write_lval /= truncate_word_u /=.
    apply rhoare_read with (R:=eq (Varr arr)).
    { rewrite /get_var /= => s [Hs [Hget0 Hget1]]. rewrite Hs /= //. }
    intros ? <-.
    apply rhoare_bind_eval with
      (R:=fun arr' => WArray.set arr al AAscale 1%Z (wrepr U32 5) = ok arr').
    { intros s Hsx.
      apply rhoare_ok with (QE:=fun _ : error => False) => _ ->.
      rewrite /WArray.set Z.mul_1_l.
      enough (validw (Pointer:=WArray.PointerZ) arr al
                (mk_scale AAscale U32)%Z U32 = true) as Hvalid.
      { destruct (validw_impl_write (wrepr U32 5) Hvalid) as [arr' Hset].
        rewrite Hset //. }
      rewrite /validw is_aligned_if_is_align ?WArray.is_align_scale // /=.
      rewrite ziota_recP /= !WArray.addE /WArray.in_bound Z.add_0_r.
      rewrite !Bool.andb_true_iff /= !Z.leb_le !Z.ltb_lt /wsize_size /=.
      repeat split; assumption || lia. }
    intros arr' Hset. rewrite /write_var.
    apply rhoare_read with (R:=fun t : Vm.t => t.[x] = Varr arr').
    { intros Hsx.
      rewrite /set_var /= Heval_atype /= eq_refl /= Vm.setP_eq /=.
      rewrite Heval_atype eq_refl //. }
    intros t Ht.
    apply rhoare_ok with (QE:= fun _ : error => False).
    intros s (Hsx & Hget0 & Hget1). exists arr'.
    rewrite (WArray.setP_eq Hset) (WArray.setP_neq (p2:=0%Z) _ Hset) //.
  Qed.

  End array_stores.

  Section memory_store_helpers.
    (** Proving facts about memory stores, with attempts at a helper lemma,
        instead of directly invoking [hoare_assgn]. 

        NOTE: all memory stores in Jasmin are [Cassgn] to an [Lmem] variant of [lval]. *)


  Lemma hoare_store_in_memory_too_weak0 i al x (ℓ v : Z) :
    (* Seems like a reasonable assumption, that the address used
       for the pointer to memory is aligned with the 32-bit values? *)
    (* TODO: do we want this assumption separately from the validity assumption? *)
    (* is_align (wrepr Uptr ℓ) U32 = true -> *)
    Hoare
      (fun s : estate =>
         validw s.(emem) al (wrepr Uptr ℓ) U32 = true)
      (store_in_memory i al x ℓ v)
      (fun s : estate =>
         read s.(emem) al (wrepr Uptr ℓ) U32 = ok (wrepr U32 v)).
  Proof.
    eapply hoare_assgn with
      (Rv:= eq (Vword _)) (Rtr:= eq (Vword _)) (Qerr:=fun _ => False) => /= //.
    { rewrite /truncate_val /= => _ _.
      eapply rhoare_bind with
        (R:=eq _) (QET:=fun _ : error => False) => /= //.
      { intros ? <-. rewrite /= truncate_word_u //. }
      apply rhoare_ok with (QE:=fun _ : error => False) => ? <- //. }
    intros ? <-.
    rewrite /write_lval /= !truncate_word_u /=.
    apply rhoare_read with
      (R:=fun m : low_memory.mem =>
            read m al (wrepr Uptr ℓ) U32 = ok (wrepr U32 v)).
    { intros s [m Hs]%(validw_impl_write (wrepr U32 v)).
      rewrite Hs. eapply writeP_eq; eauto. } 
    intros m Hreadm.
    apply rhoare_ok with (QE:=fun _ : error => False) => s Hvalid //.
  Qed.

  Lemma hoare_stores_in_memory i1 i2 al x1 x2 (ℓ1 ℓ2 v1 v2 : Z) :
    Hoare
      (fun s : estate =>
         validw s.(emem) al (wrepr Uptr ℓ1) U32 = true
         /\ validw s.(emem) al (wrepr Uptr ℓ2) U32 = true)
      (store_in_memory i1 al x1 ℓ1 v1 ++ store_in_memory i2 al x2 ℓ2 v2)
      (fun s : estate =>
         read s.(emem) al (wrepr Uptr ℓ1) U32 = ok (wrepr U32 v1)
         /\ read s.(emem) al (wrepr Uptr ℓ2) U32 = ok (wrepr U32 v2)).
  Proof.
    (* NOTE: No frame rule since so SL, so sad. *)
    rewrite hoareP => s [Hvalid1 Hvalid2].
    eapply hoare_cons.
    { eapply hoare_weaken1; last by apply hoare_store_in_memory_too_weak0;
        progress simpl.
      - by intros ? ->.
      - intros ?. apply id. }
    rewrite hoareP => s' Hread1.
    eapply hoare_weaken1; last by apply hoare_store_in_memory_too_weak0.
    { intros ? ->. eapply readV.
    (* NOTE: we have lost information about how [s'] is related to
       [s], how can we continue...? *)
      admit. }
    intros s'' Hread2. simpl in *.
    (* NOTE: we have lost information about how all of the states,
       ([s], [s'], and [s'']) are related to each other.
       How can we continue...? *)
    Abort.

  (** For this lemma to be used modularly, we need to expose the
      state [σ]. *)
  Lemma hoare_store_in_memory_remember i al x (ℓ v : Z) (σ : estate) :
    Hoare
      (fun s : estate =>
         (* NOTE: We force the precondition state to be equivalent to
            the exposed state. *)
         s = σ /\ validw s.(emem) al (wrepr Uptr ℓ) U32 = true)
      (store_in_memory i al x ℓ v)
      (fun s : estate =>
         (* NOTE: We need to remember that the new memory is the result
            of writing to the old state. *)
         write σ.(emem) al (wrepr Uptr ℓ) (wrepr U32 v) = ok s.(emem)
         (* NOTE: The variable map and system call state should be identical. *)
         /\ s.(evm) = σ.(evm) /\ s.(escs) = σ.(escs)
         /\ read s.(emem) al (wrepr Uptr ℓ) U32 = ok (wrepr U32 v)).
  Proof.
    eapply hoare_assgn with
      (Rv:= eq (Vword _)) (Rtr:= eq (Vword _)) (Qerr:=fun _ => False) => /= //.
    { rewrite /truncate_val /= => _ _.
      eapply rhoare_bind with
        (R:=eq _) (QET:=fun _ : error => False) => /= //.
      { intros ? <-. rewrite /= truncate_word_u //. }
      apply rhoare_ok with (QE:=fun _ : error => False) => ? <- //. }
    intros ? <-.
    rewrite /write_lval /= !truncate_word_u /=.
    apply rhoare_read with
      (R:=fun m : low_memory.mem =>
            write σ.(emem) al (wrepr Uptr ℓ) (wrepr U32 v) = ok m).
    { intros s [-> [m Hs]%(validw_impl_write (wrepr U32 v))].
      rewrite Hs //. }
    intros m Hwrite.
    apply rhoare_ok with (QE:=fun _ : error => False) => s [-> Hvalid] /= //.
    repeat split; auto. eapply writeP_eq; eauto.
  Qed.

  Lemma hoare_stores_in_memory i1 i2 al x1 x2 (ℓ1 ℓ2 v1 v2 : Z) :
    (* NOTE: Ya know what would also enforce that the ranges
       are disjoint: SEPARATION LOGIC! *)
    CoreMem.disjoint_range (wrepr Uptr ℓ1) U32 (wrepr Uptr ℓ2) U32 ->
    Hoare
      (fun s : estate =>
         validw s.(emem) al (wrepr Uptr ℓ1) U32 = true
         /\ validw s.(emem) al (wrepr Uptr ℓ2) U32 = true)
      (store_in_memory i1 al x1 ℓ1 v1 ++ store_in_memory i2 al x2 ℓ2 v2)
      (fun s : estate =>
         read s.(emem) al (wrepr Uptr ℓ1) U32 = ok (wrepr U32 v1)
         /\ read s.(emem) al (wrepr Uptr ℓ2) U32 = ok (wrepr U32 v2)).
  Proof.
    intros Hdisj.
    rewrite hoareP => s [Hvalid1 Hvalid2].
    eapply hoare_cons.
    { eapply hoare_weaken1; last by apply hoare_store_in_memory_remember;
        progress simpl.
      - by intros ? ->.
      - intros ?. apply id. }
    rewrite hoareP => s1 Hwrite1.
    destruct Hwrite1 as (Hwrite1 & Hevm1 & Hescs1 & Hread1).
    eapply hoare_weaken1; last by apply hoare_store_in_memory_remember.
    { intros ? ->. split; first reflexivity.
      (* NOTE: We now remember exactly how we obtained [s1]! *)
      (* TODO: seriously, no lemmas about read succeeding!!!??? *)
      rewrite (write_validw_eq Hwrite1) //. }
    intros s'' Hwrite2.
    destruct Hwrite2 as (Hwrite2 & Hevm2 & Hescs2 & Hread2).
    split; last assumption.
    rewrite (writeP_neq _ Hwrite2) //.
    by apply disjoint_range_sym.
  Qed.

  End memory_store_helpers.

  Section memory_store_direct.
    (** ** Directly prove with the [hoare_assgn] lemma. *)

    (** Here we avoid [hoareP]. *)
    Lemma hoare_stores_in_memory_direct0 i1 i2 al x1 x2 (ℓ1 ℓ2 v1 v2 : Z) :
      CoreMem.disjoint_range (wrepr Uptr ℓ1) U32 (wrepr Uptr ℓ2) U32 ->
      Hoare
        (fun s : estate =>
           validw s.(emem) al (wrepr Uptr ℓ1) U32 = true
           /\ validw s.(emem) al (wrepr Uptr ℓ2) U32 = true)
        (store_in_memory i1 al x1 ℓ1 v1 ++ store_in_memory i2 al x2 ℓ2 v2)
        (fun s : estate =>
           read s.(emem) al (wrepr Uptr ℓ1) U32 = ok (wrepr U32 v1)
           /\ read s.(emem) al (wrepr Uptr ℓ2) U32 = ok (wrepr U32 v2)).
    Proof.
      intros Hdisj.
      eapply hoare_cons with
        (R:=fun s =>
           read s.(emem) al (wrepr Uptr ℓ1) U32 = ok (wrepr U32 v1)
           /\ validw s.(emem) al (wrepr Uptr ℓ2) U32 = true).
      { eapply hoare_assgn with
          (Rv:=eq (Vword _)) (Rtr:=eq (Vword _)) (Qerr :=fun _ => False) => /= //.
        { rewrite /truncate_val /= => s [Hs1 Hs2].
          eapply rhoare_bind with (R:=eq _) (QET:=fun _ : error => False) => /= //.
          { intros ? <-. rewrite /= truncate_word_u //. }
          apply rhoare_ok with (QE:=fun _ : error => False) => ? <- //. }
        intros ? <-. rewrite /write_lval /= !truncate_word_u /=.
        (* Without binding the state via [hoareP], is it possible to obtain
           a sufficiently strong condition here? *)
        eapply rhoare_read with
          (R:=fun m : low_memory.mem =>
                read m al (wrepr Uptr ℓ1) U32 = ok (wrepr U32 v1)
                /\ validw m al (wrepr Uptr ℓ2) U32 = true).
        { intros s [[m1 Hs1]%(validw_impl_write (wrepr U32 v1)) Hs2].
          rewrite Hs1 /= //.
          split; first by eapply writeP_eq; eassumption.
          rewrite (write_validw_eq Hs1) //. }
        intros m1 Hread1.
        apply rhoare_ok with (QE:=fun _ : error => False) => /= // s [Hs1 Hs2]. }
      eapply hoare_assgn with
        (Rv:=eq (Vword _)) (Rtr:=eq (Vword _)) (Qerr :=fun _ => False) => /= //.
      { rewrite /truncate_val /= => s [Hread1 Hvalid2].
        eapply rhoare_bind with (R:=eq _) (QET:=fun _ : error => False) => /= //.
        { intros ? <-. rewrite /= truncate_word_u //. }
        apply rhoare_ok with (QE:=fun _ : error => False) => ? <- //. }
      intros ? <-. rewrite /write_lval /= !truncate_word_u /=.
      eapply rhoare_read with
        (R:=fun m : low_memory.mem =>
              read m al (wrepr Uptr ℓ1) U32 = ok (wrepr U32 v1)
              /\ read m al (wrepr Uptr ℓ2) U32 = ok (wrepr U32 v2)).
      { intros s [Hs1 [m2 Hs2]%(validw_impl_write (wrepr U32 v2))].
        rewrite Hs2 /=.
        split; last by eapply writeP_eq; eassumption.
        rewrite (writeP_neq _ Hs2) //.
        by apply disjoint_range_sym. }
      intros m [Hm1 Hm2].
      apply rhoare_ok with (QE:=fun _ : error => False) => s [Hs1 Hs2] /= //.
    Qed.

    (** Here we use [hoareP] to bind the state. *)
    Lemma hoare_stores_in_memory_direct1 i1 i2 al x1 x2 (ℓ1 ℓ2 v1 v2 : Z) :
      CoreMem.disjoint_range (wrepr Uptr ℓ1) U32 (wrepr Uptr ℓ2) U32 ->
      Hoare
        (fun s : estate =>
           validw s.(emem) al (wrepr Uptr ℓ1) U32 = true
           /\ validw s.(emem) al (wrepr Uptr ℓ2) U32 = true)
        (store_in_memory i1 al x1 ℓ1 v1 ++ store_in_memory i2 al x2 ℓ2 v2)
        (fun s : estate =>
           read s.(emem) al (wrepr Uptr ℓ1) U32 = ok (wrepr U32 v1)
           /\ read s.(emem) al (wrepr Uptr ℓ2) U32 = ok (wrepr U32 v2)).
    Proof.
      intros Hdisj.
      (* Step to bind state. *)
      rewrite hoareP => s.
      intros [[m1 Hm1]%(validw_impl_write (wrepr U32 v1))
                (* [m2 Hs2]%(validw_impl_write (wrepr U32 v2)) *)
                Hvalid2].
      (* We bind the next state to the result of a write. *)
      eapply hoare_cons with (R:=fun s1 : estate => s1 = with_mem s m1).
      { eapply hoare_assgn with
          (Rv:=eq (Vword _)) (Rtr:=eq (Vword _)) (Qerr :=fun _ => False) => /= //.
        { intros ? ->. rewrite /truncate_val /=.
          eapply rhoare_bind with (R:=eq _) (QET:=fun _ : error => False) => /= //.
          { intros ? <-. rewrite /= truncate_word_u //. }
          apply rhoare_ok with (QE:=fun _ : error => False) => ? <- //. }
        intros ? <-. rewrite /write_lval /= !truncate_word_u /=.
        eapply rhoare_read with (R:=fun m : low_memory.mem => m = m1).
        { intros ? ->. rewrite Hm1 //. }
        intros ? ->.
        apply rhoare_ok with (QE:=fun _ : error => False) => ? -> /= //. }
      eapply hoare_assgn with
        (Rv:=eq (Vword _)) (Rtr:=eq (Vword _)) (Qerr :=fun _ => False) => /= //.
      { intros ? ->. rewrite /truncate_val /=.
        eapply rhoare_bind with (R:=eq _) (QET:=fun _ : error => False) => /= //.
        { intros ? <-. rewrite /= truncate_word_u //. }
        apply rhoare_ok with (QE:=fun _ : error => False) => ? <- //. }
      intros ? <-. rewrite /write_lval /= !truncate_word_u /=.
      (* Get state after second write. *)
      rewrite -(write_validw_eq Hm1) in Hvalid2.
      apply validw_impl_write with (w:=wrepr U32 v2) in Hvalid2 as [m2 Hm2].
      eapply rhoare_read with (R:=fun m : low_memory.mem => m = m2).
      { intros ? -> => /=. rewrite Hm2 //. }
      intros ? ->.
      apply rhoare_ok with (QE:=fun _ : error => False) => _ -> /=.
      rewrite (writeP_neq _ Hm2) /=; last by apply disjoint_range_sym.
      split;  by eapply writeP_eq; eassumption.
    Qed.
  End memory_store_direct.
End proofs_hoare.
