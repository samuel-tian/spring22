(** * 6.822 Formal Reasoning About Programs, Spring 2022 - Pset 12 *)

Require Import Frap Pset12Sig.

Module Impl.
(* Part 1: read Pset12Sig.v and answer the questions below. This task is
 * ungraded, but we are assigning it in hope it helps you complete the
 * following parts.

(these are duplicative with past psets:)

- Which syntactic construct can be used to implement sequencing of two commands?

- Which step rules allow a sequenced program to make progress?

- Which step rule is used when a loop terminates?

- Which step rule is used when a loop continues?

- Why is there no step rule for Fail?

(these are about the programming language in this pset:)

- Which syntactic construct is used to spawn new threads?

- Which step rules allow a multi-threaded program to make progress?

- How can threads in this language communicate with each other?

- What do the steps that are factored out into the astep inductive have in common?

(these are about the program logic:)

- Which rule of the program logic handles astep commands?

- What is the meaning of the "rely" argument [R]?

- What would [R] be for a program that can run in any environment?

- What would [R] be for a program that can only run alone?

- Which constructors of [hoare_triple] change [R]? Do they make it more or less permissive?

- What is the meaning of the "guarantee" argument [G]?

- Which cases of [hoare_triple] require you to prove [G]?

- What would [G] be for a program that can run in any environment?

- What would [G] be for a program that can only run alone?

(these are about program logic tactics:)

- What syntactic forms of commands does [step] handle?

- What syntactic forms of commands does [fork] handle?

- What are the six arguments to the tactic [fork]? Classify them into two groups of three, and then (differently) classify them into three pairs.

- What syntactic forms of commands does [atomic] handle?

- What is the argument to the tactic [atomic]?
*)

(* Part 2: prove a program *)

(* Pset12Example.v contains an example verification of a non-trivial program.
 * You can use it as a reference when trying to figure out what the rules,
 * lemmas, and tactics here do, but you are not required to understand it.
 * The program in this file is much simpler. *)

(* Verify that this program manages to increase the counter value. *)
Lemma ht_increment : forall init,
  hoare_triple
    (fun h => h $! 0 = init)
    (fun _ _ => False)
    (   (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1)))
     || (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1)))
    )
    (fun _ _ => True)
    (fun _ h => h $! 0 > init).
Proof.
  intros.
  fork (fun h => h $! 0 >= init)
       (fun h h' => h = h' \/ h' $! 0 > init)
       (fun (_ : unit) h => h $! 0 > init)
       (fun h => h $! 0 >= init)
       (fun h h' => h = h' \/ h' $! 0 > init)
       (fun (_ : unit) h => h $! 0 > init).
  step.
  atomic (fun (r : nat) (h : heap) => h $! 0 >= init /\ r >= init).
  eapply HtAtomic; simp.
  step.
  atomic (fun (r : nat) (h : heap) => h $! 0 >= init /\ r >= init).
  eapply HtAtomic; simp.
  simp.
  simp.
  simp.
  simp.
  simp.
Qed.

(* Part 3: prove soundness of the program logic *)

(* Now it remains to prove that having a [hoare_triple] actually means
 * that execution will proceed safely, and if the program terminates then the
 * postcondition will be satisfied. *)

(* If non-negligible time has passed since you read the sig file, please
 * review the definitions of [trsys_of] and [notAboutToFail] now. *)

(* Then, feel free to just skim the next lemmas, right until the final
 * theorem you are asked to prove. *)

(* Here are a few more lemmas that you may find helpful: *)

Lemma HtStrengthen : forall {t : Set} P R c G (Q : t -> _) (P' : hprop),
    hoare_triple P R c G Q
    -> (forall h, P' h -> P h)
    -> stableP P' R
    -> hoare_triple P' R c G Q.
Proof. eauto. Qed.

Lemma HtWeakenFancy : forall {t : Set} P R c G Q (G' : hrel) (Q' : t -> hprop),
    hoare_triple P R c G Q
    -> (forall v h, Q v h -> Q' v h)
    -> (forall h h', G h h' -> G' h h')
    -> hoare_triple P R c G' Q'.
Proof. eauto using always_stableP. Qed.

Lemma HtReturn' : forall {t : Set} (P : hprop) (R G : hrel) (Q : _ -> hprop) (v : t),
    stableP P R
    -> (forall h, P h -> Q v h)
    -> hoare_triple P R (Return v) G Q.
Proof.
  simplify.
  eapply HtConsequence with (P' := P) (R' := R) (G' := G); eauto.
  simplify; propositional; subst; eauto.
Qed.

Lemma stableP_self : forall h R, stableP (fun h' => R^* h h') R.
Proof. simp. eauto using trc_trans. Qed.

Lemma stableP_star : forall R h h', R^* h h' ->
    forall P, stableP P R -> P h -> P h'.
Proof. induct 1; simplify; eauto. eapply IHtrc; eauto. Qed.

Lemma stableP_weakenR : forall P R, stableP P R -> forall R' : hrel,
    (forall h1 h2, R' h1 h2 -> R h1 h2) -> stableP P R'.
Proof. simp; eauto. Qed.

Local Hint Resolve stableP_self : core.

Lemma stable_stableQ : forall (t : Set) P (Q : t -> _) R r,
  stable P Q R -> stableP (Q r) R.
Proof. unfold stable; propositional; eauto. Qed.
Local Hint Resolve stable_stableQ : core.

Lemma stable_stableP : forall (t : Set) P (Q : t -> _) R,
  stable P Q R -> stableP P R.
Proof. unfold stable; propositional; eauto. Qed.
Local Hint Resolve stable_stableP : core.

Lemma trc_imply :forall t R (s s' : t), R^* s s' ->
  forall (R':_->_->Prop), (forall s s', R s s' -> R' s s') ->
  R'^* s s'.
Proof. induct 1; simplify; eauto. Qed.

Local Hint Extern 1 (_ >= _) => linear_arithmetic : core.
Local Hint Constructors notAboutToFail : core.

(* HINT 1-6 (see Pset12Sig.v) *)

Ltac existT_subst :=
   repeat match goal with
   | [ H : existT _ _ _ = existT _ _ _ |- _ ] => eapply inj_pair2 in H
   end; subst.

Lemma progress :
  forall (t : Set) P (c : cmd t) R G Q,
    hoare_triple P R c G Q ->
    forall h, P h ->
         notAboutToFail c.
Proof.
  intros.
  induct H; simplify; eauto.
  { econstructor; eauto. }
  { simp. }
Qed.

Lemma trc_stableP :
  forall P R h h',
    (R) ^* h h'
    -> stableP P R
    -> P h
    -> P h'.
Proof.
  induct 1; simplify; eauto.
Qed.
  
Lemma trc_stableQ {t : Set} :
  forall (Q : t -> hprop) R h h' v,
    (R) ^* h h'
    -> stableQ Q R
    -> Q v h
    -> Q v h'.
Proof.
  induct 1; simplify; eauto.
  pose proof H1.
  eapply IHtrc in H3; eauto.
Qed.

Lemma guarantee :
  forall (t : Set) P (c : cmd t) R G Q,
    hoare_triple P R c G Q ->
    forall h,
      P h ->
      forall h' c',
        step (h, c) (h', c') ->
        G^* h h'.
Proof.
  induct 1; simplify.
  { invert H3; existT_subst.
    eapply IHhoare_triple; eauto.
    eauto. }
  { invert H5; existT_subst.
    apply H2 in H4.
    pose proof (IHhoare_triple1 _ H4 _ _ H8).
    eapply trc_imply; eauto.

    apply H3 in H4.
    pose proof (IHhoare_triple2 _ H4 _ _ H8).
    eapply trc_imply; eauto. }
  { eauto. }
  { invert H1. }
  { invert H3; existT_subst; eauto. }
  { invert H3; existT_subst; eauto. }
  { eapply trc_imply; eauto. }
Qed.

Lemma post_return :
  forall (t : Set) P R G Q (v : t) h h',
    hoare_triple P R (Return v) G Q
    -> (R) ^* h h'
    -> P h
    -> Q v h'.
Proof.
  induct 1; simplify.
  { propositional.
    eapply trc_stableP; eauto. }
  { apply H1.
    apply IHhoare_triple.
    eapply trc_imply; eauto.
    eauto. }
Qed.

Lemma preservation :
  forall (t : Set) P (c : cmd t) R G Q,
    hoare_triple P R c G Q ->
    forall h,
      P h ->
      forall h' c',
        step (h, c) (h', c') ->
        hoare_triple (fun h'' => R^* h' h'') R c' G Q.
Proof.    
  induct 1; simplify.
  { invert H3; existT_subst.
    eauto.
    specialize (H0 v0).
    econstructor.
    eauto.
    simplify.
    eapply post_return; eauto.
    all: eauto. }
  { invert H5; existT_subst.
    { econstructor.
      eapply IHhoare_triple1; eauto.
      eauto.
      eauto.
      { simplify; eapply trc_imply; eauto. }
      clear IHhoare_triple1.
      clear IHhoare_triple2.
      pose proof (guarantee _ _ _ _ _ _ H).
      pose proof (H2 _ H4).
      pose proof (H5 _ H6); clear H5.
      pose proof (H7 _ _ H8); clear H6.
      apply always_stableP in H0.
      apply H3 in H4.
      simplify.

      assert (stableP P2 R).
      { unfold stableP in *; simplify.
        eapply H0 in H9; eauto. }
      assert (stableP P2 G1).
      { unfold stableP in *; simplify.
        eapply H0 in H10; eauto. }
      pose proof trc_stableP.
      eapply H11.
      eapply H6.
      eauto.
      eapply H11.
      apply H5.
      eauto.
      eauto. }

    { econstructor.
      eauto.
      eapply IHhoare_triple2; eauto.
      eauto.
        
      clear IHhoare_triple1.
      clear IHhoare_triple2.
      pose proof (guarantee _ _ _ _ _ _ H0).
      pose proof (H3 _ H4).
      pose proof (H5 _ H6); clear H5.
      pose proof (H7 _ _ H8); clear H6.
      apply always_stableP in H.
      apply H2 in H4.
      simplify.

      assert (stableP P1 R).
      { unfold stableP in *; simplify.
        eapply H in H9; eauto. }
      assert (stableP P1 G2).
      { unfold stableP in *; simplify.
        eapply H in H10; eauto. }
      pose proof trc_stableP.
      eapply H11.
      eapply H6.
      eauto.
      eapply H11.
      apply H5.
      eauto.
      eauto.

      simplify; eapply trc_imply; eauto. }
  }
  { invert H0. }
  { invert H1. }
  { invert H3.
    existT_subst.
    econstructor.
    2: eauto.
    eauto.
    simplify.
    propositional; subst.
    invert H1.
    eapply trc_stableQ; eauto.
    eauto.
    eauto.
    eauto. }
  { induct H3; existT_subst.
    econstructor.
    specialize (H init).
    econstructor.
    eauto.
    simplify.
    apply always_stableP in H.
    unfold stableP in H.
    induct H3; simplify; eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    
    simplify.
    cases r; simplify.
    { econstructor; eauto.
      simplify.
      propositional.
      equality. }
    { econstructor; eauto. }
  }
  { econstructor.
    eapply IHhoare_triple; eauto.
    all: eauto.
    simplify.
    eapply trc_imply; eauto. }
Qed.

Theorem hoare_triple_sound' : forall (t : Set) P R (c : cmd t) G Q,
  hoare_triple P R c G Q ->
  forall h, P h ->
       invariantFor (trsys_of h c)
                    (fun st =>
                       exists P',
                         P' (fst st) /\
                         hoare_triple P' R (snd st) G Q).
Proof.
  simplify.

  apply invariant_induction; simplify.

  { propositional; subst; simplify; eauto. }
  { cases H1.
    destruct s as [h1 c1].
    destruct s' as [h2 c2].
    simplify.
    eexists.
    propositional.
    2: eapply preservation; eauto.
    simplify.
    eauto. }
Qed.    

Theorem hoare_triple_sound : forall (t : Set) P (c : cmd t) Q,
  hoare_triple P (fun _ _ => False) c (fun _ _ => True) Q ->
  forall h, P h ->
  invariantFor (trsys_of h c) (fun st => notAboutToFail (snd st)).
Proof.
  simplify.

  eapply invariant_weaken.
  eapply hoare_triple_sound'; eauto.

  simplify.
  cases H1.
  propositional.
  eapply progress; eauto.
Qed.

End Impl.

Module ImplCorrect : Pset12Sig.S := Impl.
