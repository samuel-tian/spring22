(*|
=============================================================
 6.822 Formal Reasoning About Programs, Spring 2022 - Pset 8
=============================================================
|*)

Require Import Pset8Sig.

(*|
Introduction
============

Computer programs commonly manipulate data from different sources, at different levels of privacy or trust.  An e-commerce website, for example, might keep track of the contents of each individual cart, and it would be a severe issue if one user got access to the content of another user's cart.

Such “information-flow” issues are of a different nature from the functionality bugs that we usually think of, but they are also pervasive and tricky to detect and fix: for example, for a few weeks in 2011, Facebook's abuse-reporting tool made it possible to access a user's private photos by reporting one of their *public* photos for abuse: the tool would then conveniently offer to report other photos, *including private ones* that the reporter was not allowed to access. (https://www.zdnet.com/article/facebook-flaw-allows-access-to-private-photos/)

In this pset, we will see how type systems can help with information-flow issues.  We will operate in a simplified setting in which all information is either “public” or “private”, and we will concern ourselves only with *confidentiality*, the property that private inputs should not influence public program outputs.

Informally, we'll prove the correctness of a type system such that type-safe programs do not leak private data: that is, we'll prove that changing the private inputs of a well-typed program does not change its public outputs.  We'll say that well-typed programs are “confidential”.

Note that this formulation doesn't rule out side channels: changing the private inputs of a program might change its runtime or even whether it terminates.

Language definition
===================

This is as usual:
|*)

Module Impl.
Inductive bop := Plus | Minus | Times.

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Bop (b : bop) (e1 e2 : arith).

Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Declare Scope  arith_scope.
Notation "a + b" := (Bop Plus a b) : arith_scope.
Notation "a - b" := (Bop Minus a b) : arith_scope.
Notation "a * b" := (Bop Times a b) : arith_scope.
Delimit Scope arith_scope with arith.

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (thn els : cmd)
| While (e : arith) (body : cmd).

(* Here are some notations for the language, which again we won't really
 * explain. *)
Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";;" := Sequence (at level 76). (* This one changed slightly, to avoid parsing clashes. *)
Notation "'when' e 'then' thn 'else' els 'done'" := (If e%arith thn els) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" := (While e%arith body) (at level 75).

(*|
Program semantics
=================

And the semantics of the language are as expected; the language is made deterministic by defaulting to 0 when a variable is undefined.
|*)

Definition valuation := fmap var nat.

Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Bop bp e1 e2 =>
    match bp with
    | Plus => Nat.add
    | Minus => Nat.sub
    | Times => Nat.mul
    end (interp e1 v) (interp e2 v)
  end.

Inductive eval : valuation -> cmd -> valuation -> Prop :=
| EvalSkip : forall v,
    eval v Skip v
| EvalAssign : forall v x e,
    eval v (Assign x e) (v $+ (x, interp e v))
| EvalSeq : forall v c1 v1 c2 v2,
    eval v c1 v1
    -> eval v1 c2 v2
    -> eval v (Sequence c1 c2) v2
| EvalIfTrue : forall v e thn els v',
    interp e v <> 0
    -> eval v thn v'
    -> eval v (If e thn els) v'
| EvalIfFalse : forall v e thn els v',
    interp e v = 0
    -> eval v els v'
    -> eval v (If e thn els) v'
| EvalWhileTrue : forall v e body v' v'',
    interp e v <> 0
    -> eval v body v'
    -> eval v' (While e body) v''
    -> eval v (While e body) v''
| EvalWhileFalse : forall v e body,
    interp e v = 0
    -> eval v (While e body) v.

(*|
Typing judgment
===============

The `Confidential` judgment below indicates that a program respects confidentiality.  It takes a set of public variables and a command and returns a `Prop` indicating whether the program is safe.  Take the time to understand exactly how `Confidential` works (or, even better, take a few moments to think how you would define a `Confidential` predicate).

In full generality, information-flow systems associate a label to each variable.  We'll simplify things and classify variables as “public” or “private”, and instead of having a map giving the label of each value, we'll keep track of the set of all public variables.

First, we need a way to collect the variables of an expression (we haven't seen the `set` type too often; see the tips in ``Pset8Sig.v`` for a quick recap).
|*)

Fixpoint vars (e: arith) : set var :=
  match e with
  | Const n => {} (** A constant has no variables **)
  | Var x => {x} (** A variable has… one variable! **)
  | Bop _ e1 e2 => vars e1 \cup vars e2 (** An operator's variables are the variables of its subterms **)
  end.

(*|
The parameter `pub` below represents the set of all public variables.  This is predeclared and fixed.  But there is also a distinct `set var` argument.  This is because we need to consider *implicit* as well as *explicit* flows.

- An explicit flow happens when assigning to a variable.  If `e` mentions variable `x`, then `y := e` may cause data to flow from `x` into `y`.  If `x` is private and `y` is public, we want to rule that out.

- An implicit flow happens when assigning to a variable *under a conditional*.  If `e` mentions variable `x`, then `when e then y := 1` may cause data to flow from `x` to `y` (can you see why?).  There, too, if `x` is private and `y` is public, we want to disallow this flow.

This is why we have the second `set var` (`pc`) argument below: in addition to the set of public variables, we keep track of the set of variables from which data may flow implicitly.  We call that set “pc”, for “program counter”.
|*)

Inductive Confidential (pub: set var) : set var (* pc *) -> cmd (* program *) -> Prop :=
| ConfidentialSkip : forall pc,
    Confidential pub pc Skip
(** A `Skip` is safe. **)
| ConfidentialAssignPrivate : forall pc x e,
    ~ x \in pub ->
    Confidential pub pc (Assign x e)
(** Assigning to a private variable is safe. **)
| ConfidentialAssignPublic : forall pc x e,
    vars e \subseteq pub ->
    pc \subseteq pub ->
    Confidential pub pc (Assign x e)
(** Assigning to a public variable variable is safe as long as the expression does not mention private variables and we are not under a conditional that depends on private variables. **)
| ConfidentialSeq : forall pc c1 c2,
    Confidential pub pc c1 ->
    Confidential pub pc c2 ->
    Confidential pub pc (Sequence c1 c2)
(** A sequence is safe if both halves of it are safe. **)
| ConfidentialIf : forall pc e thn els,
    Confidential pub (pc \cup vars e) thn ->
    Confidential pub (pc \cup vars e) els ->
    Confidential pub pc (If e thn els)
(** A conditional is safe if both branches are safe, noting that the branches run with additional variables in the `pc`. **)
| ConfidentialWhile : forall pc e body,
    Confidential pub (pc \cup vars e) body ->
    Confidential pub pc (While e body).
(** A while loop is safe if its body is safe, noting that the body runs with additional variables in the `pc`. **)

(*|
Here are a few examples:
|*)

Definition pub_example := {"x", "y", "z"}. (* Variables x, y, z are public. *)

Example confidential_prog :=
  ("x" <- "y" + 1;;
   "a" <- "a" * "b";;
   when "y" then "a" <- 0 else "b" <- 0 done).

Goal Confidential pub_example {} confidential_prog.
Proof.
  unfold confidential_prog, pub_example.
  apply ConfidentialSeq; simplify.
  - apply ConfidentialSeq; simplify.
    + apply ConfidentialAssignPublic; simplify.
      * sets.
      * sets.
    + apply ConfidentialAssignPrivate; simplify.
      sets.
  - apply ConfidentialIf; simplify.
    + apply ConfidentialAssignPrivate; simplify.
      sets.
    + apply ConfidentialAssignPrivate; simplify.
      sets.
Qed.

Example leaky_prog :=
  (when "a" then "x" <- 1 else "x" <- 2 done).

Goal ~ Confidential pub_example {} leaky_prog.
Proof.
  unfold leaky_prog, pub_example, not; simplify.
  invert H; simplify.
  invert H3; simplify.
  - sets.
  - pose proof @subseteq_In _ "a" _ _ H4.
    sets.
Qed.

(*|
Proof of noninterference
=========================

We first need a relation to characterize “equivalent” valuations — that is, valuations that agree on all public variables.  `restrict s m` means restrict the valuation `m` to just the keys in `s`:
|*)

Definition same_public_state pub (v1 v2: valuation) :=
  restrict pub v1 = restrict pub v2.

(* Before we get started proving properties of our type system, please read
 * Pset8Sig.v and consider the questions below. This task is
 * ungraded, but we are assigning it in hopes it helps you complete the
 * following parts.

 Suppose an expression contains only public variables. Under what valuations 
 do we expect them to evaluate to the same value?



 Suppose an expression evaluates to different values under different
 valuations. What do we know about this expression if the different valuations
 share the same public state? Do we know anything if the valuations do not 
 share the same public state?



 The noninterference property says that running a program in states with 
 private variables holding potentially different values does not change the 
 public outputs of the program.

 The key difficulty is to deal with *divergence* — the cases where the two 
 program executions take different paths.

 When does this happen?  How does that translate in terms of the variables
 in `pc`?
  
 Can a divergent execution affect the values of public variables?



 When a Confidential program executes, in what ways can it modify the 
 valuation? How does this depend on the values of `pc`?



 *)

(* HINT 1-2 (see Pset8Sig.v) *)

Lemma restrict_ne : forall (pub : set var) (v : valuation) x k,
    ~ x \in pub ->
            restrict pub (v $+ (x, k)) = restrict pub v.
Proof.
  intros.
  maps_equal.
  excluded_middle (k0 \in pub); simplify.
  { rewrite !lookup_restrict_true; sets.
    cases (k0 ==v x); simplify; equality. }
  { rewrite !lookup_restrict_false; sets. }
Qed.

Lemma restrict_not_equal : forall (pub : set var) (v : valuation) x k e,
    x <> k ->
    restrict pub (v $+ (x, e)) $? k = restrict pub v $? k.
Proof.
  intros.
  excluded_middle (k \in pub); simplify.
  { rewrite !lookup_restrict_true; eauto.
    simplify.
    equality. }
  { rewrite !lookup_restrict_false; eauto. }
Qed.

Lemma restrict_lookup : forall (pub : set var) (v : valuation) x n,
    restrict pub v $? x = Some n ->
    v $? x = Some n.
Proof.
  intros.
  excluded_middle (x \in pub); simplify.
  { sets.
    rewrite <- H.
    symmetry.
    apply lookup_restrict_true.
    assumption. }
  { sets.
    apply lookup_restrict_true_fwd in H.
    propositional. }
Qed.

Lemma restrict_none : forall (pub : set var) (v : valuation) x,
    restrict pub v $? x = None ->
    x \in pub ->
    v $? x = None.
Proof.
  intros.
  sets.
  rewrite <- H.
  symmetry.
  apply lookup_restrict_true.
  assumption.
Qed.
Local Hint Resolve restrict_lookup restrict_none : core.

Lemma restrict_subseteq : forall (pub : set var) (v1 v2 : valuation) e,
    vars e \subseteq pub ->
    restrict pub v1 = restrict pub v2 ->
    interp e v1 = interp e v2.
Proof.
  intros.
  assert (forall k, restrict pub v1 $? k = restrict pub v2 $? k) by equality.
  induct e; simplify; try equality.
  { specialize (H1 x).
    cases (restrict pub v1 $? x); simplify.
    { apply restrict_lookup in Heq.
      symmetry in H1.
      apply restrict_lookup in H1.
      rewrite Heq.
      rewrite H1.
      equality. }
    { sets.
      apply restrict_none in Heq; sets.
      symmetry in H1.
      apply restrict_none in H1; sets.
      rewrite Heq.
      rewrite H1.
      equality. }
  }
  { cases b; simplify;
      rewrite IHe1; sets;
      rewrite IHe2; sets. }
Qed.
Local Hint Resolve restrict_subseteq : core.

Ltac t := repeat match goal with
                 | [ H : eval _ _ _ |- _ ] => invert1 H
                 end.

Ltac dup H := match type of H with
              | ?X => assert (X) by assumption
              end.

Lemma no_public_assignments :
  forall pub pc v v' c,
    ~ pc \subseteq pub ->
    Confidential pub pc c ->
    eval v c v' ->
    same_public_state pub v v'.
Proof.
  intros.
  unfold same_public_state in *.
  
  generalize dependent v.
  generalize dependent v'.
  generalize dependent pub.
  generalize dependent pc.
    
  induct c; simplify; t.
  { equality. }
  { invert H0.
    rewrite !restrict_ne; eauto.
    propositional. }
  { invert H0.
    dup H.
    apply IHc1 with (v:=v) (v':=v1) in H; eauto.
    apply IHc2 with (v:=v1) (v':=v') in H0; eauto.
    rewrite H.
    assumption. }
  { invert H0.
    invert H1;
      assert (~ pc \cup vars e \subseteq pub) by sets; eauto. }
  { dup H0.
    invert H0.
    induct H1; simplify; try equality.
    { assert (restrict pub v = restrict pub v').
      { eapply IHc.
        2: eauto.
        sets.
        eauto. }
      assert (restrict pub v' = restrict pub v'').
      { assert ({ } \cup (pc \cup vars e) = (pc \cup vars e)) by sets.
        rewrite H3 in H5.
        eauto. }
      rewrite H1.
      assumption.
    }
  }
Qed.
Local Hint Resolve no_public_assignments : core.

Lemma non_interference_gen :
  forall pub pc c v1 v1' v2 v2',
    eval v1 c v1' ->
    eval v2 c v2' ->
    Confidential pub pc c ->
    same_public_state pub v1 v2 ->
    same_public_state pub v1' v2'.
Proof.
  simplify.
  unfold same_public_state in *.
  
  generalize dependent v1.
  generalize dependent v1'.
  generalize dependent v2.
  generalize dependent v2'.
  generalize dependent pub.
  generalize dependent pc.

  induct c; simplify; t.
  { eauto. }
  { invert H1.
    rewrite !restrict_ne; eauto.

    assert (interp e v1 = interp e v2) by eauto.
    rewrite H.
    maps_equal.
    cases (x ==v k); sets; simplify.
    { excluded_middle (k \in pub); simplify.
      { rewrite !lookup_restrict_true; eauto.
        simplify.
        equality. }
      { rewrite !lookup_restrict_false; eauto. }
    }
    { excluded_middle (k \in pub); simplify.
      { rewrite !lookup_restrict_true; eauto.
        simplify.
        assert (restrict pub v1 $? k = restrict pub v2 $? k) by equality.
        rewrite !lookup_restrict_true in H1; eauto. }
      { rewrite !lookup_restrict_false; eauto. }
    }
  }
  { invert H1.
    eauto. }
  { invert H1.
    invert H; invert H0; simplify.
    { eauto. }
    { assert (~ pc \cup vars e \subseteq pub).
      { propositional.
        assert (vars e \subseteq pub) by sets.
        assert (interp e v1 = interp e v2) by eauto.
        linear_arithmetic. }
      assert (same_public_state pub v1 v1') by eauto.
      assert ({ } \cup (pc \cup vars e) = (pc \cup vars e)) by sets.
      rewrite H1 in H8.
      assert (same_public_state pub v2 v2') by eauto.
      unfold same_public_state in *.
      rewrite <- H0.
      rewrite <- H3.
      assumption. }
    { assert (~ pc \cup vars e \subseteq pub).
      { propositional.
        assert (vars e \subseteq pub) by sets.
        assert (interp e v1 = interp e v2) by eauto.
        linear_arithmetic. }
      assert (same_public_state pub v2 v2') by eauto.
      assert ({ } \cup (pc \cup vars e) = (pc \cup vars e)) by sets.
      rewrite H1 in H8.
      assert (same_public_state pub v1 v1') by eauto.
      unfold same_public_state in *.
      rewrite <- H0.
      rewrite <- H3.
      assumption. }
    { eauto. }
  }
  { generalize dependent v2.
    generalize dependent v2'.

    dup H1.
    invert H1.
    dup H.
    induct H; simplify.
    { dup H5.
      induct H5; simplify.
      { assert (restrict pub v' = restrict pub v'0) by eauto.
        eapply IHeval2.
        7: eauto.
        all: eauto.
        replace (pc \cup vars e) with ({ } \cup (pc \cup vars e)) by sets.
        assumption. }
      { assert (restrict pub v = restrict pub v').
        { eapply no_public_assignments.
          3: eauto.
          2: eauto.
          propositional.
          assert (interp e v = interp e v0).
          { eapply restrict_subseteq.
            assert (vars e \subseteq pub) by sets.
            eauto.
            eauto. }
          linear_arithmetic.
        }
        eapply IHeval2; eauto.
        replace (pc \cup vars e) with ({ } \cup (pc \cup vars e)) by sets.
        eauto.
        rewrite <- H8.
        assumption. }
    }
    { dup H2.
      induct H2; simplify.
      { assert (restrict pub v0 = restrict pub v').
        { eapply no_public_assignments.
          3: eauto.
          2: eauto.
          propositional.
          assert (interp e v = interp e v0).
          { eapply restrict_subseteq.
            assert (vars e \subseteq pub) by sets.
            eauto.
            eauto. }
          linear_arithmetic.
        }
        eapply IHeval2; eauto.
        rewrite <- H6.
        assumption. }
      { eauto. }
    }
  }
Qed.

Theorem non_interference :
  forall pub c v1 v1' v2 v2',
    eval v1 c v1' ->
    eval v2 c v2' ->
    Confidential pub {} c ->
    same_public_state pub v1 v2 ->
    same_public_state pub v1' v2'.
Proof.
  simplify.
  eapply non_interference_gen; eauto.
Qed.

(*|
Congratulations, you have proved that our type system is *sound*: it catches all leaky programs!  But it is not *complete*: there are some good programs that it rejects, too.  In other words, it *overapproximates* the set of unsafe programs.

Can you give an example of a safe program (a program that does not leak data) that our system would reject?
|*)

Definition tricky_example : cmd :=
  "x" <- "a";; "x" <- 1.

Lemma tricky_rejected : ~ Confidential pub_example {} tricky_example.
Proof.
  unfold tricky_example.
  unfold pub_example.
  propositional.
  invert H.
  invert H3.
  sets.
  simplify.
  sets.
  specialize (H2 "a").
  propositional; discriminate.
Qed.

Lemma tricky_confidential :
  forall v1 v1' v2 v2',
    eval v1 tricky_example v1' ->
    eval v2 tricky_example v2' ->
    same_public_state pub_example v1 v2 ->
    same_public_state pub_example v1' v2'.
Proof.
  simplify.
  unfold tricky_example in *.
  unfold pub_example in *.
  unfold same_public_state in *.
  repeat match goal with
         | [ H : eval _ _ _ |- _ ] => invert1 H
         end; simplify.
  assert (v1 $+ ("x", match v1 $? "a" with
                 | Some n => n
                 | None => 0
                      end) $+ ("x", 1) = v1 $+ ("x", 1)) by maps_equal.
  rewrite H.
  assert (v2 $+ ("x", match v2 $? "a" with
                 | Some n => n
                 | None => 0
                      end) $+ ("x", 1) = v2 $+ ("x", 1)) by maps_equal.
  rewrite H0.
  maps_equal.
  assert (restrict {"x", "y", "z"} v1 $? k = restrict {"x", "y", "z"} v2 $? k) by equality.
  excluded_middle (k \in {"x", "y", "z"}).
  { rewrite !lookup_restrict_true in H2; sets.
    rewrite !lookup_restrict_true; sets; simplify; equality.
    rewrite !lookup_restrict_true; sets; simplify; equality.
    rewrite !lookup_restrict_true; sets; simplify; equality. }
  { rewrite !lookup_restrict_false; sets. }
Qed.

End Impl.

Module ImplCorrect : Pset8Sig.S := Impl.

(* Authors:
   Clément Pit-Claudel 
   Amanda Liu *)
