(** * 6.822 Formal Reasoning About Programs, Spring 2022 - Pset 3 *)

Require Import Frap.Frap.
Require Import Pset3Sig.

Module Impl.
  (* In this pset, we will practice two topics:
     1) Polymorphic container types, i.e. types parametrized by types,
        such as "option A", "list A", "tree A", and finally, "bitwise_trie A",
        which combines option and tree to obtain a new useful data structure.
     2) Higher-order functions (HOFs), i.e. functions that take other functions
        as arguments.

     Once again we have posted some general tips for advancing in this lab near
     the bottom of the signature file under "TIPS". Below the tips are a set of
     problem-specific, spoiler hints that will help you with these problems. Try
     only to consult these if you get stuck!
  *)

  (* As usual, the grading rubric for this pset is in Pset3Sig.v. *)

  (** ** Higher-order functions **)

  (* Recall the identity function [id] we used in class, which just returns its
     argument without modification: *)
  Definition id {A : Type} (x : A) : A := x.

  (* We also saw [compose], another higher-order function: [compose g f]
   * applies [f] to its input and then applies [g]. Argument order
   * follows the general convention of functional composition in
   * mathematics denoted by the small circle.
   *)
  Definition compose {A B C : Type} (g : B -> C) (f : A -> B) (x : A) : C := g (f x).

  (* Let's use a small circle to refer to [compose]. This will make our
     goals much more readable.
     It's up to you to decide whether you also want to use the circle notation
     in your definitions or whether you prefer to write "compose".

     Users of Emacs with company-coq can simply type \circ RET
     to insert ∘ *)
  Notation " g ∘ f " := (compose g f) (at level 40, left associativity).

  (* Here are three simple properties of function composition.
     Together, these properties mean that functions with ∘ form
     a “monoid”. *)

  (* Hint: In the following, it might be helpful to use the following fact:
     If two functions return the same value for all inputs, they are the same. *)
  Check @FunctionalExtensionality.functional_extensionality.
  (* Aside: We called it a "fact" above, but logicians disagree about whether
     we should believe this or not -- maybe you remember Adam's argument from
     class that even if merge sort and bubble sort return the same result for
     all inputs, they are two different things.
     Therefore, this "fact" is not actually built into Coq's kernel, but it's
     an axiom written down in the standard library, and if you believe in it,
     you can import it (the Frap library already does so).
     In any case, it is consistent with the rest of Coq's logic, i.e. by
     assuming this axiom, you will not be able to prove False, so we're safe.*)

  (* Let's make a shorthand for this: *)
  Definition fun_ext := @FunctionalExtensionality.functional_extensionality.

  Lemma compose_id_l : forall A B (f: A -> B),
      id ∘ f = f.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Proof. equality. Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Proof.
  Admitted.
     END HANDOUT *)

  Lemma compose_id_r : forall A B (f: A -> B),
      f ∘ id = f.
  (* BEGIN SOLUTION *)
  Proof. equality. Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Proof.
  Admitted.
     END HANDOUT *)

  Lemma compose_assoc : forall A B C D (f: A -> B) (g: B -> C) (h: C -> D),
      h ∘ (g ∘ f) = h ∘ g ∘ f.
  (* BEGIN SOLUTION *)
  Proof. equality. Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Proof.
  Admitted.
     END HANDOUT *)
=======
  Proof.
  Admitted.

  Lemma compose_id_r : forall A B (f: A -> B),
      f ∘ id = f.
  Proof.
  Admitted.

  Lemma compose_assoc : forall A B C D (f: A -> B) (g: B -> C) (h: C -> D),
      h ∘ (g ∘ f) = h ∘ g ∘ f.
  Proof.
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* The selfCompose function takes a function and applies this function n times
     to the argument. There are different ways of defining it, but let's
     define it using only [id] and [compose]. *)
  Fixpoint selfCompose{A: Type}(f: A -> A)(n: nat): A -> A :=
    match n with
    | O => id
    | S n' => f ∘ (selfCompose f n')
    end.

  (* Here's an example of what [selfCompose] can do:
     If we apply the function that adds 2 to its argument 7 times to the starting
     value 3, we obtain 3 + 7 * 2 = 17. *)
  Example selfCompose_plus1: selfCompose (plus 2) 7 3 = 17. Proof. equality. Qed.

  (* We can also use [selfCompose] to define exponentiation on natural numbers, by
     saying "to raise [base] to the power [e], apply the function that multiplies
     its argument by [base] to [1] [e] times".
     Define [exp] using [selfCompose] and [Nat.mul]. *)
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Definition exp(base e: nat): nat := selfCompose (Nat.mul base) e 1.

  Lemma test_exp_3_2: exp 3 2 = 9. Proof. equality. Qed.
  Lemma test_exp_4_1: exp 4 1 = 4. Proof. equality. Qed.
  Lemma test_exp_5_0: exp 5 0 = 1. Proof. equality. Qed.
  Lemma test_exp_1_3: exp 1 3 = 1. Proof. equality. Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
=======
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a
  Definition exp(base e: nat): nat. Admitted.

  (* Once you define [exp], you can replace [Admitted.] below by [Proof. equality. Qed.] *)
  Lemma test_exp_2_3: exp 2 3 = 8. Admitted.
  Lemma test_exp_3_2: exp 3 2 = 9. Admitted.
  Lemma test_exp_4_1: exp 4 1 = 4. Admitted.
  Lemma test_exp_5_0: exp 5 0 = 1. Admitted.
  Lemma test_exp_1_3: exp 1 3 = 1. Admitted.
<<<<<<< HEAD
     END HANDOUT *)
=======
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* And here's another example to illustrate [selfCompose]. Make sure you understand
     why its result is 256. *)
  Example selfCompose_square: selfCompose (fun (x: nat) => x * x) 3 2 = 256. Proof. equality. Qed.

  (** ** Inverse functions **)

  (* Using [compose] and [id], we can write a concise definition of when
     a function [g] is the left inverse of a function [f]: *)
  Definition left_inverse{A B: Type}(f: A -> B)(g: B -> A): Prop := g ∘ f = id.

  (* Here's an example: The function that subtracts two from its argument
     is the left inverse of the function that adds two to its argument. *)
  Example plus2minus2: left_inverse (fun (x: nat) => x + 2) (fun (x: nat) => x - 2).
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    unfold left_inverse, compose, id.
    apply fun_ext.
    simplify.
    linear_arithmetic.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* On the other hand, note that the other direction does not hold, because
     if a subtraction on natural numbers underflows, it just returns 0, so
     there are several [x] for which [x-2] returns 0 (namely 0, 1, and 2),
     so it can't have a left inverse. *)
  Example minus2plus2: ~ left_inverse (fun (x: nat) => x - 2) (fun (x: nat) => x + 2).
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    unfold left_inverse.
    unfold not, compose.
    simplify.
    assert ((fun x : nat => x - 2 + 2) 0 = id 0). {
      rewrite <- H.
      equality.
    }
    unfold id in *.
    simplify.
    linear_arithmetic.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Let us make the intuition from the previous paragraph more
     concrete, by proving that a function that is not injective
     cannot have a left inverse; or, in other words, that
     functions with left inverses are injective. *)

  (* HINT 1 (see Pset3Sig.v) *)
  Lemma left_invertible_injective {A}:
    forall (f g: A -> A),
      left_inverse f g ->
      (forall x y, f x = f y -> x = y).
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    unfold left_inverse; simplify.
    replace x with ((g ∘ f) x) by (rewrite H; equality).
    replace y with ((g ∘ f) y) by (rewrite H; equality).
    unfold compose.
    equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Bonus question (no points): can you prove the reverse;
     i.e., can you prove that all injective functions have left
     inverses? *)

  (* The identity function is the inverse of itself.
     Note: we're using "@" in front of "id" to say "we want to provide all implicit
     type arguments explicitly, because otherwise Coq would not be able to infer them." *)
  Lemma left_inverse_id: forall A, left_inverse (@id A) (@id A).
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    unfold left_inverse, id. simplify. equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)

  (* BEGIN SOLUTION *)
  (* Note: Coming up with this helper lemma is one of the key insights for
     proving [invert_selfCompose]. *)
  Lemma selfCompose_succ_alt{A: Type}: forall (g: A -> A) (n: nat),
      g ∘ selfCompose g n = selfCompose g n ∘ g.
  Proof.
    induct n; simplify.
    - unfold id, compose. equality.
    - rewrite <- compose_assoc.
      f_equal.
      assumption.
  Qed.
  (* END SOLUTION *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Now we can start proving interesting facts about inverse functions: *)
  (* Here's how to invert the power function: *)
  (* HINT 2 (see Pset3Sig.v) *)  
  Lemma invert_selfCompose{A: Type}: forall (f g: A -> A) (n: nat),
      left_inverse f g ->
      left_inverse (selfCompose f n) (selfCompose g n).
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    induct n; simplify.
    - apply left_inverse_id.
    - unfold left_inverse in *.
      rewrite selfCompose_succ_alt.
      rewrite compose_assoc.
      replace (selfCompose g n ∘ g ∘ f ∘ selfCompose f n) with
          (selfCompose g n ∘ (g ∘ f) ∘ selfCompose f n). 2: {
        rewrite compose_assoc.
        equality.
      }
      rewrite H.
      rewrite compose_id_r.
      apply IHn.
      trivial.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (** ** Polymorphic container types *)

  (* First, we'll reproduce some definitions we need from Lecture 2,
     [tree] and [flatten]: *)

  Inductive tree {A} :=
  | Leaf
  | Node (l : tree) (d : A) (r : tree).
  Arguments tree : clear implicits.

  Fixpoint flatten {A} (t : tree A) : list A :=
    match t with
    | Leaf => []
    | Node l d r => flatten l ++ d :: flatten r
    end.

  (* Bitwise trie are finite maps keyed by lists of Booleans.
   * We will implement a bitwise trie with entries of type [A]
   * by [tree (option A)]. The value at the root of the tree
   * corresponds to the entry for the key [nil : list bool],
   * the left subtree contains entries for those keys that
   * begin with [true], and the right subtree contains entries
   * for those keys that begin with [false].
   *
   * Tries are a common and powerful data structure; you can read
   * more about them at https://en.wikipedia.org/wiki/Trie .
   *)
  Definition bitwise_trie A := tree (option A).

  (* Define [lookup] such that [lookup k t] looks up the
   * map entry corresponding to the key [k : list bool] in the
   * bitwise trie [t : bitwise_trie A], interpreting [t] such that
   * the value at the root of [t] corresponds to the
   * entry for the key [nil], the left subtree contains entries
   * for those keys that begin with [true], and the right subtree
   * contains entries for those keys that begin with [false].
   *
   * Look at the examples below to get a better sense of what
   * this operation does: the argument [k] is a path, in which
   * [true] means "go left" and [false] means "go right".
   *)
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Fixpoint lookup {A} (k : list bool) (t : bitwise_trie A) {struct t} : option A :=
    match t with
    | Leaf => None
    | Node l d r =>
      match k with
      | [] => d
      | x :: k' => lookup k' (if x then l else r)
      end
    end.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Fixpoint lookup {A} (k : list bool) (t : bitwise_trie A) {struct t} : option A. Admitted.
     END HANDOUT *)

  Example lookup_example1 : lookup [] (Node Leaf (None : option nat) Leaf) = None.
  Proof.
  (* BEGIN SOLUTION *)
    simplify.
    equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)
=======
  Fixpoint lookup {A} (k : list bool) (t : bitwise_trie A) {struct t} : option A. Admitted.

  Example lookup_example1 : lookup [] (Node Leaf (None : option nat) Leaf) = None.
  Proof.
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  Example lookup_example2 : lookup [false; true]
      (Node (Node Leaf (Some 2) Leaf) None (Node (Node Leaf (Some 1) Leaf) (Some 3) Leaf))
                            = Some 1.
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    simplify.
    equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* [Leaf] represents an empty bitwise trie, so a lookup for
   * any key should return [None].
   *)
  Theorem lookup_empty {A} (k : list bool)
    : lookup k (Leaf : bitwise_trie A) = None.
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    simplify.
    equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)

  (* HINT 3 (see Pset3Sig.v) *)
  (* BEGIN SOLUTION *)
  (* Note: not a top-level definition.
   * [build_singleton k v] builds a bitwise trie whose only entry is
   * (k, v).
   *)
  Fixpoint build_singleton {A} (k : list bool) (v : option A) : bitwise_trie A :=
    match k with
    | [] => Node Leaf v Leaf
    | x :: k' => let branch := build_singleton k' v in
                 if x then Node branch None Leaf
                 else Node Leaf None branch
    end.
  (* END SOLUTION *)
=======
  Admitted.

  (* HINT 3 (see Pset3Sig.v) *)
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Define an operation to "insert" a key and optional value
   * into a bitwise trie. The [insert] definition should satisfy two
   * properties: one is [lookup_insert] below, which says that if we
   * look up a key [k] in a trie where [(k, v)] has just been inserted,
   * the result should be [v]. The other is that lookups on keys different
   * from the one just inserted should be the same as on the original map.
   *
   * If an entry for that key already exists, [insert] should replace
   * that entry with the new one being inserted. Note that [insert] can
   * be used to remove an entry from the trie, too, by inserting [None]
   * as the value.
   *
   * Hint: it may be helpful to define an auxiliary function
   * that creates a singleton tree (a tree containing a single
   * key-value pair).
   *)
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Fixpoint insert {A} (k : list bool) (v : option A) (t : bitwise_trie A) {struct t}
    : bitwise_trie A :=
    match t with
    | Leaf => build_singleton k v
    | Node l d r =>
      match k with
      | [] => Node l v r
      | x :: k' => if x
                   then Node (insert k' v l) d r
                   else Node l d (insert k' v r)
      end
    end.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Fixpoint insert {A} (k : list bool) (v : option A) (t : bitwise_trie A) {struct t}
    : bitwise_trie A. Admitted.
     END HANDOUT *)

  Example insert_example1 : lookup [] (insert [] None (Node Leaf (Some 0) Leaf)) = None.
  Proof.
  (* BEGIN SOLUTION *)
    simplify.
    equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)

  Example insert_example2 : lookup [] (insert [true] (Some 2) (Node Leaf (Some 0) Leaf)) = Some 0.
  Proof.
  (* BEGIN SOLUTION *)
    simplify.
    equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)

  (* BEGIN SOLUTION *)
  (* Note: This helper lemma is not mentioned in the handout or Sig file. *)
  Lemma lookup_build_singleton {A} (k : list bool) (v : option A)
    : lookup k (build_singleton k v) = v.
  Proof.
    induct k.
    - simplify.
      equality.
    - cases a.
      + apply IHk.
      + apply IHk.
  Qed.
  
  (* HINT 4 (see Pset3Sig.v) *) 
  (* END SOLUTION *)
  Theorem lookup_insert {A} (k : list bool) (v : option A) (t : bitwise_trie A) :
    lookup k (insert k v t) = v.
  Proof.
  (* BEGIN SOLUTION *)
    induct k; cases t; simplify.
    all: try equality.
    all: cases a; simplify; auto using lookup_build_singleton.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)
=======
  Fixpoint insert {A} (k : list bool) (v : option A) (t : bitwise_trie A) {struct t}
    : bitwise_trie A. Admitted.

  Example insert_example1 : lookup [] (insert [] None (Node Leaf (Some 0) Leaf)) = None.
  Proof.
  Admitted.

  Example insert_example2 : lookup [] (insert [true] (Some 2) (Node Leaf (Some 0) Leaf)) = Some 0.
  Proof.
  Admitted.
  
  (* HINT 4 (see Pset3Sig.v) *) 
  Theorem lookup_insert {A} (k : list bool) (v : option A) (t : bitwise_trie A) :
    lookup k (insert k v t) = v.
  Proof.
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Define an operation to "merge" that takes two bitwise tries and merges
   * them together. The [merge] definition should combine two bitwise tries, 
   * preferring map entries from the first bitwise trie when an entry exists 
   * for both bitwise tries.
   *
   * The [merge] definition should satisfy three properties: one is 
   * [left_lookup_merge], which says that if a trie contains an entry [v] for a
   * key [k], then when this trie is the first trie in a merge with any other 
   * trie, then the resulting merged trie also contains an entry [v] for key [k].
   * The other [lookup_merge_None] says that if the merge of two tries 
   * contains no entry for a given key [k], then neither did the two original
   * tries. The final is [merge_selfCompose], which says that if you repeatedly
   * merge one trie with another one or more times, it is the same as merging
   * the tries once.
   *)
  
<<<<<<< HEAD
  (* BEGIN HANDOUT
  Fixpoint merge {A} (t1 t2 : bitwise_trie A) : bitwise_trie A. Admitted.    
     END HANDOUT *)
  
  (* BEGIN SOLUTION *)
  Fixpoint merge {A} (t1 t2 : bitwise_trie A) :=
    match t1 with
    | Node l1 (Some v1) r1 =>
          match t2 with
          | Node l2 (Some v2) r2 => Node (merge l1 l2) (Some v1) (merge r1 r2)
          | Node l2 None r2 => Node (merge l1 l2) (Some v1) (merge r1 r2)
          | Leaf => t1
          end
    | Node l1 None r1 =>
          match t2 with
          | Node l2 (Some v2) r2 => Node (merge l1 l2) (Some v2) (merge r1 r2)
          | Node l2 None r2 => Node (merge l1 l2) None (merge r1 r2)
          | Leaf => t1
          end      
    | Leaf => t2
    end.
  (* END SOLUTION *)

  (* BEGIN SOLUTION *)
  Example merge_example1 :
    merge (Node Leaf (Some 1) Leaf) (Node Leaf (Some 2) Leaf) =
    Node Leaf (Some 1) Leaf.
  Proof. equality. Qed.
  Example merge_example2 :
    merge Leaf (Node Leaf (@None nat) Leaf) = Node Leaf None Leaf.
  Proof. equality. Qed.
  Example merge_example3 :
    merge (Node Leaf None Leaf) (Node Leaf (Some 2) Leaf) =
    Node Leaf (Some 2) Leaf.
  Proof. equality. Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Lemma merge_test1 :
    merge (Node Leaf (Some 1) Leaf) (Node Leaf (Some 2) Leaf) =
    Node Leaf (Some 1) Leaf.
  Proof. Admitted.
  Lemma merge_test2 :
    merge Leaf (Node Leaf (@None nat) Leaf) = Node Leaf None Leaf.
  Proof. Admitted.
  Lemma merge_test3 :
    merge (Node Leaf None Leaf) (Node Leaf (Some 2) Leaf) =
    Node Leaf (Some 2) Leaf.
  Proof. Admitted.
  END HANDOUT *)
=======
  Fixpoint merge {A} (t1 t2 : bitwise_trie A) : bitwise_trie A. Admitted.    
  Lemma merge_example1 :
    merge (Node Leaf (Some 1) Leaf) (Node Leaf (Some 2) Leaf) =
    Node Leaf (Some 1) Leaf.
  Proof. Admitted.
  Lemma merge_example2 :
    merge Leaf (Node Leaf (@None nat) Leaf) = Node Leaf None Leaf.
  Proof. Admitted.
  Lemma merge_example3 :
    merge (Node Leaf None Leaf) (Node Leaf (Some 2) Leaf) =
    Node Leaf (Some 2) Leaf.
  Proof. Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a
    
  Theorem left_lookup_merge {A} : forall (t1 t2 : bitwise_trie A) k v,
      lookup k t1 = Some v ->
      lookup k (merge t1 t2) = Some v.
  Proof.
<<<<<<< HEAD
    (* BEGIN SOLUTION *)
    induct t1; simplify.
    - equality.
    - cases t2; cases k; simplify; subst.
      + equality.
      + cases b; cases d; simplify; equality.
      + cases d0; equality.
      + cases b; cases d; cases d0; simplify; auto; equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
  END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  Theorem lookup_merge_None {A} : forall (t1 t2 : bitwise_trie A) k,
      lookup k (merge t1 t2) = None ->
      lookup k t1 = None /\ lookup k t2 = None.
  Proof.
<<<<<<< HEAD
    (* BEGIN SOLUTION *)
    induct t1; simplify.
    - propositional.
    - cases k; cases d; cases t2; simplify; propositional.
      + cases d; simplify; equality.
      + cases d; simplify; equality.
      + cases d; simplify; equality.
      + cases d; cases b; simplify.
        apply IHt1_1 in H. propositional.
        apply IHt1_2 in H. propositional.
        apply IHt1_1 in H. propositional.
        apply IHt1_2 in H. propositional.
      + cases d; cases b; simplify.
        apply IHt1_1 in H. propositional.
        apply IHt1_2 in H. propositional.
        apply IHt1_1 in H. propositional.
        apply IHt1_2 in H. propositional.
      + cases d; cases b; simplify.
        apply IHt1_1 in H. propositional.
        apply IHt1_2 in H. propositional.
        apply IHt1_1 in H. propositional.
        apply IHt1_2 in H. propositional.
      + cases d; cases b; simplify.
        apply IHt1_1 in H. propositional.
        apply IHt1_2 in H. propositional.
        apply IHt1_1 in H. propositional.
        apply IHt1_2 in H. propositional.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
  END HANDOUT *)
  
  (* BEGIN SOLUTION *)
  Lemma merge_id {A} : forall (t1 : bitwise_trie A),
      merge t1 t1 = t1.
  Proof.
    induct t1; try cases d; simplify; equality.
  Qed.

  Lemma merge_idempotent {A} : forall (t1 t2 : bitwise_trie A),
      merge t1 (merge t1 t2) = merge t1 t2.
  Proof.
    induct t1; simplify.
    - equality.
    - cases d; cases t2; try cases d; simplify; try equality;
      f_equal; apply merge_id.
  Qed.
  (* END SOLUTION *)

=======
  Admitted.
  
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a
  (* HINT 5 (see Pset3Sig.v) *)
  Theorem merge_selfCompose {A} : forall n (t1 t2 : bitwise_trie A),
      0 < n ->
      selfCompose (merge t1) n t2 = merge t1 t2.
  Proof.
<<<<<<< HEAD
    (* BEGIN SOLUTION *)
    induct n; simplify.
    - linear_arithmetic.
    - unfold compose.      
      cases n.
      + simplify. equality.
      + rewrite IHn.
        apply merge_idempotent.
        linear_arithmetic.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
  END HANDOUT *)

=======
  Admitted.
  
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a
  (* Define an operation to "mirror" that takes a tree (not necessarily a 
   * trie) and returns the mirrored version of the tree.
   *
   * The [mirror] definition should satisfy two properties: one is 
   * [mirror_mirror_id], which says that if you mirror a tree twice, it
   * results in the original tree. The other is [flatten_mirror_rev] which
   * states that flattening a mirrored tree is equivalent to reversing the
   * list resulting from the flattening of that same tree.
 *)
  
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Fixpoint mirror {A} (t : tree A) : tree A :=
    match t with
    | Node l v r => Node (mirror r) v (mirror l)
    | _ => t
    end.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
   Fixpoint mirror {A} (t : tree A) : tree A. Admitted.     
   END HANDOUT *)
=======
  Fixpoint mirror {A} (t : tree A) : tree A. Admitted.     
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  Example mirror_test1 :
    mirror (Node Leaf 1 (Node Leaf 2 (Node Leaf 3 Leaf))) =
    Node (Node (Node Leaf 3 Leaf) 2 Leaf) 1 Leaf.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Proof. equality. Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT 
  Admitted.
  END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a
  
  Theorem mirror_mirror_id {A} : forall (t : tree A),
      mirror (mirror t) = t.
  Proof.
<<<<<<< HEAD
    (* BEGIN SOLUTION *)
    induct t; simplify; equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
  END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a
  
  Theorem flatten_mirror_rev {A} : forall (t : tree A),
      flatten (mirror t) = rev (flatten t).
  Proof.
<<<<<<< HEAD
    (* BEGIN SOLUTION *)
    induct t; simplify.
    - equality.
    - rewrite IHt2.
      rewrite rev_app_distr.
      simplify.
      rewrite app_assoc_reverse.
      simplify.
      equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
  END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (** ** HOFs on lists and trees **)
  
  (* Just like we defined [map] for lists, we can similarly define
   * a higher-order function [tree_map] that applies a function on
   * elements to all of the elements in the tree, leaving the tree
   * structure intact.
   *)
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Fixpoint tree_map {A B : Type} (f : A -> B) (t : tree A)
    : tree B :=
    match t with
    | Leaf => Leaf
    | Node l d r => Node (tree_map f l) (f d) (tree_map f r)
    end.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Fixpoint tree_map {A B : Type} (f : A -> B) (t : tree A)
    : tree B. Admitted.
     END HANDOUT *)
=======
  Fixpoint tree_map {A B : Type} (f : A -> B) (t : tree A)
    : tree B. Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  Example tree_map_example :
    tree_map (fun x => x + 1) (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 (Node Leaf 4 Leaf)))
    = (Node (Node Leaf 2 Leaf) 3 (Node Leaf 4 (Node Leaf 5 Leaf))).
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    simplify.
    equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)

  (* BEGIN SOLUTION *)
  (* Note: This helper lemma is not mentioned in the handout or Sig file. *)
  Lemma map_append : forall {A B : Type} (f : A -> B) (xs ys : list A),
      map f (xs ++ ys) = map f xs ++ map f ys.
  Proof.
    induct xs.
    - simplify.
      equality.
    - simplify.
      rewrite IHxs.
      equality.
  Qed.

  (* END SOLUTION *)
=======
  Admitted.

>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a
  (* [tree_map_flatten] shows that [map]
   * and [tree_map] are related by the [flatten] function.
   *)
  (* HINT 6 (see Pset3Sig.v) *)
  Theorem tree_map_flatten : forall {A B : Type} (f : A -> B) (t : tree A),
      flatten (tree_map f t) = map f (flatten t).
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    induct t.
    - simplify.
      equality.
    - simplify.
      rewrite IHt1.
      rewrite IHt2.
      rewrite map_append.
      equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* This function asserts that a predicate holds over all
     elements of a tree. *)
  Fixpoint tree_forall {A} (P: A -> Prop) (tr: tree A) :=
    match tr with
    | Leaf => True
    | Node l d r => tree_forall P l /\ P d /\ tree_forall P r
    end.

  (* Define a similar function for the [exists] case; that is, define
     a function that asserts that a predicate holds for at least
     one value of a tree. *)
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Fixpoint tree_exists {A} (P: A -> Prop) (tr: tree A) {struct tr} :=
    match tr with
    | Leaf => False
    | Node l d r => tree_exists P l \/ P d \/ tree_exists P r
    end.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Fixpoint tree_exists {A} (P: A -> Prop) (tr: tree A) {struct tr} : Prop.
  Admitted.
     END HANDOUT *)
=======
  Fixpoint tree_exists {A} (P: A -> Prop) (tr: tree A) {struct tr} : Prop.
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Two sanity checks for your function: *)
  Lemma tree_exists_Leaf {A} (P: A -> Prop):
    ~ tree_exists P Leaf.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Proof. unfold tree_exists; propositional. Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Proof.
  Admitted.
     END HANDOUT *)

  Lemma tree_forall_exists {A} (P: A -> Prop):
    forall tr, tr <> Leaf -> tree_forall P tr -> tree_exists P tr.
  (* BEGIN SOLUTION *)
  Proof. simplify; cases tr; simplify; propositional. Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Proof.
  Admitted.
     END HANDOUT *)
=======
  Proof.
  Admitted.

  Lemma tree_forall_exists {A} (P: A -> Prop):
    forall tr, tr <> Leaf -> tree_forall P tr -> tree_exists P tr.
  Proof.
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* What does the following theorem mean? Write a short
     explanation below. *)

<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  (* “If an element [a] is in a tree [tr] and [tree_forall P tr]
     holds, then [P a] holds” *)
  (* END SOLUTION *)

=======
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a
  Lemma tree_forall_sound {A} (P: A -> Prop):
    forall tr, tree_forall P tr ->
          forall d, tree_exists (fun d' => d' = d) tr ->
               P d.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Proof. induct tr; simplify; propositional; subst; first_order. Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Proof.
  Admitted.
     END HANDOUT *)
=======
  Proof.
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (** ** Binary search trees **)

  (* Like tries, binary search trees (BSTs) are a popular way to
     store structured data.  We will use them to implement a set
     data type, with methods to insert a new element, remove an
     existing element, and check whether the set contains a
     given element.

     Proving a complete BST implementation in a week is a bit
     too much at this point in the term, so we will start this
     week with definitions and correctness proofs for membership
     tests. *)

  (* BSTs will allow us to illustrate an important idea: data
     abstraction, the general principle that data structures
     should expose interfaces that abstract over (i.e., hide)
     the complexities of their internal representation.  Data
     abstraction is a key ingredient of modularity in most
     programming languages.  (We have a lecure on it coming in
     a week.)

     Concretely, this means that client code using our set
     library built with BSTs shouldn't have to think about
     binary trees at all: instead, we'll write all specs in
     terms of abstract sets, representing a set of values of
     type [A] using the type [A -> Prop].
   *)

  Fixpoint bst (tr : tree nat) (s : nat -> Prop) :=
    match tr with
    | Leaf => forall x, ~ (s x) (* s is empty set *)
    | Node l d r =>
      s d /\
      bst l (fun x => s x /\ x < d) /\
      bst r (fun x => s x /\ d < x)
    end.

  (* First, let's get familiar with this definition by proving
     that [bst tr s] implies that all elements of [tr] have
     property [s].  Recall that you may need to prove a stronger
     lemma than the one we show here. *)

  (* If you want to apply a lemma that binds terms that don't appear
     in the goal, Coq can't infer what those terms should be. You
     may need to give them explicitly when you apply the lemma.
     A potentially helpful tip: you can use the `apply` tactic like so:

                   apply <theorem name> with (<x>:=<term>)

     where <x> is a forall-bound name in theorem statement you're
     trying to apply and <term> is what you what to fill in for <x>.
   *)
  
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  (* Hint: *)
  Lemma tree_forall_implies:
    forall tr (P Q: nat -> Prop),
      tree_forall P tr ->
      (forall x, P x -> Q x) ->
      tree_forall Q tr.
  Proof.
    induct tr; simplify.
    - propositional.

    - propositional.
      + eapply (IHtr1 _ _ H1).
        eassumption.
      + first_order.
      + eapply (IHtr2 _ _ H3).
        first_order.
  Qed.
  (* END SOLUTION *)
=======
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* HINT 7 (see Pset3Sig.v) *)
  Lemma bst_implies:
    forall tr s, bst tr s -> tree_forall s tr.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Proof.
    induction tr; simplify.
    - trivial.
    - propositional.
      all: eapply tree_forall_implies; simplify.
      all: eauto.
      all: simplify; propositional.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Proof.
  Admitted.
     END HANDOUT *)
=======
  Proof.
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Next, let's prove that elements of the left subtree of a
     BST node are less than the node's data and that all
     elements of the right subtree are greater than it.  This
     should be a consequence of the lemma you proved for
     [bst_implies]; our solution does not use induction here. *)

  Lemma bst_node_ordered :
    forall l d r s,
      bst (Node l d r) s ->
      tree_forall (fun x => x < d) l /\ tree_forall (fun x => x > d) r.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Proof.
    simplify.
    propositional.
    - apply tree_forall_implies with (P := fun x => s x /\ x < d).
      apply bst_implies; trivial.
      propositional.
    - apply tree_forall_implies with (P := fun x => s x /\ x > d).
      apply bst_implies; trivial.
      propositional.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Proof.
  Admitted.
     END HANDOUT *)
=======
  Proof.
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Here is another convenient property: if two sets are the
     same, then a bst representing one also represents the
     other.  Hint: [rewrite] and related tactics can be used
     with logical equivalence, not just equality! *)

  Lemma bst_iff : forall tr P Q,
      bst tr P ->
      (forall x, P x <-> Q x) ->
      bst tr Q.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Proof.
    induct tr; simplify.
    { rewrite <-H0. apply H with (x:=x). }
    rewrite H0 in H.
    propositional.
    { apply IHtr1 with (P:=(fun x => P x /\ x < d)); propositional.
      { rewrite <-H0; trivial. }
      { rewrite H0; trivial. } }
    { apply IHtr2 with (P:=(fun x => P x /\ d < x)); propositional.
      { rewrite <-H0; trivial. }
      { rewrite H0; trivial. } }
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Proof.
  Admitted.
     END HANDOUT *)
=======
  Proof.
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Let's prove something about the way we can map over binary search
     trees while preserving the bst structure. In order to preserve, the
     ordered structure of the data in a BST, the function that is mapped over
     must be strictly monotonically increasing. This means that if "f" is a
     strictly monotone-increasing function, and x and y are naturals where
     x is less than y, then f x must also be less than f y.

     The resulting predicate of the mapped tree is then recharacterized as
     a property that holds for all and only the mapped values of the 
     original tree.
     *)

  Theorem bst_strict_monotone_increasing : forall tr P Q f g,
      bst tr P ->
      left_inverse g f ->
      (forall x y, x < y <-> f x < f y) ->
      (forall x, P x <-> Q (f x)) ->
      bst (tree_map f tr) Q.
  Proof.
<<<<<<< HEAD
    (* BEGIN SOLUTION *)
    induct tr; simplify.
    - propositional.
      apply (H (g x)).
      unfold left_inverse in H0.
      apply H2.
      replace x with ((f ∘ g) x) in H3.
      equality. rewrite H0. equality.
    - propositional.
      + apply H2. auto.
      + eapply IHtr1.
        * apply H.
        * eassumption.
        * apply H1.
        * propositional.
          apply H2. apply H6.
          rewrite <- H1. apply H7.
          apply H2. apply H6.
          apply H1. apply H7.
      + eapply IHtr2.
        * apply H5.
        * eassumption.
        * apply H1.
        * propositional.
          apply H2. apply H6.
          rewrite <- H1. apply H7.
          apply H2. apply H6.
          apply H1. apply H7.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
  END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Monotone functions can be characterized as monotone increasing or 
     monotone decreasing. In the case of a strictly monotonically decreasing
     function we have the property that for a function f, if x is less than y
     then f y is less than f x.

     Let's prove the result of mapping a strictly monotonically decreasing
     function over a binary search tree. This will be similar to the mapping
     a strictly monotone-increasing function over a tree, only now to preserve
     the ordered property the resulting tree must be mirrored.
     *)
  
  Theorem bst_strict_monotone_decreasing_mirror : forall tr P Q f g,
      bst tr P ->
      left_inverse g f ->
      (forall x y, x < y <-> f x > f y) ->
      (forall x, P x <-> Q (f x)) ->
      bst (mirror (tree_map f tr)) Q.
  Proof.
<<<<<<< HEAD
    (* BEGIN SOLUTION *)
    induct tr; simplify.
    - propositional.
      apply (H (g x)).
      unfold left_inverse in H0.
      apply H2.
      replace x with ((f ∘ g) x) in H3.
      equality. rewrite H0. equality.
    - propositional.
      + apply H2. auto.
      + eapply IHtr2. apply H5.
        eassumption. auto.
        propositional.
        * apply H2. apply H6.
        * apply H1 in H7. linear_arithmetic.
        * apply H2. apply H6.
        * apply H1. linear_arithmetic.
      + eapply IHtr1. apply H.
        eassumption. auto.
        propositional.
        * apply H2. apply H6.
        * apply H1 in H7. linear_arithmetic.
        * apply H2. apply H6.
        * apply H1. linear_arithmetic.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
  END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a
  
  (* [member] computes whether [a] is in [tr], but to do so it *relies* on the
     [bst] property -- if [tr] is not a valid binary search tree, [member]
     will (and should, for performance) give arbitrarily incorrect answers. *)

  Fixpoint bst_member (a: nat) (tr: tree nat) : bool :=
    match tr with
    | Leaf => false
    | Node lt v rt =>
      match compare a v with
      | Lt => bst_member a lt
      | Eq => true
      | Gt => bst_member a rt
      end
    end.

  Lemma member_bst : forall tr s a,
      bst tr s -> bst_member a tr = true <-> s a.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Proof.
    induct tr; simplify.
    - specialize (H a). equality.
    - cases (compare a d); first_order; equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Proof.
  Admitted.
     END HANDOUT *)
=======
  Proof.
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Next week, we will look at insertion and deletion in
     BSTs. *)

  (** ****** Optional exercises ****** *)

  (* Everything below this line is optional! *)

  (* You've reached the end of the problem set. Congrats!
   *
   * [fold] is a higher-order function that is even more general
   * than [map]. In essence, [fold f z] takes as input a list
   * and produces a term where the [cons] constructor is
   * replaced by [f] and the [nil] constructor is replaced
   * by [z].
   *
   * [fold] is a "right" fold, which associates the bitwise operation
   * the opposite way as the [fold_left] function from Coq's
   * standard library.
   *)
  Fixpoint fold {A B : Type} (b_cons : A -> B -> B) (b_nil : B)
           (xs : list A) : B :=
    match xs with
    | nil => b_nil
    | cons x xs' => b_cons x (fold b_cons b_nil xs')
    end.

  (* For instance, we have
         fold plus 10 [1; 2; 3]
       = 1 + (2 + (3 + 10))
       = 16
   *)
  Example fold_example : fold plus 10 [1; 2; 3] = 16.
  Proof.
    simplify.
    equality.
  Qed.

  (* Prove that [map] can actually be defined as a particular
   * sort of [fold].
   *)
  Lemma map_is_fold : forall {A B : Type} (f : A -> B) (xs : list A),
      map f xs = fold (fun x ys => cons (f x) ys) nil xs.
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    induct xs.
    - simplify.
      equality.
    - simplify.
      rewrite IHxs.
      equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Since [fold f z] replaces [cons] with [f] and [nil] with
   * [z], [fold cons nil] should be the identity function.
   *)
  Theorem fold_id : forall {A : Type} (xs : list A),
      fold cons nil xs = xs.
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    induct xs.
    - simplify.
      equality.
    - simplify.
      rewrite IHxs.
      equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* If we apply [fold] to the concatenation of two lists,
   * it is the same as folding the "right" list and using
   * that as the starting point for folding the "left" list.
   *)
  Theorem fold_append : forall {A : Type} (f : A -> A -> A) (z : A)
                               (xs ys : list A),
      fold f z (xs ++ ys) = fold f (fold f z ys) xs.
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    induct xs.
    - simplify.
      equality.
    - simplify.
      rewrite IHxs.
      equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Using [fold], define a function that computes the
   * sum of a list of natural numbers.
   *)
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Definition sum : list nat -> nat := fold plus 0.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Definition sum : list nat -> nat. Admitted.
     END HANDOUT *)

  Example sum_example : sum [1; 2; 3] = 6.
  Proof.
    (* BEGIN SOLUTION *)
    (* Simplify doesn't unfold far enough for this to actually simplify! *)
    simplify.
    equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)
=======
  Definition sum : list nat -> nat. Admitted.

  Example sum_example : sum [1; 2; 3] = 6.
  Proof.
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Using [fold], define a function that computes the
   * conjunction of a list of Booleans (where the 0-ary
   * conjunction is defined as [true]).
   *)
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Definition all : list bool -> bool := fold andb true.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Definition all : list bool -> bool. Admitted.
     END HANDOUT *)

  Example all_example : all [true; false; true] = false.
  Proof.
  (* BEGIN SOLUTION *)
    (* Same issue here. *)
    simplify.
    equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)

  (* BEGIN SOLUTION *)
  (* Note: helper lemma *)
  Lemma sum_cons : forall (x : nat) (xs : list nat),
      sum (x :: xs) = x + sum xs.
  Proof.
    simplify.
    equality.
  Qed.
  (* END SOLUTION *)
=======
  Definition all : list bool -> bool. Admitted.

  Example all_example : all [true; false; true] = false.
  Proof.
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* The following two theorems, [sum_append] and [all_append],
   * say that the sum of the concatenation of two lists
   * is the same as summing each of the lists first and then
   * adding the result.
   *)
  Theorem sum_append : forall (xs ys : list nat),
      sum (xs ++ ys) = sum xs + sum ys.
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    simplify.
    induction xs.
    - simplify.
      equality.
    - simplify.
      rewrite !sum_cons.
      rewrite IHxs.
      linear_arithmetic.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)

  (* BEGIN SOLUTION *)
  (* Note: helper lemma *)
  Lemma all_cons : forall (x : bool) (xs : list bool),
      all (x :: xs) = x && all xs.
  Proof.
    simplify.
    equality.
  Qed.
  (* END SOLUTION *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  Theorem all_append : forall (xs ys : list bool),
      all (xs ++ ys) = andb (all xs) (all ys).
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    simplify.
    induction xs.
    - simplify.
      equality.
    - simplify.
      rewrite !all_cons.
      rewrite IHxs.
      apply andb_assoc.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Using [fold], define a function that composes a list of functions,
   * applying the *last* function in the list *first*.
   *)
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
  Definition compose_list {A : Type} : list (A -> A) -> A -> A :=
    fold compose id.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Definition compose_list {A : Type} : list (A -> A) -> A -> A. Admitted.
     END HANDOUT *)
=======
  Definition compose_list {A : Type} : list (A -> A) -> A -> A. Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  Example compose_list_example :
    compose_list [fun x => x + 1; fun x => x * 2; fun x => x + 2] 1 = 7.
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    (* Same issue with [simplify] here. *)
    simplify.
    equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)

  (* BEGIN SOLUTION *)
  (* Note: helper lemma *)
  Lemma compose_list_cons {A} (f : A -> A) fs x :
    compose_list (f :: fs) x = f (compose_list fs x).
  Proof.
    unfold compose_list.
    unfold compose.
    simplify.
    equality.
  Qed.
  (* END SOLUTION *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a

  (* Show that [sum xs] is the same as converting each number
   * in the list [xs] to a function that adds that number,
   * composing all of those functions together, and finally
   * applying that large composed function to [0].
   * Note that function [plus], when applied to just one number as an
   * argument, returns a function over another number, which
   * adds the original argument to it!
   *)
  Theorem compose_list_map_add_sum : forall (xs : list nat),
      compose_list (map plus xs) 0 = sum xs.
  Proof.
<<<<<<< HEAD
  (* BEGIN SOLUTION *)
    induct xs.
    - simplify.
      equality.
    - simplify.
      rewrite sum_cons.
      rewrite compose_list_cons.
      rewrite IHxs.
      equality.
  Qed.
  (* END SOLUTION *)
  (* BEGIN HANDOUT
  Admitted.
     END HANDOUT *)
=======
  Admitted.
>>>>>>> 3e863c7d5056ac92704c2b94ee39e21abc6b805a
End Impl.

Module ImplCorrect : Pset3Sig.S := Impl.

(* Authors:
 * Ben Sherman
 * Adam Chlipala
 * Samuel Gruetter
 * Clément Pit-Claudel
 * Amanda Liu
 *)
