Notation "'sigma' x .. y , p" := 
  (sigT (fun x => .. (sigT (fun y => p)) ..)) 
  (at level 200, x binder, y binder, right associativity) : type_scope.

Notation "A & B" := (prod A B) (at level 100, right associativity) : type_scope.

Definition Prod_Pr1 (A B : Type) (p : A * B) : A := match p with pair x y => x end.
Definition Prod_Pr2 (A B : Type) (p : A * B) : B := match p with pair x y => y end.

Definition Correspondence A B := 
  (A -> B) & (B -> A).

Notation "A <--> B" := (Correspondence A B) (at level 101, right associativity): type_scope.

Definition Decidable P :=
  ((P) + (P -> Empty_set))%type.

Notation "A == B" := (identity A B) (at level 100, no associativity).

Notation "'not' A" := (A -> Empty_set) (at level 100, no associativity).


Definition DeMorganConj (P Q : Type) (p : Decidable P) (q : Decidable Q)
  (f : not (P & Q)) : (not P) + (not Q) :=
match p with
| inl _ x =>
  match q with
  | inl _ y => inl (not Q) (fun z : P => f (x, y))
  | inr _ y => inr _ y
  end
| inr _ x =>
  match q with
  | inl _ y => inl _ x
  | inr _ y => inl _ x
  end
end.

Definition DeMorganDisj (P Q : Type) (p : Decidable P) (q : Decidable Q)
  (f : (not P) + (not Q)) : not (P & Q) :=
match p with
| inl _ x =>
  match q with
  | inl _ y => 
      match f with
      | inl _ z => (fun w => z x)
      | inr _ z => (fun w => z y)
      end
  | inr _ y => fun w => y (snd w)
  end
| inr _ x =>
  match q with
  | inl _ y => fun w => x (fst w)
  | inr _ y => fun w => x (fst w)
  end
end.

Lemma DeMorgan (P Q : Type) (p : Decidable P) (q : Decidable Q):
  ((not P) + (not Q)) <--> not (P & Q).
split. apply DeMorganDisj; assumption. apply DeMorganConj; assumption.
Defined.


Record IsEquivalence {A : Type} (eq: A -> A -> Type) := {
  Equivalence_Reflexivity: forall a : A, eq a a;
  Equivalence_Symmetry: forall a b : A, eq a b -> eq b a;
  Equivalence_Transitivity: forall a b c : A, eq a b -> eq b c -> eq a c;
}.

Definition IdentityIsEquivalence {A: Type}: IsEquivalence (@identity A).
apply Build_IsEquivalence; intuition.
rewrite H; assumption.
Defined.


Lemma NatSucc :
  forall a b: nat, a == b <--> S a == S b.
intros. split.
- intros. rewrite H. reflexivity.
- intros. injection H. intuition.
Defined.

Lemma NatIdentityDecidable :
  forall a b: nat, Decidable (a == b).
unfold Decidable.
induction a.
intros.
induction b.
  left. reflexivity.
  right. discriminate.
induction b.
- right. discriminate.
- destruct (IHa b).
  + left. rewrite i. reflexivity.
  + right. intros. apply e. apply NatSucc. assumption.
Defined.

Inductive LessThanOrEqual : nat -> nat -> Type :=
| LessThanOrEqualRefl : forall n, LessThanOrEqual n n
| LessThanOrEqualSucc : forall n m, LessThanOrEqual n m -> LessThanOrEqual n (S m).


Definition IsLeast (n : nat) : Type := forall m : nat, LessThanOrEqual n m.

Lemma ZeroIsUnique:
  forall n : nat, IsLeast n -> n == 0.
unfold IsLeast.
intros.
specialize (H 0).
inversion H.
reflexivity.
Defined.

Lemma ZeroIsLeast : IsLeast 0.
unfold IsLeast.
induction m.
- apply LessThanOrEqualRefl.
- apply LessThanOrEqualSucc. assumption.
Defined.

Lemma ZeroIsTheLeast:
  forall n : nat, LessThanOrEqual 0 n & (LessThanOrEqual n 0 -> n == 0).
intros. split.
- apply ZeroIsLeast.
- intros. induction n. reflexivity. inversion H.
Defined.


Lemma LessThanOrEqualS1 :
  forall n m: nat, LessThanOrEqual n m -> LessThanOrEqual (S n) (S m).
intros. induction n.
  + induction m.
    * apply LessThanOrEqualRefl.
    * apply LessThanOrEqualSucc. apply IHm. inversion H. assumption.
  + induction m.
    * apply ZeroIsTheLeast in H. discriminate H.
    * inversion H. apply LessThanOrEqualRefl.
      apply LessThanOrEqualSucc. apply IHm. assumption.
      intros. assumption.
Defined.

Lemma LessThanOrEqualS2 :
  forall n m: nat, LessThanOrEqual (S n) (S m) -> LessThanOrEqual n m.
induction n.
+ induction m.
  * intros. apply LessThanOrEqualRefl.
  * intros. apply ZeroIsTheLeast.
+ induction m.
  * intros. inversion H. apply ZeroIsTheLeast in H2. discriminate H2.
  * intros.
    inversion H. apply LessThanOrEqualRefl.
    apply LessThanOrEqualSucc. apply IHm. assumption.
Defined.

Lemma LessThanOrEqualPreservedBySucc:
  forall n m: nat, LessThanOrEqual n m <--> LessThanOrEqual (S n) (S m).
intros. split. apply LessThanOrEqualS1. apply LessThanOrEqualS2. Defined.

Lemma LessThanOrEqualSubstract:
  forall n m: nat, LessThanOrEqual (S n) m -> LessThanOrEqual n m.
induction n.
- induction m.
  + intros. apply LessThanOrEqualRefl.
  + intros. apply ZeroIsTheLeast.
- induction m.
  + intros. apply ZeroIsTheLeast in H. discriminate H.
  + intros. apply (LessThanOrEqualPreservedBySucc n m). apply IHn.
    apply LessThanOrEqualPreservedBySucc. assumption.
Defined.


Lemma LessThanOrEqualDecidable :
  forall n m : nat, Decidable (LessThanOrEqual n m).
unfold Decidable.
induction n.
- intros. left. apply ZeroIsTheLeast.
- induction m.
  + right. intros. apply ZeroIsTheLeast in H. discriminate H.
  + destruct (IHn m).
    * left. apply LessThanOrEqualPreservedBySucc in l. assumption.
    * right. intros. apply e. apply LessThanOrEqualPreservedBySucc. assumption.
Defined.

Lemma PositiveIsNotLessThanOrEqualToZero:
  forall n: nat, LessThanOrEqual (S n) 0 -> Empty_set.
intros. apply ZeroIsTheLeast in H. discriminate.
Defined.


Lemma LessThanOrEqualAntisymmetry:
  forall n m: nat,
  LessThanOrEqual n m ->
  LessThanOrEqual m n -> n == m.
induction n.
- induction m.
  + intuition.
  + intros. apply ZeroIsTheLeast in H0. discriminate H0.
- induction m.
  + intros. apply ZeroIsTheLeast in H. discriminate H.
  + intros.
    apply (NatSucc n m).
    apply IHn.
    * apply LessThanOrEqualPreservedBySucc. assumption.
    * apply LessThanOrEqualPreservedBySucc. assumption.
Defined.


Lemma LessThanOrEqualLinear:
  forall n m: nat, (LessThanOrEqual n m) + (LessThanOrEqual m n).
induction n.
- induction m.
  + left. apply LessThanOrEqualRefl.
  + left. apply ZeroIsTheLeast.
- induction m.
  + right. apply ZeroIsTheLeast.
  + destruct (IHn m).
    * left. apply (LessThanOrEqualPreservedBySucc n m). assumption.
    * right. apply (LessThanOrEqualPreservedBySucc m n). assumption.
Defined.

Lemma LessThanOrEqualTransitive:
  forall n m u, 
    LessThanOrEqual n m -> LessThanOrEqual m u -> LessThanOrEqual n u.
induction n.
- induction m.
  + induction u.
    * trivial.
    * intros. apply ZeroIsTheLeast.
  + intros. apply ZeroIsTheLeast.
- induction m.
  + induction u.
    * intros. apply ZeroIsTheLeast in H. discriminate H.
    * intros. apply ZeroIsTheLeast in H. discriminate H.
  + induction u.
    * intros. apply ZeroIsTheLeast in H0. discriminate H0.
    * intros.
      apply (LessThanOrEqualPreservedBySucc n u).
      apply (IHn m u).
      apply (LessThanOrEqualPreservedBySucc n m). assumption.
      apply (LessThanOrEqualPreservedBySucc m u). assumption.
Defined.

Definition LessThan (a b : nat) := LessThanOrEqual (S a) b.

Lemma LessThanIrreflexive:
  forall n : nat, LessThanOrEqual (S n) n -> Empty_set.
induction n.
- intros. apply ZeroIsTheLeast in H. discriminate H.
- intros. apply IHn. apply LessThanOrEqualPreservedBySucc. assumption.
Defined.


Lemma LessThanOrEqualStrictlySmaller:
  forall n m, LessThanOrEqual n m -> ((n == m) -> Empty_set) -> LessThanOrEqual (S n) m.
intros.
inversion H. destruct H0. rewrite H2. reflexivity.
apply (LessThanOrEqualPreservedBySucc n m0). assumption.
Defined.

Lemma LessThanOrEqualInvert:
  forall n m: nat,
  (LessThanOrEqual n m -> Empty_set) -> (LessThanOrEqual m n & ((n == m) -> Empty_set)).
intros.
split.
- destruct (LessThanOrEqualLinear n m). contradiction. assumption.
- intros. apply H. rewrite H0. apply LessThanOrEqualRefl.
Defined.

Lemma DeconstructLessThanOrEqual:
  forall n m : nat,
  LessThanOrEqual n m <--> (LessThan n m) + (n == m).
intros. split.
- intros. unfold LessThan.
  destruct (NatIdentityDecidable n m).
  + right. assumption.
  + left. apply LessThanOrEqualStrictlySmaller; assumption.
- intros. unfold LessThan in H. destruct H.
  + apply LessThanOrEqualSubstract. assumption.
  + rewrite i. apply LessThanOrEqualRefl.
Defined.


Lemma LessThanInvert:
  forall n m, (not (LessThan n m)) -> LessThanOrEqual m n.
unfold LessThan.
intros.
apply LessThanOrEqualInvert in H.
destruct H.
inversion l.
- rewrite H0 in e. contradiction.
- assumption.
Defined.


Lemma LessThanZeroFalse:
  forall n, not (LessThan n 0).
intros. unfold LessThan in H. apply ZeroIsTheLeast in H. discriminate H.
Defined. 

Lemma LessThanDecidable:
  forall n m, Decidable (LessThan n m).
unfold LessThan. intros. apply LessThanOrEqualDecidable.
Defined.






