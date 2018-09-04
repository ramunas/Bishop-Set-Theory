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


Lemma ZeroIsTheLeast:
  forall n : nat, LessThanOrEqual 0 n & (LessThanOrEqual n 0 -> n == 0).
intros.
split.
induction n.
- apply LessThanOrEqualRefl.
- apply LessThanOrEqualSucc. assumption.
- intros. inversion H. reflexivity.
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


Lemma LessThanOrEqualDecidable :
  forall n m : nat, Decidable (LessThanOrEqual n m).
unfold Decidable.
induction n.
- induction m.
  + left. apply LessThanOrEqualRefl.
  + left. apply ZeroIsTheLeast.
- induction m.
  + right. intros. apply ZeroIsTheLeast in H. discriminate H.
  + destruct (IHn m).
    * left. apply LessThanOrEqualPreservedBySucc in l. assumption.
    * right. intros. apply e.  apply LessThanOrEqualPreservedBySucc. assumption.
Defined.


Definition LessThan (a b : nat) := LessThanOrEqual (S a) b.








