
Record IsEquivalence {A : Type} (eq: A -> A -> Prop) := {
  Equivalence_Reflexivity: forall a : A, eq a a;
  Equivalence_Symmetry: forall a b : A, eq a b -> eq b a;
  Equivalence_Transitivity: forall a b c : A, eq a b -> eq b c -> eq a c;
}.


Definition PropositionalEqualityIsEquivalence {A: Type}: IsEquivalence (@eq A).
apply Build_IsEquivalence; intuition.
rewrite H; assumption.
Defined.


Record Setoid := {
  Setoid_Type : Type;
  Setoid_Equivalence : Setoid_Type -> Setoid_Type -> Prop;
  Setoid_IsEquivalence: IsEquivalence Setoid_Equivalence;
}.

Notation "a ==[ A ] b" := (Setoid_Equivalence A a b) (at level 70, no associativity).
Notation "| A |" := (Setoid_Type A) (at level 70, no associativity).

Ltac setoid_refl A := apply (Equivalence_Reflexivity (Setoid_Equivalence A) (Setoid_IsEquivalence A)).
Ltac setoid_symm A := apply (Equivalence_Symmetry (Setoid_Equivalence A) (Setoid_IsEquivalence A)).
Ltac setoid_tran A e := apply (Equivalence_Transitivity (Setoid_Equivalence A) (Setoid_IsEquivalence A)) with (b := e).

Definition PropSetoidOf (A : Type): Setoid.
apply (Build_Setoid A (@eq A) PropositionalEqualityIsEquivalence).
Defined.


Record Function (A : Setoid) (B : Setoid) := {
  Function_Map : |A| -> |B|;
  Function_MapIsExtensional: forall a b : |A|, A.(Setoid_Equivalence) a b -> B.(Setoid_Equivalence) (Function_Map a) (Function_Map b);
}.


Definition FunctionApp {A B : Setoid} (f : Function A B) (x : |A| ) : |B| :=
  (Function_Map A B f) x.

Notation "f ` a" := (FunctionApp f a) (at level 69, left associativity).


Definition FunctionEquivalence {A B : Setoid} (f g : Function A B) : Prop :=
  forall a : A.(Setoid_Type), f`a ==[B] g`a.

Lemma Function_eqv_is_equivalence {A B : Setoid}: IsEquivalence (@FunctionEquivalence A B).
apply Build_IsEquivalence.
- intros. unfold FunctionEquivalence. intros.
  apply (Equivalence_Reflexivity (Setoid_Equivalence B) (Setoid_IsEquivalence B)).
- unfold FunctionEquivalence. intros.
  apply (Equivalence_Symmetry (Setoid_Equivalence B) (Setoid_IsEquivalence B)). apply H.
- unfold FunctionEquivalence. intros. specialize (H a0). specialize (H0 a0).
  apply (Equivalence_Transitivity (Setoid_Equivalence B) (Setoid_IsEquivalence B)) with (b := b ` a0).
  assumption. assumption.
Defined.


Definition FunctionSetoid (A: Setoid) (B : Setoid) : Setoid := {|
  Setoid_Type := Function A B;
  Setoid_Equivalence := FunctionEquivalence;
  Setoid_IsEquivalence := Function_eqv_is_equivalence
|}.

Notation "A ==> B" := (Function A B) (at level 68, right associativity).
Notation "B ^^ A" := (FunctionSetoid A B) (at level 67, no associativity).


Record Prod (A : Type) (B : Type) := {
  fst : A;
  snd : B;
}.



Definition ProdSetoid (A B : Setoid) : Setoid.
apply (Build_Setoid
        (Prod (|A|) (|B|))
        (fun a b => fst (|A|) (|B|) a ==[A] fst (|A|) (|B|) b /\ 
                    snd (|A|) (|B|) a ==[B] snd (|A|) (|B|) b)).
apply Build_IsEquivalence.
- intros. split. setoid_refl A. setoid_refl B.
- intros. split. setoid_symm A. intuition. setoid_symm B. intuition. 
- intros. split. setoid_tran A (fst (| A |) (| B |) b). intuition. intuition.
                 setoid_tran B (snd (| A |) (| B |) b). intuition. intuition.
Defined.


Inductive Sum (A : Type) (B : Type) :=
| inl : A -> Sum A B
| inr : B -> Sum A B.

(*
Inductive Sum_equivalence {A B : Setoid}: Sum (|A|) (|B|) -> Sum (|A|) (|B|) -> Prop :=
| inl_eq: forall a b : |A|, a ==[A] b -> Sum_equivalence (inl _ _ a) (inl _ _ b)
| inr_eq: forall a b : |B|, a ==[B] b -> Sum_equivalence (inr _ _ a) (inr _ _ b).

Definition SumSetoid (A B : Setoid) : Setoid.
apply (Build_Setoid (Sum (|A|) (|B|)) (Sum_equivalence)).
apply (Build_Equivalence).
- intros. destruct a.
  + apply inl_eq. setoid_refl A.
  + apply inr_eq. setoid_refl B.
- intros. destruct a. destruct b.
  apply inl_eq. inversion H. setoid_symm A. assumption.
  inversion H.
  destruct b.
  inversion H.
  apply inr_eq. inversion H. setoid_symm B. assumption.
- intros. destruct a. destruct b. destruct c.
  apply inl_eq. inversion H. inversion H0. setoid_tran A u0; assumption.
  inversion H0.
  destruct c. inversion H0. inversion H.
  destruct b. destruct c. inversion H. inversion H.
  destruct c. inversion H0.
  apply inr_eq. inversion H. inversion H0. setoid_tran B u0; assumption.
Defined.
*)

Definition SumSetoid (A B : Setoid) : Setoid.
apply (Build_Setoid
  (Sum (|A|) (|B|))
  (fun a b =>
    match a with
    | inl _ _ x =>
      match b with
      | inl _ _ y => x ==[A] y
      | inr _ _ y => False
      end
    | inr _ _ x =>
      match b with
      | inl _ _ y => False
      | inr _ _ y => x ==[B] y
      end
    end)).
apply Build_IsEquivalence.
- intros. destruct a. setoid_refl A. setoid_refl B.
- intros. destruct a. destruct b. setoid_symm A. assumption. assumption.
  destruct b. assumption. setoid_symm B. assumption.
- intros.
  destruct a. destruct b. destruct c. setoid_tran A s0. assumption. assumption. assumption.
  destruct c. contradiction. contradiction.
  destruct b. destruct c. contradiction. contradiction.
  destruct c. contradiction. setoid_tran B s0. assumption. assumption.
Defined.



Record Property (A : Setoid) := {
  Property_Prop : |A| -> Prop;
  Property_PropIsExtensional: 
    forall a b: |A|, a ==[A] b -> Property_Prop a -> Property_Prop b
}.

Record Relation (A B : Setoid) := {
  Relation_Rel : |A| -> |B| -> Prop;
  Relation_RelIsExtensional:
    forall a b : |A|, forall c d : |B|,
      a ==[A] b -> c ==[B] d ->
      Relation_Rel a c -> Relation_Rel b d
}.


Definition IsInjection {A B : Setoid} (f : A ==> B) : Prop :=
  forall a b : |A|, f` a ==[B] f` b -> a ==[A] b.

Definition IsSurjection {A B : Setoid} (f : A ==> B) : Prop :=
  forall b: |B|, exists a: |A|, f ` a ==[B] b.

Definition IsBijection {A B : Setoid} (f : A ==> B) : Prop :=
  IsInjection f /\ IsSurjection f.

Definition id {A : Setoid} : A ==> A.
  apply (Build_Function A A (fun x => x)).
  auto.
Defined.

Definition const {A B : Setoid} (x : |B|) : A ==> B.
  apply (Build_Function A B (fun y => x)).
  intros. setoid_refl B.
Defined.

Definition compose {A B C: Setoid} (g : B ==> C) (f : A ==> B): A ==> C.
  apply (Build_Function A C (fun a : |A| => g ` (f ` a))).
  intros.
  apply Function_MapIsExtensional.
  apply Function_MapIsExtensional.
  assumption.
Defined.

Notation "f |> g" := (compose g f) (at level 65, left associativity).

Definition IsMono {A B : Setoid} (f : A ==> B) : Prop :=
  forall C : Setoid, forall g h: C ==> A, g |> f  ==[B^^C] h |> f -> g ==[A^^C] h.

Definition IsEpi {A B : Setoid} (f : A ==> B) : Prop :=
  forall C : Setoid, forall g h: B ==> C, f |> g ==[C^^A] f |> h -> g ==[C^^B] h.

Definition IsIso {A B : Setoid} (f : A ==> B) : Prop :=
  exists g : B ==> A, f |> g ==[A^^A] id /\ g |> f ==[B^^B] id.

Inductive Unit: Type := Star.

Definition UnitSetoid : Setoid.
  apply (Build_Setoid Unit (fun _ _ => True)).
  apply Build_IsEquivalence; auto.
Defined.

Definition Unit_function {A : Setoid} : A ==> UnitSetoid.
apply (Build_Function A UnitSetoid (fun x => Star)). intros. setoid_refl UnitSetoid.
Defined.

Lemma Unit_function_is_unique:
  forall B : Setoid,
    forall g: B ==> UnitSetoid, Unit_function ==[UnitSetoid^^B] g.
intros. simpl. unfold FunctionEquivalence.
intros. simpl. trivial.
Defined.



Lemma MonoInjective {A B : Setoid}:
  forall f : A ==> B,
  IsMono f <-> IsInjection f.
intros. split.
- unfold IsMono. unfold IsInjection.
  intros. specialize (H UnitSetoid (const a) (const b)).
  simpl in H. unfold FunctionEquivalence in H. simpl in H.
  intuition.
- unfold IsMono. unfold IsInjection.
  intros. simpl. unfold FunctionEquivalence; simpl. intros.
  specialize (H (g ` a) (h ` a)).
  simpl in H0.  unfold FunctionEquivalence in H0; simpl.
  specialize (H0 a). intuition.
Qed.


Definition HasRightInverse {A B : Setoid} (f : A ==> B) : Prop :=
  exists g : B ==> A, g |> f ==[B^^B] id.

Lemma HasRightInverseIsSurjection {A B : Setoid}: 
  forall f : A ==> B,
  HasRightInverse f -> IsSurjection f.
intros. 
 unfold HasRightInverse. unfold IsSurjection.
  intros. destruct H as [g].
  simpl in H. unfold FunctionEquivalence in H.
  exists (g ` b). apply H.
Qed.

Definition IsChoiceSetoid (S : Setoid) : Prop :=
  forall X : Setoid, forall f : X ==> S,
    IsSurjection f -> HasRightInverse f.



Record Subset (A: Setoid) := {
  Subset_Setoid: Setoid ;
  Subset_Injection: Subset_Setoid ==> A;
  Subset_InjectionIsInjection: IsInjection Subset_Injection
}.



Definition IsMemberOfSubset {A : Setoid} (a : |A|) (S: Subset A) : Prop :=
  exists x : |Subset_Setoid _ S|, ((Subset_Injection _ S)` x) ==[A] a.

Notation "a ::[ A ] S" := (@IsMemberOfSubset A a S) (at level 66, no associativity).

Definition IsSubsetOf {A : Setoid} (X Y : Subset A) : Prop :=
  forall a : |A|, a ::[A] X -> a ::[A] Y.

Definition IsSubsetEquiv {A : Setoid} (X Y : Subset A): Prop :=
  IsSubsetOf X Y /\ IsSubsetOf Y X.


Record Sigma (A : Type) (P : A -> Type) := {
  pr1 : A;
  pr2 : P pr1;
}.

Definition SigmaSetoid (X : Setoid) (P : Property X) : Setoid.
  apply (Build_Setoid (Sigma (|X|) (P.(Property_Prop X)))
        (fun a b =>
          pr1 _ _ a ==[X] pr1 _ _ b
        )).
  apply Build_IsEquivalence; intros.
  - setoid_refl X.
  - setoid_symm X. assumption.
  - setoid_tran X (pr1 (| X |) P.(Property_Prop X) b) ; assumption.
Defined.

Definition SigmaSetoid_pr1 {X : Setoid} {P : Property X}: SigmaSetoid X P ==> X.
  apply (Build_Function (SigmaSetoid X P) X (pr1 _ _)).
  intros. simpl in H. assumption.
Defined.


Definition SubsetComprehension (A : Setoid) (P : Property A) : Subset A.
  apply (Build_Subset A (SigmaSetoid A P) SigmaSetoid_pr1).
  unfold IsInjection. intros.
  simpl in H.
  simpl.
  assumption.
Defined.


Lemma BetaSubsetMembership {A : Setoid} {P : Property A}:
  forall a : |A|,
  (a ::[A] (SubsetComprehension A P)) <-> P.(Property_Prop _) a.
intros. split.
- intros. unfold IsMemberOfSubset in H. simpl in H.
  destruct H.
  assert  ((Property_Prop A P) (pr1 (| A |) (Property_Prop A P) x)).
  apply pr2.
  apply (Property_PropIsExtensional A P (pr1 (| A |) (Property_Prop A P) x) a).
  assumption.
  assumption.
- intros. unfold IsMemberOfSubset.
  simpl.
  exists {| pr1 := a; pr2 := H |}.
  simpl. setoid_refl A.
Qed.


Lemma ExtPropConj {A: Setoid} (P Q : Property A): Property A.
  apply (Build_Property A (fun x => Property_Prop A P x /\ Property_Prop A Q x)).
  intros. destruct H0. split.
  apply (Property_PropIsExtensional A P a); assumption.
  apply (Property_PropIsExtensional A Q a); assumption.
Defined.

Lemma ExtPropDisj {A: Setoid} (P Q : Property A): Property A.
  apply (Build_Property A (fun x => Property_Prop A P x \/ Property_Prop A Q x)).
  intros. destruct H0.
  - left. apply (Property_PropIsExtensional A P a); assumption.
  - right. apply (Property_PropIsExtensional A Q a); assumption.
Defined.


Definition PropertyOnProdToRelation {A B : Setoid} (P : Property (ProdSetoid A B)) : Relation A B.
apply (Build_Relation A B (fun a b => Property_Prop _ P {| fst := a; snd := b |})).
intros.
apply (Property_PropIsExtensional (ProdSetoid A B) P {| fst := a; snd := c |}).
simpl. intuition. assumption.
Defined.

Lemma PR {A B : Setoid}:
  forall P : Property (ProdSetoid A B), exists R : Relation A B,
  forall a b,
  Property_Prop _ P {| fst := a; snd := b |}  <-> Relation_Rel _ _ R a b.
intros.
exists (PropertyOnProdToRelation P).
intros.
simpl. intuition.
Qed.

Definition RelationToPropertyProd {A B : Setoid} (R: Relation A B): Property (ProdSetoid A B).
apply (Build_Property (ProdSetoid A B)
    (fun a => Relation_Rel A B R (fst (|A|) (|B|) a) (snd (|A|) (|B|) a))).
intros.
simpl in H.
destruct H.
apply (Relation_RelIsExtensional A B R 
  (fst (| A |) (| B |) a) 
  (fst (| A |) (| B |) b)
  (snd (| A |) (| B |) a)
  (snd (| A |) (| B |) b)
); assumption.
Defined.

Lemma PR2 {A B : Setoid}:
  forall R : Relation A B, exists P : Property (ProdSetoid A B),
  forall a b,
  Property_Prop _ P {| fst := a; snd := b |}  <-> Relation_Rel _ _ R a b.
intros.
exists (RelationToPropertyProd R).
intros. simpl. intuition.
Qed.



Definition IsEquivalenceRelation {A: Setoid} (R : Relation A A) := 
  IsEquivalence (R.(Relation_Rel A A)).


Definition QuotientSetoid (A : Setoid) (R : Relation A A) (p : IsEquivalenceRelation R): Setoid :=
  {| Setoid_Type := | A |; Setoid_Equivalence := Relation_Rel A A R; Setoid_IsEquivalence := p |}.


Definition quotient (A : Setoid) (R: Relation A A) (p :IsEquivalenceRelation R) : 
  A ==> QuotientSetoid A R p.
apply (Build_Function A (QuotientSetoid A R p) (fun x => x)).
intros.
simpl. destruct p as [refl].
apply (Relation_RelIsExtensional A A R a a a b).
setoid_refl A. assumption. apply refl.
Defined.


Lemma quotient_is_surjective {A: Setoid} {R: Relation A A} (p :IsEquivalenceRelation R): IsSurjection (quotient A R p).
unfold IsSurjection. intros. simpl.
exists b.
destruct p as [refl].
apply refl.
Qed.



Definition quotient_lift {A B: Setoid} {R: Relation A A} {p: IsEquivalenceRelation R}
  (f : A ==> B)
  (q: forall a b : |A|, R.(Relation_Rel A A) a b -> f`a ==[B] f`b):
  (QuotientSetoid A R p) ==> B.
apply (Build_Function (QuotientSetoid A R p) B (f.(Function_Map _ _))).
intros.
simpl in H.
apply q.
assumption.
Defined.


Lemma QuotientFactors {A B : Setoid} 
  (R: Relation A A) (p : IsEquivalenceRelation R) (f : A ==> B)
  (q : forall a b : |A|, R.(Relation_Rel A A) a b -> f`a ==[B] f`b):
  exists h : QuotientSetoid A R p ==> B,
  forall x : |A|,
  h ` (quotient A R p ` x) ==[B] f ` x.
exists (quotient_lift f q). simpl. intros.
setoid_refl B.
Qed.


Inductive NatOver : nat -> Type :=
| NatOverZ {n : nat}: NatOver (S n)
| NatOverS {n : nat}: NatOver n -> NatOver (S n).

Definition FinSetoid (n: nat) : Setoid.
apply (Build_Setoid (NatOver n) eq).
apply Build_IsEquivalence ; intuition. 
rewrite H. assumption.
Defined.


Definition IsSetoidFinite (S: Setoid): Prop :=
  exists n : nat, exists f : S ==> FinSetoid n,  IsBijection f.











