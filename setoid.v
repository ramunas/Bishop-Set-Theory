
Record Equivalence {A : Type} (eqv: A -> A -> Prop) := {
  refl: forall a : A, eqv a a;
  symm: forall a b : A, eqv a b -> eqv b a;
  tran: forall a b c : A, eqv a b -> eqv b c -> eqv a c;
}.


Definition PropositionalEqualityIsEquivalence {A: Type}: Equivalence (@eq A).
apply Build_Equivalence; intuition.
rewrite H; assumption.
Defined.


Record Setoid := {
  U : Type;
  eqv : U -> U -> Prop;
  eqv_is_equivalence: Equivalence eqv;
}.

Definition PropSetoidOf (A : Type): Setoid.
apply (Build_Setoid A (@eq A) PropositionalEqualityIsEquivalence).
Defined.


Notation "a ==[ A ] b" := (A.(eqv) a b) (at level 70, no associativity).
Notation "| A |" := (A.(U)) (at level 70, no associativity).


Record Function (A : Setoid) (B : Setoid) := {
  underlying_map : A.(U) -> B.(U);
  map_is_extensional: forall a b : A.(U), A.(eqv) a b -> B.(eqv) (underlying_map a) (underlying_map b);
}.


Definition app {A B : Setoid} (f : Function A B) (x : |A| ) : |B| :=
  (underlying_map A B f) x.

Notation "f ` a" := (app f a) (at level 69, left associativity).


Definition Function_eqv {A B : Setoid} (f g : Function A B) : Prop :=
  forall a : A.(U), f`a ==[B] g`a.

Lemma Function_eqv_is_equivalence {A B : Setoid}: Equivalence (@Function_eqv A B).
apply Build_Equivalence.
- intros. unfold Function_eqv. intros.
  apply (refl (eqv B) (eqv_is_equivalence B)).
- unfold Function_eqv. intros.
  apply (symm (eqv B) (eqv_is_equivalence B)). apply H.
- unfold Function_eqv. intros. specialize (H a0). specialize (H0 a0).
  apply (tran (eqv B) (eqv_is_equivalence B)) with (b := b ` a0).
  assumption. assumption.
Defined.


Definition FunctionSetoid (A: Setoid) (B : Setoid) : Setoid :=
{| U := Function A B; eqv := Function_eqv; eqv_is_equivalence := Function_eqv_is_equivalence |}.


Record Prod (A : Type) (B : Type) := {
  fst : A;
  snd : B;
}.



Ltac setoid_refl A := apply (refl (eqv A) (eqv_is_equivalence A)).
Ltac setoid_symm A := apply (symm (eqv A) (eqv_is_equivalence A)).
Ltac setoid_tran A e := apply (tran (eqv A) (eqv_is_equivalence A)) with (b := e).

Definition ProdSetoid (A B : Setoid) : Setoid.
apply (Build_Setoid
        (Prod (|A|) (|B|))
        (fun a b => fst (|A|) (|B|) a ==[A] fst (|A|) (|B|) b /\ 
                    snd (|A|) (|B|) a ==[B] snd (|A|) (|B|)b)).
apply Build_Equivalence.
- intros. split. setoid_refl A. setoid_refl B.
- intros. split. setoid_symm A. intuition. setoid_symm B. intuition. 
- intros. split. setoid_tran A (fst (| A |) (| B |) b). intuition. intuition.
                 setoid_tran B (snd (| A |) (| B |) b). intuition. intuition.
Defined.


Definition mkProd {A B : Setoid} (a : |A|) (b : |B|): |ProdSetoid A B| :=
  {| fst := a; snd := b |}.


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
apply Build_Equivalence.
- intros. destruct a. setoid_refl A. setoid_refl B.
- intros. destruct a. destruct b. setoid_symm A. assumption. assumption.
  destruct b. assumption. setoid_symm B. assumption.
- intros.
  destruct a. destruct b. destruct c. setoid_tran A u0. assumption. assumption. assumption.
  destruct c. contradiction. contradiction.
  destruct b. destruct c. contradiction. contradiction.
  destruct c. contradiction. setoid_tran B u0. assumption. assumption.
Defined.



Record Property (A : Setoid) := {
  underlying_prop : |A| -> Prop;
  property_is_extensional: 
    forall a b: |A|, a ==[A] b -> underlying_prop a -> underlying_prop b
}.

Record Relation (A B : Setoid) := {
  underlying_relation : |A| -> |B| -> Prop;
  relation_is_extensional:
    forall a b : |A|, forall c d : |B|,
      a ==[A] b -> c ==[B] d ->
      underlying_relation a c -> underlying_relation b d
}.


Notation "A ==> B" := (Function A B) (at level 68, right associativity).
Notation "B ^^ A" := (FunctionSetoid A B) (at level 67, no associativity).

Definition IsInjective {A B : Setoid} (f : A ==> B) : Prop :=
  forall a b : |A|, f` a ==[B] f` b -> a ==[A] b.

Definition IsSurjective {A B : Setoid} (f : A ==> B) : Prop :=
  forall b: |B|, exists a: |A|, f ` a ==[B] b.

Definition IsBijective {A B : Setoid} (f : A ==> B) : Prop :=
  IsInjective f /\ IsSurjective f.

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
  apply map_is_extensional.
  apply map_is_extensional.
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
  apply Build_Equivalence; auto.
Defined.

Definition Unit_function {A : Setoid} : A ==> UnitSetoid.
apply (Build_Function A UnitSetoid (fun x => Star)). intros. setoid_refl UnitSetoid.
Defined.

Lemma Unit_function_is_unique:
  forall B : Setoid,
    forall g: B ==> UnitSetoid, Unit_function ==[UnitSetoid^^B] g.
intros. simpl. unfold Function_eqv.
intros. simpl. trivial.
Defined.



Lemma MonoInjective {A B : Setoid}:
  forall f : A ==> B,
  IsMono f <-> IsInjective f.
intros. split.
- unfold IsMono. unfold IsInjective.
  intros. specialize (H UnitSetoid (const a) (const b)).
  simpl in H. unfold Function_eqv in H. simpl in H.
  intuition.
- unfold IsMono. unfold IsInjective.
  intros. simpl. unfold Function_eqv; simpl. intros.
  specialize (H (g ` a) (h ` a)).
  simpl in H0.  unfold Function_eqv in H0; simpl.
  specialize (H0 a). intuition.
Qed.


Definition HasRightInverse {A B : Setoid} (f : A ==> B) : Prop :=
  exists g : B ==> A, g |> f ==[B^^B] id.

Lemma HasRightInverseIsSurjection {A B : Setoid}: 
  forall f : A ==> B,
  HasRightInverse f -> IsSurjective f.
intros. 
 unfold HasRightInverse. unfold IsSurjective.
  intros. destruct H as [g].
  simpl in H. unfold Function_eqv in H.
  exists (g ` b). apply H.
Qed.

Definition IsChoiceSetoid (S : Setoid) : Prop :=
  forall X : Setoid, forall f : X ==> S,
    IsSurjective f -> HasRightInverse f.



Record Subset (A: Setoid) := {
  subset_setoid: Setoid ;
  subset_injection: subset_setoid ==> A;
  subset_injection_is_injective: IsInjective subset_injection
}.



Definition IsMemberOfSubset {A : Setoid} (a : |A|) (S: Subset A) : Prop :=
  exists x : |subset_setoid _ S|, ((subset_injection _ S)` x) ==[A] a.

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
  apply (Build_Setoid (Sigma (|X|) (P.(underlying_prop X)))
        (fun a b =>
          pr1 _ _ a ==[X] pr1 _ _ b
        )).
  apply Build_Equivalence; intros.
  - setoid_refl X.
  - setoid_symm X. assumption.
  - setoid_tran X (pr1 (| X |) P.(underlying_prop X) b) ; assumption.
Defined.

Definition SigmaSetoid_pr1 {X : Setoid} {P : Property X}: SigmaSetoid X P ==> X.
  apply (Build_Function (SigmaSetoid X P) X (pr1 _ _)).
  intros. simpl in H. assumption.
Defined.


Definition SubsetComprehension (A : Setoid) (P : Property A) : Subset A.
  apply (Build_Subset A (SigmaSetoid A P) SigmaSetoid_pr1).
  unfold IsInjective. intros.
  simpl in H.
  simpl.
  assumption.
Defined.


Lemma BetaSubsetMembership {A : Setoid} {P : Property A}:
  forall a : |A|,
  (a ::[A] (SubsetComprehension A P)) <-> P.(underlying_prop _) a.
intros. split.
- intros. unfold IsMemberOfSubset in H. simpl in H.
  destruct H.
  assert  ((underlying_prop A P) (pr1 (| A |) (underlying_prop A P) x)).
  apply pr2.
  apply (property_is_extensional A P (pr1 (| A |) (underlying_prop A P) x) a).
  assumption.
  assumption.
- intros. unfold IsMemberOfSubset.
  simpl.
  exists {| pr1 := a; pr2 := H |}.
  simpl. setoid_refl A.
Qed.


Lemma ExtPropConj {A: Setoid} (P Q : Property A): Property A.
  apply (Build_Property A (fun x => underlying_prop A P x /\ underlying_prop A Q x)).
  intros. destruct H0. split.
  apply (property_is_extensional A P a); assumption.
  apply (property_is_extensional A Q a); assumption.
Defined.

Lemma ExtPropDisj {A: Setoid} (P Q : Property A): Property A.
  apply (Build_Property A (fun x => underlying_prop A P x \/ underlying_prop A Q x)).
  intros. destruct H0.
  - left. apply (property_is_extensional A P a); assumption.
  - right. apply (property_is_extensional A Q a); assumption.
Defined.


Definition PropertyOnProdToRelation {A B : Setoid} (P : Property (ProdSetoid A B)) : Relation A B.
apply (Build_Relation A B (fun a b => underlying_prop _ P {| fst := a; snd := b |})).
intros.
apply (property_is_extensional (ProdSetoid A B) P {| fst := a; snd := c |}).
simpl. intuition. assumption.
Defined.

Lemma PR {A B : Setoid}:
  forall P : Property (ProdSetoid A B), exists R : Relation A B,
  forall a b,
  underlying_prop _ P {| fst := a; snd := b |}  <-> underlying_relation _ _ R a b.
intros.
exists (PropertyOnProdToRelation P).
intros.
simpl. intuition.
Qed.

Definition RelationToPropertyProd {A B : Setoid} (R: Relation A B): Property (ProdSetoid A B).
apply (Build_Property (ProdSetoid A B)
    (fun a => underlying_relation A B R (fst (|A|) (|B|) a) (snd (|A|) (|B|) a))).
intros.
simpl in H.
destruct H.
apply (relation_is_extensional A B R 
  (fst (| A |) (| B |) a) 
  (fst (| A |) (| B |) b)
  (snd (| A |) (| B |) a)
  (snd (| A |) (| B |) b)
); assumption.
Defined.

Lemma PR2 {A B : Setoid}:
  forall R : Relation A B, exists P : Property (ProdSetoid A B),
  forall a b,
  underlying_prop _ P {| fst := a; snd := b |}  <-> underlying_relation _ _ R a b.
intros.
exists (RelationToPropertyProd R).
intros. simpl. intuition.
Qed.



Definition IsEquivalenceRelation {A: Setoid} (R : Relation A A) := 
  Equivalence (R.(underlying_relation A A)).


Definition QuotientSetoid (A : Setoid) (R : Relation A A) (p : IsEquivalenceRelation R): Setoid :=
  {| U := | A |; eqv := underlying_relation A A R; eqv_is_equivalence := p |}.


Definition quotient (A : Setoid) (R: Relation A A) (p :IsEquivalenceRelation R) : 
  A ==> QuotientSetoid A R p.
apply (Build_Function A (QuotientSetoid A R p) (fun x => x)).
intros.
simpl. destruct p.
apply (relation_is_extensional A A R a a a b).
setoid_refl A. assumption. apply refl0.
Defined.


Lemma quotient_is_surjective {A: Setoid} {R: Relation A A} (p :IsEquivalenceRelation R): IsSurjective (quotient A R p).
unfold IsSurjective. intros. simpl.
exists b.
destruct p.
apply refl0.
Qed.



Definition quotient_lift {A B: Setoid} {R: Relation A A} {p: IsEquivalenceRelation R}
  (f : A ==> B)
  (q: forall a b : |A|, R.(underlying_relation A A) a b -> f`a ==[B] f`b):
  (QuotientSetoid A R p) ==> B.
apply (Build_Function (QuotientSetoid A R p) B (f.(underlying_map _ _))).
intros.
simpl in H.
apply q.
assumption.
Defined.


Lemma QuotientFactors {A B : Setoid} 
  (R: Relation A A) (p : IsEquivalenceRelation R) (f : A ==> B)
  (q : forall a b : |A|, R.(underlying_relation A A) a b -> f`a ==[B] f`b):
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
apply Build_Equivalence ; intuition. 
rewrite H. assumption.
Defined.


Definition IsSetoidFinite (S: Setoid): Prop :=
  exists n : nat, exists f : S ==> FinSetoid n,  IsBijective f.











