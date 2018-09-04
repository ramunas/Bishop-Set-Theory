Load MLTT.

Set Universe Polymorphism.

Record Setoid := {
  Setoid_Type : Type;
  Setoid_Equivalence : Setoid_Type -> Setoid_Type -> Type;
  Setoid_IsEquivalence: IsEquivalence Setoid_Equivalence;
}.

Notation "a ==[ A ] b" := (Setoid_Equivalence A a b) (at level 70, no associativity).
Notation "| A |" := (Setoid_Type A) (at level 101, no associativity).

Ltac setoid_refl A := apply (Equivalence_Reflexivity (Setoid_Equivalence A) (Setoid_IsEquivalence A)).
Ltac setoid_symm A := apply (Equivalence_Symmetry (Setoid_Equivalence A) (Setoid_IsEquivalence A)).
Ltac setoid_tran A e := apply (Equivalence_Transitivity (Setoid_Equivalence A) (Setoid_IsEquivalence A)) with (b := e).



Definition IsSetoidDiscrete (A : Setoid) : Type :=
  forall a b, Decidable (a ==[A] b).


Definition unique_for_setoid (A: Setoid) (P : (|A|) -> Type) (x: |A|): Type :=
  P x  *  forall a: |A|, P a -> a ==[A] x.


Notation "'exists_in' [ A ] ! x , P" :=
  (sigT (unique_for_setoid A (fun x => P))) (at level 60).


Definition IdentitySetoid (A : Type): Setoid.
apply (Build_Setoid A (@identity A) IdentityIsEquivalence).
Defined.


Definition ProdSetoid (A B : Setoid) : Setoid.
apply (Build_Setoid
        ((|A|) * (|B|))
        (fun a b => (Prod_Pr1 (|A|) (|B|) a ==[A] Prod_Pr1 (|A|) (|B|) b) &
                    (Prod_Pr2 (|A|) (|B|) a ==[B] Prod_Pr2 (|A|) (|B|) b))).
apply Build_IsEquivalence.
- intros. split. setoid_refl A. setoid_refl B.
- intros. split. setoid_symm A. intuition. setoid_symm B. intuition. 
- intros. split. setoid_tran A (Prod_Pr1 (| A |) (| B |) b). intuition. intuition.
                 setoid_tran B (Prod_Pr2 (| A |) (| B |) b). intuition. intuition.
Defined.


Notation "A # B" := (ProdSetoid A B) (at level 67, right associativity).


Record Function (A : Setoid) (B : Setoid) := {
  Function_Map : |A| -> |B|;
  Function_MapIsExtensional: 
    forall a b : |A|, a ==[A] b -> Function_Map a ==[B] Function_Map b;
}.


Definition FunctionApp {A B : Setoid} (f : Function A B) (x : |A| ) : |B| :=
  (Function_Map A B f) x.

Notation "f ` a" := (FunctionApp f a) (at level 69, left associativity).


Definition FunctionEquivalence {A B : Setoid} (f g : Function A B) : Type :=
  forall a : A.(Setoid_Type), f`a ==[B] g`a.

Lemma Function_eqv_is_equivalence {A B : Setoid}: IsEquivalence (@FunctionEquivalence A B).
apply Build_IsEquivalence.
- intros. unfold FunctionEquivalence. intros.
  apply (Equivalence_Reflexivity (Setoid_Equivalence B) (Setoid_IsEquivalence B)).
- unfold FunctionEquivalence. intros.
  apply (Equivalence_Symmetry (Setoid_Equivalence B) (Setoid_IsEquivalence B)). apply X.
- unfold FunctionEquivalence. intros. specialize (X a0). specialize (X0 a0).
  apply (Equivalence_Transitivity (Setoid_Equivalence B) (Setoid_IsEquivalence B)) with (b := b ` a0).
  assumption. assumption.
Defined.


Definition FunctionSetoid (A: Setoid) (B : Setoid) : Setoid := {|
  Setoid_Type := Function A B;
  Setoid_Equivalence := FunctionEquivalence;
  Setoid_IsEquivalence := Function_eqv_is_equivalence
|}.

Notation "A ==> B" := (FunctionSetoid A B) (at level 68, right associativity).

Definition FunctionCompose {A B C: Setoid} (g : |B ==> C|) (f : |A ==> B|): |A ==> C|.
  apply (Build_Function A C (fun a : |A| => g ` (f ` a))).
  intros.
  apply Function_MapIsExtensional.
  apply Function_MapIsExtensional.
  assumption.
Defined.

Notation "f |> g" := (FunctionCompose g f) (at level 65, left associativity).


Lemma FunctionCong 
  {A B : Setoid} (x y : |A|) (w : |B|)
  (f : |A ==> B|) (p : x ==[A] y) (q: f ` x ==[B] w) : f ` y ==[B] w.
apply (Function_MapIsExtensional A B f x y) in p.
assert (f ` y ==[B] f ` x).
setoid_symm B. assumption.
setoid_tran B (f ` x); assumption.
Qed.


Definition FunctionEval {A B : Setoid} : |(ProdSetoid (A ==> B) A) ==> B|.
apply (Build_Function (ProdSetoid (A ==> B) A) B
  (fun x => (Function_Map A B (Prod_Pr1 _ _ x)) (Prod_Pr2 _ _ x) )).
intros.
simpl.
destruct a. destruct b.  simpl in X. destruct X.
simpl.
unfold FunctionEquivalence in f.
specialize (f s2).
apply (FunctionCong s2 s0).
setoid_symm A; assumption.
assumption.
Defined.


Definition PreFunctionCurry {A B C : Setoid}
  (a : |A|)
  (f : | ProdSetoid A B ==> C |):
  |B ==> C|.
apply (Build_Function B C (fun b => f ` (a, b))).
intros.
apply Function_MapIsExtensional. simpl. split.
- setoid_refl A.
- assumption.
Defined.

Definition FunctionCurry {A B C : Setoid} 
  (f : | ProdSetoid A B ==> C|) : |A ==> (B ==> C)|.
apply (Build_Function A (B ==> C) (fun a => PreFunctionCurry a f) ).
intros. simpl. unfold FunctionEquivalence.
intros. simpl.
apply Function_MapIsExtensional. simpl. intuition.
setoid_refl B.
Defined.


Lemma FunctionCurrying {A B C: Setoid}
  (f : |ProdSetoid A B ==> C|) : 
  exists_in [ A ==> (B ==> C) ] ! h,
  forall (a : |A|) (b : |B|),
  FunctionEval ` ((h ` a), b) ==[C] f ` (a, b).
exists (FunctionCurry f). unfold unique_for_setoid. split.
- intros. simpl. setoid_refl C.
- intros. simpl. unfold FunctionEquivalence. intros. simpl. 
unfold FunctionEquivalence. intros. simpl.
specialize (X a0 a1).
simpl in X. assumption.
Qed.

Definition FunctionUnCurry {A B C : Setoid}
  (f : |A ==> B ==> C|) : |ProdSetoid A B ==> C|.
apply (Build_Function (A # B) C
  (fun x => f ` (Prod_Pr1 _ _ x) ` (Prod_Pr2 _ _ x))).
intros.
destruct a. destruct b. simpl in X. destruct X.
simpl.
apply (FunctionCong s2 s0).
setoid_symm B. assumption.
destruct f as [map ext].
simpl. apply ext. assumption.
Defined.

Lemma FunctionUnCurrying {A B C: Setoid}
  (f : |A ==> (B ==> C)|) : 
  exists_in [ ProdSetoid A B ==> C ] ! h,
  forall (a : |A|) (b : |B|),
  FunctionEval ` ((f ` a), b) ==[C] h ` (a, b).
exists (FunctionUnCurry f).
unfold unique_for_setoid. split.
- intros. simpl. setoid_refl C.
- simpl. intros. unfold FunctionEquivalence. intros. simpl.
  destruct a0. simpl.
  specialize (X s s0).
  setoid_symm C.
  assumption.
Qed.

Definition IdFunction {A : Setoid} : |A ==> A|.
  apply (Build_Function A A (fun x => x)).
  auto.
Defined.

Definition ProdSetoidMkPair {A B : Setoid}:
  |A ==> B ==> ProdSetoid A B|.
apply FunctionCurry.
apply IdFunction.
Defined.


Definition ProdSetoidPr1 {A B : Setoid}: |ProdSetoid A B ==> A|.
apply (Build_Function (ProdSetoid A B) A (fun x => Prod_Pr1 _ _ x)).
intros. destruct a. destruct b.
simpl. simpl in X. intuition.
Defined.

Definition ProdSetoidPr2 {A B : Setoid}: |ProdSetoid A B ==> B|.
apply (Build_Function (ProdSetoid A B) B (fun x => Prod_Pr2 _ _ x)).
intros. destruct a. destruct b.
simpl. simpl in X. intuition.
Defined.

Lemma ProdSetoidIsProduct {A B: Setoid} (a : |A|) (b : |B|): 
  ProdSetoidPr1 ` (ProdSetoidMkPair ` a ` b) ==[A] a &
  ProdSetoidPr2 ` (ProdSetoidMkPair ` a ` b) ==[B] b.
simpl. split. setoid_refl A. setoid_refl B.
Qed.

Definition Pairing {P A B : Setoid} (p1 : |P ==> A|) (p2: |P ==> B|): 
  |P ==> (A # B)|.
apply (Build_Function P (A # B) (fun p => ((p1 ` p), (p2 ` p)))).
intros.
simpl. split.
- destruct p1 as [p1f p1ext]. simpl. apply p1ext. assumption.
- destruct p2 as [p2f p2ext]. simpl. apply p2ext. assumption.
Defined.

(* TODO : missing uniquness *)
Lemma ConnonicityOfProduct { A B : Setoid}
  (P : Setoid)
  (p1 : |P ==> A|)
  (p2 : |P ==> B|):
  Pairing p1 p2 |> ProdSetoidPr1 ==[P ==> A] p1 &
  Pairing p1 p2 |> ProdSetoidPr2 ==[P ==> B] p2.
split.
- simpl. unfold FunctionEquivalence. intros. simpl. setoid_refl A.
- simpl. unfold FunctionEquivalence. intros. simpl. setoid_refl B.
Qed.


Definition SumSetoid (A B : Setoid) : Setoid.
apply (Build_Setoid
  ((|A|) + (|B|))
  (fun a b =>
    match a with
    | inl _ x =>
      match b with
      | inl _ y => x ==[A] y
      | inr _ y => False
      end
    | inr _ x =>
      match b with
      | inl _ y => False
      | inr _ y => x ==[B] y
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


Definition SumSetoidInl {A B : Setoid} : |A ==> SumSetoid A B|.
apply (Build_Function A ( SumSetoid A B) (fun x => inl _ x)).
intros. simpl. assumption.
Defined.

Definition SumSetoidInr {A B : Setoid} : |B ==> SumSetoid A B|.
apply (Build_Function B ( SumSetoid A B) (fun x => inr _ x)).
intros. simpl. assumption.
Defined.


Record Property (A : Setoid) := {
  Property_Prop : |A| -> Type;
  Property_PropIsExtensional: 
    forall a b: |A|, a ==[A] b -> Property_Prop a -> Property_Prop b
}.

Record Relation (A B : Setoid) := {
  Relation_Rel : |A| -> |B| -> Type;
  Relation_RelIsExtensional:
    forall a b : |A|, forall c d : |B|,
      a ==[A] b -> c ==[B] d ->
      Relation_Rel a c -> Relation_Rel b d
}.


Definition IsInjection {A B : Setoid} (f : |A ==> B|) : Type :=
  forall a b : |A|, f` a ==[B] f` b -> a ==[A] b.

Lemma FunctionInjectionCompositionIsInjection
  {A B C: Setoid}
  (f : |A ==> B|) (g : |B ==> C|) 
  (p : IsInjection f) (q: IsInjection g): IsInjection (f |> g).
unfold IsInjection in *.
simpl.
intros.
specialize (q (f ` a) (f ` b) X).
intuition.
Qed.

Definition IsSurjection {A B : Setoid} (f : |A ==> B|) : Type :=
  forall b: |B|, (sigma a: |A|, f ` a ==[B] b).


Lemma FunctionSurjectionCompositionIsSurjection
  {A B C: Setoid}
  (f : |A ==> B|) (g : |B ==> C|) 
  (p : IsSurjection f) (q: IsSurjection g): IsSurjection (f |> g).
unfold IsSurjection in *.
simpl. intros.
specialize (q b). destruct q.
specialize (p x). destruct p.
exists x0.
assert (x ==[B] f ` x0). setoid_symm B; assumption.
apply (FunctionCong x (f ` x0) b); assumption.
Qed.


Definition IsBijection {A B : Setoid} (f : |A ==> B|) : Type :=
  IsInjection f & IsSurjection f.

Lemma FunctionBijectionCompositionIsBijection
  {A B C: Setoid}
  (f : |A ==> B|) (g : |B ==> C|) 
  (p : IsBijection f) (q: IsBijection g): IsBijection (f |> g).
unfold IsBijection in *. destruct p. destruct q.
split.
- apply FunctionInjectionCompositionIsInjection; assumption.
- apply FunctionSurjectionCompositionIsSurjection; assumption.
Qed.

Definition ConstFunction {A B : Setoid} (x : |B|) : |A ==> B|.
  apply (Build_Function A B (fun y => x)).
  intros. setoid_refl B.
Defined.


Definition IsMono {A B : Setoid} (f : |A ==> B|) : Type :=
  forall C : Setoid, forall g h: |C ==> A|, g |> f  ==[C ==> B] h |> f -> g ==[C ==> A] h.

Definition IsEpi {A B : Setoid} (f : |A ==> B|) : Type :=
  forall C : Setoid, forall g h: |B ==> C|, f |> g ==[A ==> C] f |> h -> g ==[B ==> C] h.

Definition IsIso {A B : Setoid} (f : |A ==> B|) : Type :=
  sigma g : |B ==> A|, f |> g ==[A ==> A] IdFunction & g |> f ==[B ==> B] IdFunction.

Definition UnitSetoid : Setoid.
  apply (Build_Setoid unit (fun _ _ => unit)).
  apply Build_IsEquivalence; auto.
Defined.

Definition Unit_function {A : Setoid} : |A ==> UnitSetoid|.
apply (Build_Function A UnitSetoid (fun _ => tt)). intros. setoid_refl UnitSetoid.
Defined.

Lemma Unit_function_is_unique:
  forall B : Setoid,
    forall g: |B ==> UnitSetoid|, Unit_function ==[B ==> UnitSetoid] g.
intros. simpl. unfold FunctionEquivalence.
intros. simpl. constructor.
Defined.



Lemma MonoInjective {A B : Setoid}:
  forall f : |A ==> B|,
  IsMono f -> IsInjection f & IsInjection f -> IsMono f .
intros. split.
- unfold IsMono. unfold IsInjection.
  intros. specialize (X UnitSetoid (ConstFunction a) (ConstFunction b)).
  simpl in X. unfold FunctionEquivalence in X. simpl in X.
  intuition.
- unfold IsMono. unfold IsInjection.
  intros. simpl. unfold FunctionEquivalence; simpl. intros.
  specialize (X0 (g ` a) (h ` a)).
  simpl in X1.  unfold FunctionEquivalence in X1; simpl.
  specialize (X1 a). intuition.
Qed.


Definition HasRightInverse {A B : Setoid} (f : |A ==> B|) : Type :=
  sigma g : |B ==> A|, g |> f ==[B ==> B] IdFunction.

Lemma HasRightInverseIsSurjection {A B : Setoid}: 
  forall f : |A ==> B|,
  HasRightInverse f -> IsSurjection f.
intros. 
 unfold HasRightInverse. unfold IsSurjection.
  intros. destruct X as [g].
  simpl in s. unfold FunctionEquivalence in s.
  exists (g ` b). apply s.
Qed.


Definition IsChoiceSetoid (S : Setoid) : Type :=
  forall X : Setoid, forall f : |X ==> S|,
    IsSurjection f -> HasRightInverse f.



Record Subset (A: Setoid) := {
  Subset_Setoid: Setoid ;
  Subset_Injection: |Subset_Setoid ==> A|;
  Subset_InjectionIsInjection: IsInjection Subset_Injection
}.



Definition IsMemberOfSubset {A : Setoid} (a : |A|) (S: Subset A) : Type :=
  sigma x : |Subset_Setoid _ S|, ((Subset_Injection _ S)` x) ==[A] a.

Notation "a ::[ A ] S" := (@IsMemberOfSubset A a S) (at level 66, no associativity).

Definition IsSubsetOf {A : Setoid} (X Y : Subset A) : Type :=
  forall a : |A|, a ::[A] X -> a ::[A] Y.

Definition IsSubsetEquiv {A : Setoid} (X Y : Subset A): Type :=
  IsSubsetOf X Y & IsSubsetOf Y X.


Definition FunctionImageSetoid {A B : Setoid} (f : |A ==> B|) : Setoid.
apply (Build_Setoid (|A|) (fun a b => f ` a ==[B] f ` b)).
apply (Build_IsEquivalence).
- intros. setoid_refl B.
- intros. setoid_symm B. assumption.
- intros. setoid_tran B (f ` b); assumption.
Defined.

Definition FunctionImageFunction {A B : Setoid} (f : |A ==> B|):
  |FunctionImageSetoid f ==> B|.
apply (Build_Function (FunctionImageSetoid f) B (fun a => f ` a)).
intros. simpl in X. apply X.
Defined.

Definition FunctionImage {A B : Setoid} (f : |A ==> B|): Subset B.
apply (Build_Subset B (FunctionImageSetoid f) (FunctionImageFunction f)).
unfold IsInjection.
intros. simpl in *. assumption.
Defined.


Definition SigmaSetoid (X : Setoid) (P : Property X) : Setoid.
  apply (Build_Setoid (sigT (P.(Property_Prop X)))
        (fun a b =>
          projT1 a ==[X] projT1 b
        )).
  apply Build_IsEquivalence; intros.
  - setoid_refl X.
  - setoid_symm X. assumption.
  - setoid_tran X (projT1 b) ; assumption.
Defined.

Definition SigmaSetoid_Pr1 {X : Setoid} {P : Property X}: |SigmaSetoid X P ==> X|.
  apply (Build_Function (SigmaSetoid X P) X (fun x => projT1 x)).
  intros. simpl in X0. assumption.
Defined.


Definition SubsetComprehension (A : Setoid) (P : Property A) : Subset A.
  apply (Build_Subset A (SigmaSetoid A P) SigmaSetoid_Pr1).
  unfold IsInjection. intros.
  simpl in X.
  simpl.
  assumption.
Defined.


Lemma BetaSubsetMembership {A : Setoid} {P : Property A}:
  forall a : |A|,
  (a ::[A] (SubsetComprehension A P)) <--> P.(Property_Prop _) a.
intros. split.
- intros [H]. unfold IsMemberOfSubset in H. simpl in H.
  destruct H.
  simpl in s.
  destruct P as [prop ext]. simpl. apply (ext x a); assumption.
- intros. unfold IsMemberOfSubset.
  simpl.
  exists (existT _ a X). simpl. setoid_refl A.
Qed.


Definition IsSingleton {A : Setoid} (S : Subset A) : Type :=
  forall a b: |A|, a ::[A] S -> b ::[A] S -> a ==[A] b.


Definition Singleton {A : Setoid} (a : |A|) : Subset A.
assert (Property A).
apply (Build_Property A (fun x => (a ==[A] x))).
intros. setoid_tran A a0; assumption.
apply (SubsetComprehension A X).
Defined.

Lemma SingletonIsSingleton {A : Setoid} (a : |A|) : IsSingleton (Singleton a).
unfold IsSingleton.
intros.
apply BetaSubsetMembership in X.
apply BetaSubsetMembership in X0. simpl in *.
setoid_tran A a.
setoid_symm A; assumption.
assumption.
Qed.

Lemma SingletonHasOneMember {A : Setoid}: 
  forall a b: |A|, b ::[A] (Singleton a) -> a ==[A] b.
intros. apply BetaSubsetMembership in X. simpl in *. assumption.
Qed.


Definition SubsetUnion {A : Setoid} (S U : Subset A) : Subset A.
apply (SubsetComprehension A).
apply (Build_Property A (fun a => sum (a ::[A] S) (a ::[A] U))).
intros.
destruct X0.
- left. destruct i. unfold IsMemberOfSubset. exists x.
  setoid_tran A a; assumption.
- right. destruct i.  unfold IsMemberOfSubset. exists x.
  setoid_tran A a; assumption.
Defined.

Definition SubsetIntersection {A : Setoid} (S U : Subset A) : Subset A.
apply (SubsetComprehension A).
apply (Build_Property A (fun a => a ::[A] S & a ::[A] U)).
intros. destruct X0. split.
- destruct i. unfold IsMemberOfSubset. exists x.
  setoid_tran A a; assumption.
- destruct i0. unfold IsMemberOfSubset. exists x.
  setoid_tran A a; assumption.
Defined.

Definition FunctionInverseImage {A B : Setoid} (S : Subset B) (f : |A ==> B|) : Subset A.
apply (SubsetComprehension A).
apply (Build_Property A (fun a => (f ` a) ::[B] S)).
intros.
destruct X0.
exists x.
setoid_symm B.
apply (FunctionCong a b). assumption.
setoid_symm B.
assumption.
Defined.

Definition BijectionInversion {A B : Setoid} 
  (f : |A ==> B|) (p: IsBijection f): | B ==> A|.
apply (Build_Function B A
  (fun b => projT1 ((Prod_Pr2 _ _ p) b))).
intros.
destruct p. simpl.
destruct i0. simpl.
destruct i0. simpl.
apply i.
assert (f ` x ==[B] b).
setoid_tran B a; assumption.
setoid_tran B b. assumption.
setoid_symm B. assumption.
Defined.

Lemma BijectionInversionIsBijection {A B :Setoid}
  (f : |A ==> B|) (p: IsBijection f) : IsBijection (BijectionInversion f p).
destruct p.
split.
- unfold IsInjection in *. simpl.
  unfold IsSurjection in *. intros.
  destruct i0. 
  destruct i0. simpl in *.
  assert (f ` x ==[B] f ` x0).
  apply (Function_MapIsExtensional _ _ f). assumption.
  assert (a ==[B] f ` x0).
  setoid_tran B (f ` x). setoid_symm B. assumption. assumption.
  setoid_tran B (f ` x0). assumption. assumption.
- unfold IsInjection in *. simpl. unfold IsSurjection in *. intros.
  simpl.
  exists (f ` b). destruct i0. simpl.
  intuition.
Qed.

Definition BijectionInversionBijection {A B : Setoid} 
  (f : |A ==> B|) (p: IsBijection f): sigma g :| B ==> A|, IsBijection g.
exists (BijectionInversion f p).
apply (BijectionInversionIsBijection f p).
Defined.


Lemma BijectionToIso {A B : Setoid}  (f : |A ==> B|) (p: IsBijection f) : IsIso f.
unfold IsIso.
exists (BijectionInversion f p).
simpl. split; unfold FunctionEquivalence.
- intros. destruct p. simpl. destruct i0. simpl. apply i. assumption.
- intros. destruct p. simpl. destruct i0. simpl. assumption.
Qed.

Lemma IsoToBijection {A B : Setoid}  (f : |A ==> B|) (p: IsIso f) : IsBijection f.
split.
- unfold IsInjection. intros. unfold IsIso in p. destruct p as [g]. destruct p.
  assert (g ` (f ` a) ==[A] a).
  simpl in s. unfold FunctionEquivalence in s. simpl in s. apply s.
  assert (g ` (f ` b) ==[A] b).
  simpl in s. unfold FunctionEquivalence in s. simpl in s. apply s.
  assert (g ` (f ` a) ==[A] g ` (f ` b)).
  apply (Function_MapIsExtensional _ _ g). assumption.
  assert (a ==[ A] g ` (f ` a)). setoid_symm A; assumption.
  assert (a ==[A] g ` (f ` b)). setoid_tran A (g ` (f ` a)); assumption.
  setoid_tran A (g ` (f ` b)); assumption.
- unfold IsSurjection. intros.
  unfold IsIso in p. destruct p as [g]. destruct p.
  exists (g ` b).
  simpl in s0. unfold FunctionEquivalence in s0. apply s0.
Qed.


Lemma BijectionIsoCorrespondence 
  {A B : Setoid} (f : |A ==> B|) : IsBijection f <--> IsIso f.
split.
- apply BijectionToIso.
- apply IsoToBijection.
Qed.

Lemma ExtPropConj {A: Setoid} (P Q : Property A): Property A.
  apply (Build_Property A (fun x => Property_Prop A P x & Property_Prop A Q x)).
  intros. destruct X0. split.
  apply (Property_PropIsExtensional A P a); assumption.
  apply (Property_PropIsExtensional A Q a); assumption.
Defined.

Lemma ExtPropDisj {A: Setoid} (P Q : Property A): Property A.
  apply (Build_Property A (fun x => sum (Property_Prop A P x) (Property_Prop A Q x))).
  intros. destruct X0.
  - left. apply (Property_PropIsExtensional A P a); assumption.
  - right. apply (Property_PropIsExtensional A Q a); assumption.
Defined.


Definition PropertySetoid (A : Setoid) : Setoid.
apply (Build_Setoid (Property A)
  (fun P Q => forall a, Property_Prop A P a <--> Property_Prop A Q a)).
split.
- intros. split; intuition.
- intros. split.
  + intros. apply X. assumption.
  + intros. apply X. assumption.
- intros. split.
  + intros. apply X0.  apply X. assumption.
  + intros. apply X.  apply X0. assumption.
Defined.


Definition RelationSetoid (A B : Setoid): Setoid.
apply (Build_Setoid (Relation A B)
  (fun R S => forall a b, Relation_Rel A B R a b <--> Relation_Rel A B S a b)).
split; intros.
- split; intros.
  assumption. assumption.
- split; intros. apply X. assumption. apply X. assumption.
- split; intros. apply X0. apply X. assumption. apply X. apply X0. assumption. 
Defined.


Definition PropertyOnProdToRelation {A B : Setoid} 
  (P : Property (A # B)) : Relation A B.
apply (Build_Relation A B (fun a b => Property_Prop _ P (a, b))).
intros.
apply (Property_PropIsExtensional (ProdSetoid A B) P (a, c)).
simpl. intuition. assumption.
Defined.

Definition FunctionPropertyOnProdToRelation {A B : Setoid}:
  | PropertySetoid (A # B) ==> RelationSetoid A B |.
apply (Build_Function (PropertySetoid (A # B)) (RelationSetoid A B) 
  PropertyOnProdToRelation).
intros.
simpl. intros. apply X.
Defined.


Definition RelationToPropertyProd {A B : Setoid} (R: Relation A B): Property (A # B).
apply (Build_Property (ProdSetoid A B)
    (fun a => Relation_Rel A B R (Prod_Pr1 (|A|) (|B|) a) (Prod_Pr2 (|A|) (|B|) a))).
intros.
simpl in X.
destruct X.
apply (Relation_RelIsExtensional A B R 
  (Prod_Pr1 (| A |) (| B |) a) 
  (Prod_Pr1 (| A |) (| B |) b)
  (Prod_Pr2 (| A |) (| B |) a)
  (Prod_Pr2 (| A |) (| B |) b)
); assumption.
Defined.

Definition FunctionRelationToPropertyProd {A B : Setoid}:
  | RelationSetoid A B ==> PropertySetoid (A # B) |.
apply (Build_Function (RelationSetoid A B) (PropertySetoid (A # B)) 
  RelationToPropertyProd).
intros.
simpl. intros. destruct a0. simpl. apply X.
Defined.

Lemma RelationPropertyProdIsIso
  {A B : Setoid} : IsIso (@FunctionRelationToPropertyProd A B).
exists FunctionPropertyOnProdToRelation.
simpl. unfold FunctionEquivalence. simpl. split; intros.
- setoid_refl (RelationSetoid A B).
- destruct a0. simpl. setoid_refl (PropertySetoid (A # B)).
Qed.


Definition IsEquivalenceRelation {A: Setoid} (R : Relation A A) := 
  IsEquivalence (R.(Relation_Rel A A)).


Definition QuotientSetoid (A : Setoid) (R : Relation A A) (p : IsEquivalenceRelation R): Setoid :=
  {| Setoid_Type := | A |; Setoid_Equivalence := Relation_Rel A A R; Setoid_IsEquivalence := p |}.


Definition Quotient (A : Setoid) (R: Relation A A) (p :IsEquivalenceRelation R) : 
  |A ==> QuotientSetoid A R p|.
apply (Build_Function A (QuotientSetoid A R p) (fun x => x)).
intros.
simpl. destruct p as [refl].
apply (Relation_RelIsExtensional A A R a a a b).
setoid_refl A. assumption. apply refl.
Defined.


Lemma QuotientIsSurjection {A: Setoid} {R: Relation A A} (p :IsEquivalenceRelation R): IsSurjection (Quotient A R p).
unfold IsSurjection. intros. simpl.
exists b.
destruct p as [refl].
apply refl.
Qed.


Definition LiftFunctionToQuotient {A B: Setoid} {R: Relation A A} {p: IsEquivalenceRelation R}
  (f : |A ==> B|)
  (q: forall a b : |A|, R.(Relation_Rel A A) a b -> f`a ==[B] f`b):
  |(QuotientSetoid A R p) ==> B|.
apply (Build_Function (QuotientSetoid A R p) B (f.(Function_Map _ _))).
intros.
simpl in X.
apply q.
assumption.
Defined.


Lemma QuotientFactors {A B : Setoid} 
  (R: Relation A A) (p : IsEquivalenceRelation R) (f : |A ==> B|)
  (q : forall a b : |A|, R.(Relation_Rel A A) a b -> f`a ==[B] f`b):
  sigma h : |QuotientSetoid A R p ==> B|,
  forall x : |A|,
  h ` (Quotient A R p ` x) ==[B] f ` x.
exists (LiftFunctionToQuotient f q). simpl. intros.
setoid_refl B.
Qed.


Definition NatSetoid : Setoid := IdentitySetoid nat.


Definition FinOrdSubset (n : nat) : Subset NatSetoid.
apply (SubsetComprehension ).
(* apply (Build_Property NatSetoid (fun x => x < n)). *)
apply (Build_Property NatSetoid (fun x => LessThan x n)).
intros. simpl in X. rewrite <- X. assumption.
Defined.

Definition FinSetoid (n : nat): Setoid := Subset_Setoid NatSetoid (FinOrdSubset n).

Definition NatToFinSetoid {x : nat} (n: nat) (p: LessThan n x): |FinSetoid x| :=
existT _ n p.

Definition FinSetoidToNat {x : nat} (n : |FinSetoid x|) : nat :=
match n with existT _ x _ => x end.

Definition IsSetoidFinite (S: Setoid): Type :=
  sigma n : nat, sigma f : |S ==> FinSetoid n|,  IsBijection f.

Definition IsSubsetFinite {A : Setoid} (S : Subset A) : Type :=
  IsSetoidFinite (Subset_Setoid A S).

Definition IsSubsetDecidable {A : Setoid} (S : Subset A) : Type :=
  forall a, Decidable (a ::[A] S).

(* TODO:
Lemma FiniteSubsetMembershipDecidable {A : Setoid}
  (q : IsSetoidDiscrete A)
  (S : Subset A) (p : IsSubsetFinite S) :
  IsSubsetDecidable S.
unfold IsSubsetDecidable.
intros. destruct p.  destruct s as [f fbij].
unfold IsMemberOfSubset.
unfold IsSetoidDiscrete in q.
unfold Decidable in *.
assert (inv : | FinSetoid x ==> Subset_Setoid A S|).
apply (BijectionInversion f fbij).

induction x.
- unfold FinSetoid in inv. simpl in inv. destruct inv.

Print nat_rect.

ads
*)

Definition EnumerateSingletonSubset {A : Setoid} (a : |A|) : 
  | Subset_Setoid A (Singleton a) ==> FinSetoid 1|.
assert (LessThan 0 1) as obvious. unfold LessThan. apply LessThanOrEqualRefl.
apply (Build_Function (Subset_Setoid A (Singleton a)) (FinSetoid 1)
  (fun x => existT _ 0 obvious)).
simpl. intros. reflexivity.
Defined.

Lemma SingletonIsFinite {A : Setoid} (a : |A|) : IsSubsetFinite (Singleton a).
unfold IsSubsetFinite.
unfold IsSetoidFinite.
exists (S 0).
exists (EnumerateSingletonSubset a).
split.
- unfold IsInjection. intros.
  destruct a0. destruct b. simpl in *.
  setoid_tran A a. setoid_symm A. assumption. assumption.
- unfold IsSurjection. intros. simpl.
  assert (sigT (fun x : | A | => a ==[ A] x)) as ael.
  exists a. setoid_refl A.
  exists ael.
  destruct b. simpl in *.
  unfold LessThan in p.
  inversion p. reflexivity. apply ZeroIsTheLeast in H1. discriminate H1.
Qed.

(* TODO:
Lemma UnionOfFiniteSubsetsIsFinite {A : Setoid}
  (S U : Subset A) (p : IsSubsetFinite S) (q: IsSubsetFinite U):
  IsSubsetFinite (SubsetUnion S U).
unfold IsSubsetFinite in *.
unfold IsSetoidFinite in *.
destruct p. destruct q.
exists (x + x0).
destruct s. destruct s0.
assert (f : |Subset_Setoid A (SubsetUnion S U) ==> FinSetoid (x + x0)|).
apply (Build_Function (Subset_Setoid A (SubsetUnion S U)) (FinSetoid (x + x0))
  (fun x => )
).
intros.
*)


Definition BijectionSetoid (A B : Setoid) : Setoid.
apply (Build_Setoid (sigma f : |A ==> B|, IsBijection f)
  (fun f g => FunctionEquivalence (projT1 f) (projT1 g))
).
apply Build_IsEquivalence.
- intros. destruct a. simpl. setoid_refl (A ==> B).
- intros. destruct a. destruct b. simpl in *. setoid_symm (A ==> B). assumption.
- intros. destruct a. destruct b. destruct c. simpl in *. setoid_tran (A ==> B) x0; assumption.
Defined.









