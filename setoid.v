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
  P x  &  (forall a: |A|, P a -> a ==[A] x).


Notation "'exists_in' [ A ] ! x , P" :=
  (sigT (unique_for_setoid A (fun x => P))) (at level 60).

Notation "'sigma!' x : A , P" :=
  (sigT (unique_for_setoid A (fun x => P))) (x ident, at level 60, A at level 60).



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

Definition FunctionIdentity {A : Setoid} : |A ==> A|.
apply (Build_Function A A (fun x => x)). intuition.
Defined.

Lemma FunctionIdentityLeft {A B : Setoid} (f : |A ==> B|):
  FunctionIdentity |> f ==[_] f.
simpl. unfold FunctionEquivalence. simpl. intro. setoid_refl B.
Defined.

Lemma FunctionIdentityRight {A B : Setoid} (f : |A ==> B|):
  f ==[_] FunctionIdentity |> f.
simpl. unfold FunctionEquivalence. simpl. intro. setoid_refl B.
Defined.


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
      | inr _ y => Empty_set
      end
    | inr _ x =>
      match b with
      | inl _ y => Empty_set
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

Definition SumSetoidDeconstruct {A B C : Setoid} :
  |SumSetoid A B ==> (A ==> C) ==> (B ==> C) ==> C|.
apply FunctionCurry.
apply FunctionCurry.
apply (Build_Function ((SumSetoid A B # (A ==> C)) # (B ==> C)) C
  (fun x => 
      let s := ProdSetoidPr1 ` (ProdSetoidPr1 ` x) in
      let f := ProdSetoidPr2 ` (ProdSetoidPr1 ` x) in
      let g := ProdSetoidPr2 ` x in
      match s with
      | inl _ a => f ` a
      | inr _ b => g ` b
      end
)).
intros.
destruct a. destruct s.
destruct b. destruct s2.
simpl.
assert (s ==[_] s2). apply X.
destruct s.
destruct s2. intuition.
simpl in X.
- simpl in X0. assert (s1 ==[_] s4) as eq. apply X.
  apply (FunctionCong s2 s). setoid_symm A. assumption.
  apply eq.
- contradiction.
- destruct s2.
  + simpl in X0. contradiction.
  + simpl in X0. assert (s0 ==[_] s3) as eq. apply X.
  apply (FunctionCong s2 s). setoid_symm B. assumption.
  apply eq.
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


Lemma BijectionInversionLeftCancelable
  {A B : Setoid} 
  (f : |A ==> B|) (p: IsBijection f):
  forall x, BijectionInversion f p ` (f ` x) ==[A] x.
intros.
simpl. destruct p. simpl. destruct i0. simpl. apply i. assumption.
Defined.

Lemma BijectionInversionRightCancelable
  {A B : Setoid} 
  (f : |A ==> B|) (p: IsBijection f):
  forall x, (f ` (BijectionInversion f p ` x)) ==[B] x.
intros. simpl. destruct p. simpl. destruct i0. simpl. assumption.
Defined.

Definition IsMono {A B : Setoid} (f : |A ==> B|) : Type :=
  forall C : Setoid, forall g h: |C ==> A|, g |> f  ==[C ==> B] h |> f -> g ==[C ==> A] h.

Definition IsEpi {A B : Setoid} (f : |A ==> B|) : Type :=
  forall C : Setoid, forall g h: |B ==> C|, f |> g ==[A ==> C] f |> h -> g ==[B ==> C] h.

Definition IsIso {A B : Setoid} (f : |A ==> B|) : Type :=
  sigma g : |B ==> A|, f |> g ==[A ==> A] IdFunction & g |> f ==[B ==> B] IdFunction.


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

Definition ConstFunction {A B : Setoid} (x : |B|) : |A ==> B|.
  apply (Build_Function A B (fun y => x)).
  intros. setoid_refl B.
Defined.

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


Definition ProdSetoidAssociativity {A B C: Setoid}: |A # (B # C) ==> (A # B) # C|.
apply (Build_Function (A # (B # C)) ((A # B) # C)
  (fun x => ((ProdSetoidPr1 ` x, ProdSetoidPr1 ` (ProdSetoidPr2 ` x)), 
             ProdSetoidPr2 ` (ProdSetoidPr2 ` x)))).
intros. simpl. split. split.
- destruct a. destruct s0. simpl. destruct b. simpl. apply X.
- destruct a. destruct s0. simpl. destruct b. simpl. destruct s3. simpl. apply X.
- destruct a. destruct s0. simpl. destruct b. destruct s3. simpl. apply X.
Defined.

Lemma ProdSetoidAssociativityBijection {A B C: Setoid}:
  IsBijection (@ProdSetoidAssociativity A B C).
split.
- unfold IsInjection. intros.
  destruct a. destruct s0. destruct b. destruct s3.
  simpl in X. 
  simpl. intuition.
- unfold IsSurjection. intros.
  exists ( (ProdSetoidPr1 ` (ProdSetoidPr1 ` b), (ProdSetoidPr2 ` (ProdSetoidPr1 ` b), 
           ProdSetoidPr2 ` b)) ).
  destruct b. destruct s.
  simpl. intuition. setoid_refl A. setoid_refl B. setoid_refl C.
Defined.


Definition ProdSetoidSwap {A B : Setoid}:
  | A # B ==> B # A| := Pairing ProdSetoidPr2 ProdSetoidPr1.

Lemma ProdSetoidSwapIso {A B : Setoid}:
  IsIso (@ProdSetoidSwap A B).
unfold IsIso.
exists (@ProdSetoidSwap B A).
simpl. split.
- unfold FunctionEquivalence. intros. simpl. split. setoid_refl A. setoid_refl B.
- unfold FunctionEquivalence. intros. simpl. split. setoid_refl B. setoid_refl A.
Defined.

Lemma ProdSetoidSwapBijection {A B : Setoid}:
  IsBijection (@ProdSetoidSwap A B).
apply IsoToBijection.
apply ProdSetoidSwapIso.
Defined.

Definition FunctionExchange {A B C: Setoid}
  (f : | A # B ==> C |): | B # A ==> C | :=
ProdSetoidSwap |> f.

Definition FunctionAssociativityR {A B C D: Setoid}
  (f : | A # (B # C) ==> D |): | (A # B) # C ==> D | :=
BijectionInversion ProdSetoidAssociativity ProdSetoidAssociativityBijection |> f.

Definition FunctionAssociativityL {A B C D: Setoid}
  (f : | (A # B) # C ==> D |): | A # (B # C) ==> D | :=
ProdSetoidAssociativity |> f.


Definition SumSetoidDeconstruct2 {A B C : Setoid} :
  |(A ==> C) ==> (B ==> C) ==> SumSetoid A B  ==> C|.
apply FunctionCurry.
apply FunctionCurry.
apply FunctionExchange.
apply FunctionAssociativityL.
apply FunctionUnCurry.
apply FunctionUnCurry.
apply SumSetoidDeconstruct.
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


Record Subset (A: Setoid) := {
  Subset_Setoid: Setoid ;
  Subset_Injection: |Subset_Setoid ==> A|;
  Subset_InjectionIsInjection: IsInjection Subset_Injection
}.


Definition SubsetComprehension (A : Setoid) (P : Property A) : Subset A.
  apply (Build_Subset A (SigmaSetoid A P) SigmaSetoid_Pr1).
  unfold IsInjection. intros.
  simpl in X.
  simpl.
  assumption.
Defined.

Definition IsMemberOfSubset {A : Setoid} (a : |A|) (S: Subset A) : Type :=
  sigma x : |Subset_Setoid _ S|, ((Subset_Injection _ S)` x) ==[A] a.

Notation "a ::[ A ] S" := (@IsMemberOfSubset A a S) (at level 66, no associativity).

Lemma SubsetIsMemberOfTransport {A : Setoid} (S : Subset A) (a b : |A|):
  a ==[A] b -> a ::[A] S -> b ::[A] S.
intros.
unfold IsMemberOfSubset in *.
destruct X0.
assert (Subset_Injection A S ` x ==[A] b).
setoid_tran A a; assumption.
exists x. assumption.
Defined.

Definition IsMemberOfSubsetSetoid
  {A : Setoid} (a : |A|) (S: Subset A) : Setoid.
apply (SigmaSetoid (Subset_Setoid _ S)).
apply (Build_Property _ (fun x => ((Subset_Injection _ S) ` x) ==[A] a)).
intros.
apply (FunctionCong a0 b a (Subset_Injection A S)); assumption.
Defined.

Lemma SubsetIsMemberOfSetoidTransport {A : Setoid} (S : Subset A) (a b : |A|):
  a ==[A] b -> |IsMemberOfSubsetSetoid a S| -> |IsMemberOfSubsetSetoid b S|.
apply SubsetIsMemberOfTransport.
Defined.

Lemma IsMemberOfSubsetTypeToSetoid
{A : Setoid} (a : |A|) (S: Subset A) (p: a ::[A] S) : 
  |IsMemberOfSubsetSetoid a S|.
apply p.
Defined.

Definition SubsetMembershipWitness
  {A : Setoid} (a : |A|) (S: Subset A):
  |IsMemberOfSubsetSetoid a S ==> Subset_Setoid A S|.
apply SigmaSetoid_Pr1.
Defined.

Lemma SubsetMembershipWitnessExtensional {A : Setoid} (a b : |A|)  (S: Subset A):
  a ==[A] b -> forall x y,
  SubsetMembershipWitness a S ` x ==[Subset_Setoid A S]
  SubsetMembershipWitness b S ` y.
intros.
simpl.
destruct x. destruct y. simpl in *.
pose (LHS := Subset_Injection A S ` x).
assert (LHS ==[ A] b). setoid_tran A a. assumption. assumption.
assert (LHS ==[A] Subset_Injection A S ` x0). setoid_tran A b. assumption. setoid_symm A. assumption.
apply (Subset_InjectionIsInjection).
assumption.
Defined.

Lemma SubsetMembershipWitnessIsInjection
  {A : Setoid} (a : |A|) (S: Subset A): 
  IsInjection (SubsetMembershipWitness a S).
unfold IsInjection. intros. cbn in X. destruct a0. destruct b. simpl in *.
assumption.
Defined.


Lemma SubsetMembershipWitnessIsInjectionWithTransfer
  {A : Setoid} (S: Subset A):
  forall a b x y, 
  SubsetMembershipWitness a S ` x ==[Subset_Setoid A S]
  SubsetMembershipWitness b S ` y ->
  sigma p: a ==[A] b, 
  (SubsetIsMemberOfSetoidTransport S a b p x) ==[IsMemberOfSubsetSetoid b S] y.
intros.
destruct x. destruct y. simpl in *.
pose (LHS := a).
assert (LHS ==[A] Subset_Injection A S ` x). setoid_symm A ; assumption.
assert (Subset_Injection A S ` x ==[A] Subset_Injection A S ` x0).
  apply (Function_MapIsExtensional _ _ (Subset_Injection _ _)). assumption.
assert (LHS ==[A] Subset_Injection A S ` x0).
  setoid_tran A (Subset_Injection A S ` x); assumption.
assert (LHS ==[A] b). setoid_tran A (Subset_Injection A S ` x0); assumption.
exists X3.
assumption.
Defined.


Definition IsSubsetDecidable {A : Setoid} (S : Subset A) : Type :=
  forall a, Decidable (a ::[A] S).


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
Defined.


Definition SubsetOfSubsetInjection
  {A : Setoid} (X Y : Subset A)
  (incl : forall a : | A |, a ::[ A] X -> a ::[ A] Y):
  | Subset_Setoid A X ==> Subset_Setoid A Y |.
apply (Build_Function _ _
  (fun x =>
  SubsetMembershipWitness _ _ `
       ( incl (Subset_Injection A X ` x) 
             (existT _ x
             (Equivalence_Reflexivity (Setoid_Equivalence A) (Setoid_IsEquivalence A)
              (Subset_Injection A X ` x)
              ) ) )
  )
).
intros.
apply SubsetMembershipWitnessExtensional.
apply (Function_MapIsExtensional _ _ (Subset_Injection A X)).
assumption.
Defined.

Lemma SubsetOfSubsetInjectionIsInjection
  {A : Setoid} (X Y : Subset A)
  (incl : forall a : | A |, a ::[ A] X -> a ::[ A] Y):
  IsInjection (SubsetOfSubsetInjection X Y incl).
unfold IsInjection.
intros.
apply SubsetMembershipWitnessIsInjectionWithTransfer in X0.
destruct X0.
apply (Subset_InjectionIsInjection _ _).
assumption.
Defined.


Lemma SigmaUniqueness (A : Type) (P : A -> Type) (p : sigma x, P x):
  existT _ (projT1 p) (projT2 p) = p.
destruct p.
simpl.
reflexivity.
Defined.


Lemma IsSubsetOfToInjection {A : Setoid}
  (X Y : Subset A): 
  IsSubsetOf X Y    -> sigma! f : (Subset_Setoid A X ==> Subset_Setoid A Y),
                      (IsInjection f &
                      Subset_Injection A X ==[ _ ]
                      (f |> Subset_Injection A Y)).
  unfold IsSubsetOf. intro incl.
  assert (Subset_Injection A X ==[ _ ]
                      ((SubsetOfSubsetInjection X Y incl |> Subset_Injection A Y)))
  as factors.
  simpl. unfold FunctionEquivalence. intros.
  unfold IsMemberOfSubset in incl.
  simpl. setoid_symm A.
  apply (projT2 (incl 
        (Subset_Injection A X ` a)
        (existT _ a (Equivalence_Reflexivity (Setoid_Equivalence A) (Setoid_IsEquivalence A)
              (Subset_Injection A X ` a))))).

  exists (SubsetOfSubsetInjection X Y incl).
  split.
  + split. apply SubsetOfSubsetInjectionIsInjection. apply factors.
  + intro f. intros. destruct X0.
    simpl. unfold FunctionEquivalence. intros.
    simpl in s. unfold FunctionEquivalence in s. simpl in s.
    apply (Subset_InjectionIsInjection A Y).
    setoid_tran A (Subset_Injection A X ` a). setoid_symm A. apply (s a).
    apply factors.
Defined.

Lemma InjectionToIsSubsetOf {A : Setoid}
  (X Y : Subset A): 
  (sigma f : |Subset_Setoid A X ==> Subset_Setoid A Y|,
  (IsInjection f &
  Subset_Injection A X ==[ _ ] (f |> Subset_Injection A Y))) -> IsSubsetOf X Y.
  intros. unfold IsSubsetOf. unfold IsMemberOfSubset. intros.
  destruct X0 as [f].
  destruct p as [finj fagr].
  destruct X1.
  exists (f ` x).
  specialize (fagr x).
  setoid_tran A (Subset_Injection A X ` x).
  setoid_symm A. assumption. assumption.
Defined.

(*
Lemma IsSubsetOfInjectionCorrespondance {A : Setoid}
  (X Y : Subset A): 
  IsSubsetOf X Y <--> sigma! f : (Subset_Setoid A X ==> Subset_Setoid A Y),
                      (IsInjection f &
                      Subset_Injection A X ==[ _ ]
                      (f |> Subset_Injection A Y)).
split.
- unfold IsSubsetOf. intro incl.
  assert (Subset_Injection A X ==[ _ ]
                      ((SubsetOfSubsetInjection X Y incl |> Subset_Injection A Y)))
  as factors.
  simpl. unfold FunctionEquivalence. intros.
  unfold IsMemberOfSubset in incl.
  simpl. setoid_symm A.
  apply (projT2 (incl 
        (Subset_Injection A X ` a)
        (existT _ a (Equivalence_Reflexivity (Setoid_Equivalence A) (Setoid_IsEquivalence A)
              (Subset_Injection A X ` a))))).

  exists (SubsetOfSubsetInjection X Y incl).
  split.
  + split. apply SubsetOfSubsetInjectionIsInjection. apply factors.
  + intro f. intros. destruct X0.
    simpl. unfold FunctionEquivalence. intros.
    simpl in s. unfold FunctionEquivalence in s. simpl in s.
    apply (Subset_InjectionIsInjection A Y).
    setoid_tran A (Subset_Injection A X ` a). setoid_symm A. apply (s a).
    apply factors.
- intros. unfold IsSubsetOf. unfold IsMemberOfSubset. intros.
  destruct X0 as [f]. destruct u.
  destruct p as [finj fagr].
  destruct X1.
  exists (f ` x).
  specialize (fagr x).
  setoid_tran A (Subset_Injection A X ` x).
  setoid_symm A. assumption. assumption.
Defined.

*)



Definition EmptySubset {A: Setoid} : Subset A.
apply SubsetComprehension.
apply (Build_Property _ (fun _ => Empty_set)).
intros. assumption.
Defined.


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

Definition SubsetComplement {A : Setoid}
  (S : Subset A): Subset A.
apply SubsetComprehension.
apply (Build_Property _ (fun x => not (x ::[A] S))).
intros. 
apply X0.
apply (SubsetIsMemberOfTransport S b a).
setoid_symm A; assumption. assumption.
Defined.

Definition SubsetSubstract {A : Setoid}
  (S U : Subset A): Subset A.
apply SubsetComprehension.
apply (Build_Property _ (fun a => a ::[A] S & not (a ::[A] U))).
intros. destruct X0.
split.
- apply (SubsetIsMemberOfTransport _ a b); assumption.
- intros. apply e. apply (SubsetIsMemberOfTransport _ b a).
  setoid_symm A. assumption. assumption.
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

Lemma FinSetRec
  (n : nat)
  (P : nat -> Type)
  (q: forall x: nat, LessThan x n -> P x):
  forall y: |FinSetoid n|, P (FinSetoidToNat y).
intros.
simpl in y.
destruct y.
simpl.
apply q.
assumption.
Defined.

Lemma FinSubsetDecidable {n : nat}:
  IsSubsetDecidable (FinOrdSubset n).
unfold IsSubsetDecidable. simpl.
unfold IsMemberOfSubset. simpl.
induction n.
- intros. right. intros. destruct H. destruct x. unfold LessThan in l.
  apply (PositiveIsNotLessThanOrEqualToZero x). assumption.
- induction a.
  + specialize (IHn 0). destruct IHn.
    * left. destruct s. destruct x. simpl in i.
      assert (LessThan x (S n)).
      unfold LessThan in *. apply LessThanOrEqualSucc. assumption.
      exists (existT _ x H). simpl. assumption.
    * left.
      assert (LessThan 0 (S n)). unfold LessThan.
      apply (LessThanOrEqualPreservedBySucc 0 n).
      apply ZeroIsTheLeast.
      exists (existT _ 0 H). simpl. reflexivity.
  + destruct (IHn a).
    { (* a < n *) destruct s. destruct x. simpl in i. rewrite -> i in l.
      (* a + 1 < n + 1 *) assert (LessThan (S a) (S n)).
      unfold LessThan in *.
      apply LessThanOrEqualPreservedBySucc in l. assumption.
      left. exists (existT _ (S a) H). simpl. reflexivity.
    } {
      (* not (a < n) -> n <= a *)
      assert (not (LessThan a n)).
      intros. apply e. exists (existT _ a H). simpl. reflexivity.
      unfold LessThan in H. apply LessThanInvert in H.
      right.
      intros. destruct H0. destruct x. simpl in i. rewrite i in l.
      unfold LessThan in l. apply LessThanOrEqualPreservedBySucc in l.
      assert (LessThanOrEqual (S a) a).
      apply (LessThanOrEqualTransitive (S a) n a); assumption.
      apply LessThanIrreflexive in H0. contradiction.
    }
Defined.


Lemma SigmaDistributesOverDisjunction:
  forall A: Type,
  forall P Q : A -> Type,
  (sigma x : A , P x) + (sigma y : A , Q y) <-->
  sigma x : A, (P x + Q x) % type.
intros. split.
- intros. destruct X.
  + destruct s. exists x. left. assumption.
  + destruct s. exists x. right. assumption.
- intros. destruct X. destruct s.
  + left. exists x. assumption.
  + right. exists x. assumption.
Defined.

Definition InjectInFinSetoid (n : nat) : | FinSetoid n| -> | FinSetoid (S n) | :=
fun x => match x with existT _ n p => existT _ n (LessThanOrEqualSucc _ _ p) end.


Definition InjectionFinSetoid {n : nat} : | FinSetoid n ==> FinSetoid (S n) |.
apply (Build_Function (FinSetoid n) (FinSetoid (S n)) (InjectInFinSetoid n)).
intros.
simpl.
destruct a. destruct b. simpl in *. assumption.
Defined.

Lemma InjectionFinSetoidIsInjection {n : nat}:
  IsInjection (@InjectionFinSetoid n).
unfold IsInjection.
intros. destruct a. destruct b. simpl in *. assumption.
Defined.

Lemma InjectionFinSetoidMax {n : nat}:
  forall x : |FinSetoid n|,
  (LessThan (FinSetoidToNat (@InjectionFinSetoid n ` x)) n).
intros. destruct x. simpl in *. assumption.
Defined.


Definition ShrinkPropertyDomainUnderlying (n : nat) (P : |FinSetoid (S n)| -> Type):
  (|FinSetoid n| -> Type).
simpl in *.
intros. apply P.
destruct H. apply LessThanOrEqualSucc in l.
exists x. assumption.
Defined.

Definition ShrinkPropertyDomain {n : nat}:
  Property (FinSetoid (S n)) -> Property (FinSetoid n).
intro P. destruct P as [P Pext].
apply (Build_Property (FinSetoid n) (ShrinkPropertyDomainUnderlying n P)).
intros.
specialize (Pext (InjectionFinSetoid ` a)).
specialize (Pext (InjectionFinSetoid ` b)).
apply Pext.
apply (Function_MapIsExtensional _ _ InjectionFinSetoid). assumption.
assumption.
Defined.

Definition DecidableProperty {A : Setoid} (P : Property A) :=
  forall a, Decidable (Property_Prop _ P a).

Lemma ShrinkingPreservesDecidability {n : nat}
  (P : Property (FinSetoid (S n)))
  (q : DecidableProperty P):
  DecidableProperty (ShrinkPropertyDomain P).
  unfold DecidableProperty in *.
  intros.
  specialize (q (InjectionFinSetoid ` a)).
  destruct q.
  - left. destruct P as [P Pext]. simpl in *. assumption.
  - right. intros. apply e. destruct P as [P Pext]. simpl in *. assumption.
Defined.

Lemma FinSetPropertyAdd { n : nat }
  (P : Property (FinSetoid (S n)))
  (p : forall x, Property_Prop _ (ShrinkPropertyDomain P) x)
  (q : Property_Prop _ P (NatToFinSetoid n (LessThanOrEqualRefl (S n)))):
  forall x, Property_Prop _ P x.
intros.
destruct x. simpl in p0. simpl.
unfold LessThan in p0.
assert ((LessThan (S x) (S n)) + ((S x) == (S n))).
apply DeconstructLessThanOrEqual. assumption.
destruct H.
- apply LessThanOrEqualPreservedBySucc in l.
  specialize (p (existT _ x l)). simpl in p.
  destruct P as [P Pext].
  simpl in p. simpl. 
  apply (Pext (InjectionFinSetoid ` (existT _ x l)) (existT _ x p0)).
  simpl. reflexivity.
  simpl. assumption.
- apply NatSucc in i.
  destruct P as [P Pext].
  simpl in q. simpl.
  apply (Pext (NatToFinSetoid n (LessThanOrEqualRefl (S n))) (existT _ x p0)).
  simpl. auto.
  assumption.
Defined.


Lemma FinSetPropForallDecidable
  { n : nat}
  (P : Property (FinSetoid n))
  (p : DecidableProperty P):
  Decidable (forall y: | FinSetoid n |, Property_Prop _ P y).
induction n.
- destruct P as [P Pext].
  assert (not | FinSetoid 0 |).
  intros. simpl in H. destruct H. apply LessThanZeroFalse in l. assumption. 
  left. intros. contradiction.
- specialize (IHn (ShrinkPropertyDomain P) (ShrinkingPreservesDecidability P p)).
  destruct IHn.
  + unfold DecidableProperty in p.
    specialize (p (NatToFinSetoid n (LessThanOrEqualRefl (S n)))).
    destruct p.
    * left. apply FinSetPropertyAdd; assumption.
    * right. intro. apply e. apply X.
  + right. intro. apply e. intros.
    specialize (X ( InjectionFinSetoid ` y)).
    destruct P as [P Pext].
    simpl in X. simpl. assumption.
Defined.


Lemma FinSetPropSigmaDecidable
  { n : nat}
  (P : Property (FinSetoid n))
  (p : DecidableProperty P):
  Decidable (sigma y: | FinSetoid n |, Property_Prop _ P y).
induction n.
- destruct P as [P Pext].
  assert (not | FinSetoid 0 |).
  intros. simpl in H. destruct H. apply LessThanZeroFalse in l. assumption.
  right. intros. apply H. destruct X. assumption.
- specialize (IHn (ShrinkPropertyDomain P) (ShrinkingPreservesDecidability P p)).
  destruct IHn.
  + destruct s. left.
    exists (InjectionFinSetoid ` x).
    destruct P as [P Pext]. simpl. simpl in p0. assumption.
  + unfold DecidableProperty in p.
    destruct (p (NatToFinSetoid n (LessThanOrEqualRefl _))).
    * left. exists (NatToFinSetoid n (LessThanOrEqualRefl _)). assumption.
    * right.
      intros.
      destruct X. destruct x. simpl in p1. simpl in p0.
      assert ((LessThan (S x) (S n)) + (S x == S n)).
      apply DeconstructLessThanOrEqual. apply p1.
      destruct H. {
        unfold LessThan in l.
        apply LessThanOrEqualPreservedBySucc in l.
        apply e.
        exists (existT _ x l). simpl.
        destruct P as [P Pext]. simpl in *.
        apply (Pext (existT _ x p1) (InjectionFinSetoid ` (existT _ x l))).
        simpl. reflexivity. assumption.
      } {
        apply e0.
        destruct P as [P Pext]. simpl in *.
        apply (Pext (existT (fun x : nat => LessThan x (S n)) x p1) (NatToFinSetoid n (LessThanOrEqualRefl (S n)))).
        simpl. apply NatSucc. assumption. assumption.
      }
Defined.


Lemma FiniteSubsetMembershipDecidable {A : Setoid}
  (q : IsSetoidDiscrete A)
  (U : Subset A) (p : IsSubsetFinite U) :
  IsSubsetDecidable U.
unfold IsSubsetDecidable.
unfold IsSubsetFinite in p. unfold IsSetoidFinite in p. destruct p.
destruct s as [f fbij].

assert ((forall a: |A|, 
  Decidable (sigma x: |FinSetoid x|, 
      Subset_Injection A U ` ((BijectionInversion f fbij) ` x) ==[A] a)) ->
  (forall a : | A |, Decidable (a ::[ A] U))
  ).
intros.
unfold IsMemberOfSubset.
specialize (X a).
unfold Decidable in X. unfold Decidable. destruct X. destruct s.
- left. exists (BijectionInversion f fbij ` x0). assumption.
- right. intros. apply e. destruct X.
  exists (f ` x0).
  apply (FunctionCong x0 (BijectionInversion f fbij ` (f ` x0))).
  setoid_symm (Subset_Setoid A U).
  apply BijectionInversionLeftCancelable. assumption.
- apply X. intros. 

refine (let P := _ : Property (FinSetoid x) in _).
Unshelve. Focus 2.
apply (Build_Property _ 
  (fun x => Subset_Injection A U ` (BijectionInversion f fbij ` x) ==[ A] a)).
intros.
apply (FunctionCong (BijectionInversion f fbij ` a0) (BijectionInversion f fbij ` b)).
apply (Function_MapIsExtensional _ _ (BijectionInversion _ _)); assumption.
assumption.

assert (DecidableProperty P) as Pdec.
unfold DecidableProperty.
intros. unfold IsSetoidDiscrete in q.
simpl.
apply q.

apply (FinSetPropSigmaDecidable P Pdec).
Defined.




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


Definition SubsetAdd {A : Setoid}
  (S : Subset A) (a : |A|) : Subset A.
apply SubsetComprehension.
apply (Build_Property _ (fun x => sum (x ::[A] S) (x ==[A] a))).
intros. destruct X0.
- left. apply (SubsetIsMemberOfTransport _ a0 b); assumption.
- right. setoid_tran A a0. setoid_symm A; assumption. assumption.
Defined.

Lemma SubsetAddIdem
  { A : Setoid } (S : Subset A) (a : |A|) (p : a ::[A] S):
  IsSubsetEquiv S (SubsetAdd S a).
unfold IsSubsetEquiv. unfold IsSubsetOf. split.
- intros. simpl.
  apply BetaSubsetMembership. simpl. left. assumption.
- intros. apply BetaSubsetMembership in X. simpl in X.
  destruct X. assumption.
  apply (SubsetIsMemberOfTransport _ a a0).
  setoid_symm A; assumption. assumption.
Defined.

Lemma SubsetAddCharecterisation
  { A : Setoid } (S : Subset A) (a : |A|):
  forall b, b ::[A] SubsetAdd S a <--> (b ::[A] S) + (b ==[A] a).
split.
- intros. apply BetaSubsetMembership in X. simpl in X. assumption.
- intros. apply BetaSubsetMembership. simpl. assumption.
Defined.


Definition PreInclusion
  { A : Setoid } (S : Subset A) (a : |A|) (p : a ::[A] S)
  (x : |Subset_Setoid A S|) : |Subset_Setoid A (SubsetAdd S a)|.
simpl.
exists (Subset_Injection A S ` x).
left. unfold IsMemberOfSubset.
exists x. setoid_refl A.
Defined.


Definition Inclusion
  { A : Setoid } (S : Subset A) (a : |A|) (p : a ::[A] S):
  |Subset_Setoid A S ==> Subset_Setoid A (SubsetAdd S a)|.
apply (Build_Function _ _ (PreInclusion S a p)).
intros.
simpl. apply (Function_MapIsExtensional _ _ (Subset_Injection _ _)).
assumption.
Defined.

Lemma InclusionBijection
  { A : Setoid } (S : Subset A) (a : |A|) (p : a ::[A] S):
  IsBijection (Inclusion S a p).
split.
- unfold IsInjection. intros. simpl in X.
  apply (Subset_InjectionIsInjection _ _). assumption.
- unfold IsSurjection. intros. simpl.
  destruct b as [b]. simpl in p0. simpl.
  destruct p0.
  * assumption.
  * destruct p. exists x. setoid_tran A a. assumption. setoid_symm A. assumption.
Defined.


Definition PreExtendBijection
  {A : Setoid}
  (U : Subset A)
  (n : nat)
  (f : | Subset_Setoid A U ==> FinSetoid n |)
  (fbij : IsBijection f)
  (a : |A|)
  (np : not a ::[ A] U):
  |Subset_Setoid A (SubsetAdd U a)| -> |FinSetoid (S n)|. 
intro x.
destruct x. simpl in p. destruct p.
- destruct i. apply (InjectionFinSetoid ` (f ` x0)).
- apply (NatToFinSetoid n). apply LessThanOrEqualRefl.
Defined.


Definition ExtendBijection
  {A : Setoid}
  (U : Subset A)
  (n : nat)
  (f : | Subset_Setoid A U ==> FinSetoid n |)
  (fbij : IsBijection f)
  (a : |A|)
  (np : not a ::[ A] U):
  |Subset_Setoid A (SubsetAdd U a) ==> FinSetoid (S n)|.
apply (Build_Function _ _ (PreExtendBijection U n f fbij a np)).
destruct a0. destruct b. simpl in *. destruct p.
- intros. destruct p0.
  * destruct i. destruct i0. 
    assert (f ` x1 ==[ FinSetoid n] f ` x2).
    apply (Function_MapIsExtensional _ _ f).
    assert (Subset_Injection A U ` x1  ==[ A] x0).
      setoid_tran A x. assumption. assumption.
    apply (Subset_InjectionIsInjection).
      setoid_tran A x0. assumption. setoid_symm A. assumption.
    assert (InjectInFinSetoid n (f ` x1) ==[FinSetoid (S n)]
            InjectInFinSetoid n (f ` x2)).
    apply (Function_MapIsExtensional _ _ (InjectionFinSetoid)). assumption.
    simpl in X1. assumption.
  * assert (a ::[A] U).
    apply (SubsetIsMemberOfTransport _ x a).
    setoid_tran A x0. assumption. assumption. assumption.
    contradiction.
- intros. destruct p0.
  * assert (a ::[A] U). apply (SubsetIsMemberOfTransport _ x0 a).
    setoid_tran A x. setoid_symm A. assumption. assumption. assumption.
    contradiction.
  * simpl. reflexivity.
Defined.

Lemma ExtendBijectionIsBijection
  {A : Setoid}
  (U : Subset A)
  (n : nat)
  (f : | Subset_Setoid A U ==> FinSetoid n |)
  (fbij : IsBijection f)
  (a : |A|)
  (np : not a ::[ A] U):
  IsBijection (ExtendBijection U n f fbij a np).
split.
- unfold IsInjection. intros.
  destruct a0. destruct b. simpl in *.
  destruct p.
  * destruct p0.
    + destruct i. destruct i0.
      assert (InjectInFinSetoid n (f ` x1) ==[FinSetoid (S n)]
              InjectInFinSetoid n (f ` x2)). assumption.
      apply InjectionFinSetoidIsInjection in X0.
      apply (fst fbij) in X0. (* f is injection *)
      assert (Subset_Injection A U ` x1 ==[A] Subset_Injection A U ` x2).
      apply (Function_MapIsExtensional _ _). assumption.
      setoid_tran A (Subset_Injection A U ` x1).
      setoid_symm A. assumption.
      setoid_tran A (Subset_Injection A U ` x2).
      assumption. assumption.
    + destruct i.
      assert (InjectInFinSetoid n (f ` x1) ==[FinSetoid (S n)] NatToFinSetoid n (LessThanOrEqualRefl (S n))).
      assumption.
      assert (forall x, LessThan (FinSetoidToNat (InjectInFinSetoid n (f ` x))) n).
      intros. apply InjectionFinSetoidMax.
      specialize (X1 x1).
      assert ((FinSetoidToNat (InjectInFinSetoid n (f ` x1))) == n).
      assumption.
      rewrite H in X1.
      apply LessThanIrreflexive in X1. contradiction.
  * destruct p0.
    + destruct i. 
      assert (InjectInFinSetoid n (f ` x1) ==[FinSetoid (S n)] NatToFinSetoid n (LessThanOrEqualRefl (S n))).
      setoid_symm (FinSetoid (S n)). assumption.
      assert (LessThan (FinSetoidToNat (InjectInFinSetoid n (f ` x1))) n).
      apply InjectionFinSetoidMax.
      assert ((FinSetoidToNat (InjectInFinSetoid n (f ` x1))) == n).
      assumption.
      rewrite H0 in H.
      apply LessThanIrreflexive in H. contradiction.
    + setoid_tran A a. assumption. setoid_symm A. assumption.
- unfold IsSurjection.
  intros. destruct b. simpl in *.
  apply DeconstructLessThanOrEqual in p.
  destruct p.
  + apply LessThanOrEqualPreservedBySucc in l.
    pose (Subset_Injection A U ` ((BijectionInversion f fbij) ` (NatToFinSetoid x l))).
    assert (s ::[A] U).
    unfold IsMemberOfSubset.
    exists (BijectionInversion f fbij ` NatToFinSetoid x l).
    setoid_refl A.

    exists (existT _ s (inl _ X)).
    simpl.
    destruct X.
    apply Subset_InjectionIsInjection in s0.
    assert (f ` x0 ==[FinSetoid n] NatToFinSetoid x l).
    apply (FunctionCong (BijectionInversion f fbij ` NatToFinSetoid x l) x0).
    setoid_symm (Subset_Setoid A U) . assumption.
    apply BijectionInversionRightCancelable.

    assert (LessThan x (S n)). unfold LessThan. apply LessThanOrEqualSucc. assumption.
    assert (InjectInFinSetoid n (f ` x0) ==[FinSetoid (S n)] NatToFinSetoid x H).

    apply (FunctionCong 
       (NatToFinSetoid x l) 
        (f ` x0)
      _
      InjectionFinSetoid
    ).
    setoid_symm (FinSetoid n); assumption.
    simpl. reflexivity.

    assumption.
  + assert (a ==[A] a). setoid_refl A.
    exists (existT _ a (inr _ X)).
    simpl. apply NatSucc. symmetry. assumption.
Defined.


Lemma FiniteSubsetAddIsFinite { A : Setoid }
  (q : IsSetoidDiscrete A)
  (S : Subset A) (p : IsSubsetFinite S) (a : |A|):
  IsSubsetFinite (SubsetAdd S a).
unfold IsSubsetFinite in *.
unfold IsSetoidFinite in *.
destruct (FiniteSubsetMembershipDecidable q S p a).
- destruct p.
  exists x. destruct s.
  exists ((BijectionInversion (Inclusion S a i) (InclusionBijection S a i)) |> x0).
  apply FunctionBijectionCompositionIsBijection.
  * apply BijectionInversionIsBijection.
  * assumption.
- (* Define a bijection that assigns and index to the new element 'a'. *)
  destruct p. destruct s.
  exists (Datatypes.S x).
  exists (ExtendBijection S x x0 i a e).
  apply (ExtendBijectionIsBijection).
Defined.


Lemma LessThanOrEqualExists:
  forall n, sigma m, LessThanOrEqual m n.
intros. exists n. apply LessThanOrEqualRefl.
Defined.

Lemma LessThanExists:
  forall n, (sigma m, LessThan m n) + (n == 0).
induction n.
- right. reflexivity.
- left. exists n. apply LessThanOrEqualRefl.
Defined.



Lemma LargestNumberLessThan:
  forall n, (sigma x, (LessThan x n)) + (n == 0).
intros. destruct n.
- right. reflexivity.
- left. exists n. apply LessThanOrEqualRefl.
Defined.


Lemma FunctionIdentityIsInjection {A : Setoid}:
  IsInjection (@FunctionIdentity A).
intros a b. simpl. intuition.
Defined.


Definition IterateSubsetAdd { A : Setoid}
  (S U : Subset A) (n : nat) (x : nat) (p : LessThan x n)
  (f : | FinSetoid n ==> Subset_Setoid A U |): Subset A.
induction x.
  + apply S.
  + assert (LessThan x n). apply LessThanOrEqualSubstract in p. assumption.
    apply (SubsetAdd (IHx H) (Subset_Injection A U ` (f ` (NatToFinSetoid x H)))).
Defined.

Definition SubsetAddLeftInclusion {A : Setoid}
  (U: Subset A) (a : |A|):
  sigma f: |Subset_Setoid A U ==> Subset_Setoid A (SubsetAdd U a)|,
  IsInjection f &
  Subset_Injection A U ==[_] f |> Subset_Injection A (SubsetAdd U a).
(* Construct inclusion and prove extensionality *)
refine (let f := _ : (|Subset_Setoid A U| -> |Subset_Setoid A (SubsetAdd U a)|) in _).
Unshelve. Focus 2.
intros. simpl.
exists (Subset_Injection A U ` X).
left. unfold IsMemberOfSubset.
exists X.
setoid_refl A.
refine (let g := _ : (|Subset_Setoid A U ==> Subset_Setoid A (SubsetAdd U a)|) in _).
Unshelve. Focus 2.
apply (Build_Function (Subset_Setoid A U) (Subset_Setoid A (SubsetAdd U a)) f).
intros. simpl.
apply (Function_MapIsExtensional _ _).
assumption.
(* Injection and factoring *)
exists g. split.
- unfold IsInjection. intros. simpl in X.
  apply (Subset_InjectionIsInjection A U). assumption.
- simpl. unfold FunctionEquivalence. intros.
  simpl. setoid_refl A.
Defined.


Definition IterateSubsetAddLeftInclusion {A : Setoid}
  (S U : Subset A) (n : nat) (x : nat) (p : LessThan x n)
  (i : | FinSetoid n ==> Subset_Setoid A U |):
  sigma f: |Subset_Setoid A S ==> Subset_Setoid A (IterateSubsetAdd S U n x p i)|,
  IsInjection f &
  Subset_Injection A S ==[_] f |> Subset_Injection A (IterateSubsetAdd S U n x p i).
induction x.
- simpl. exists FunctionIdentity. split.
  + apply FunctionIdentityIsInjection.
  + unfold FunctionEquivalence. simpl. intros. setoid_refl A.
- specialize (IHx (LessThanOrEqualSubstract ((Datatypes.S x)) n p)).
  destruct IHx as [g g'].
  destruct g' as [ ginj gfact].
  exists (g |> projT1 (SubsetAddLeftInclusion 
                  (IterateSubsetAdd S U n x (LessThanOrEqualSubstract ((Datatypes.S x)) n p) i)
                  (Subset_Injection A U  ` (i ` (NatToFinSetoid x (LessThanOrEqualSubstract ((Datatypes.S x)) n p)))))).
  split.
  + apply FunctionInjectionCompositionIsInjection.
    assumption.
    destruct SubsetAddLeftInclusion. intuition.
  + assumption.
Defined.

Definition SubsetAddAll { A : Setoid}
  (S U : Subset A) (p: IsSubsetFinite U): Subset A.
unfold IsSubsetFinite in p. unfold IsSetoidFinite in p.
destruct p. destruct s.
destruct (LargestNumberLessThan x).
- destruct s. apply (IterateSubsetAdd S U x x1 l).
  apply (BijectionInversion x0 i).
- apply S.
Defined.

Definition SubsetAddAllLeftInclusion {A : Setoid}
  (S U : Subset A) (p: IsSubsetFinite U):
  sigma f : |Subset_Setoid A S ==> Subset_Setoid A (SubsetAddAll S U p)|,
  IsInjection f &
  Subset_Injection A S ==[_] f |> Subset_Injection A (SubsetAddAll S U p).
unfold IsSubsetFinite in p. unfold IsSetoidFinite in p.
destruct p. destruct s. simpl.
destruct (LargestNumberLessThan x).
- destruct s. apply IterateSubsetAddLeftInclusion.
- exists (FunctionIdentity). split. 
  + apply FunctionIdentityIsInjection.
  + unfold FunctionEquivalence. intros. simpl. setoid_refl A.
Defined.

Lemma SubsetAddAllIsSubsetOf {A : Setoid}
  (S U: Subset A) (p: IsSubsetFinite U)
  (a : |A|): IsSubsetOf S (SubsetAddAll S U p).
apply InjectionToIsSubsetOf.
apply SubsetAddAllLeftInclusion.
Defined.

(*
Definition PreNumberOfSharedElements
  (q : IsSetoidDiscrete A)
  (S U : Subset A) 
  (n : nat) (f : |FinSetoid n ==> Subset_Setoid A S|)
  (m : nat) (g : |FinSetoid m ==> Subset_Setoid A U|)
  (x : nat): nat :=
match 

Lemma Enum {A : Setoid}
  (q : IsSetoidDiscrete A)
  (S U : Subset A) 
  (n : nat) (f : |FinSetoid n ==> Subset_Setoid A S|)
  (m : nat) (g : |FinSetoid m ==> Subset_Setoid A U|):
  sigma j, |FinSetoid j ==> Subset_Setoid A (SubsetUnion S U)|.

*)







