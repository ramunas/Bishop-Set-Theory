
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

Definition unique_for_setoid (A: Setoid) (P : |A| -> Prop) (x: |A|): Prop :=
  P x /\ forall a: |A|, P a -> a ==[A] x.

Notation "'exists_in' [ A ] ! x , P" :=
  (ex (unique_for_setoid A (fun x => P))) (at level 60).


Definition PropSetoidOf (A : Type): Setoid.
apply (Build_Setoid A (@eq A) PropositionalEqualityIsEquivalence).
Defined.

Record Prod (A : Type) (B : Type) := {
  fst : A;
  snd : B;
}.

Definition mkPair {A B: Type} (a: A) (b: B) := {| fst := a; snd := b |}.

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


Notation "A # B" := (ProdSetoid A B) (at level 67, right associativity).


Record Function (A : Setoid) (B : Setoid) := {
  Function_Map : |A| -> |B|;
  Function_MapIsExtensional: 
    forall a b : |A|, a ==[A] b -> Function_Map a ==[B] Function_Map b;
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
  (fun x => (Function_Map A B (fst _ _ x)) (snd _ _ x) )).
intros.
simpl.
destruct a. destruct b.  simpl in H. destruct H.
simpl.
unfold FunctionEquivalence in H.
specialize (H snd1).
apply (FunctionCong snd1 snd0 (fst1 ` snd1)).
setoid_symm A; assumption.
assumption.
Defined.


Definition PreFunctionCurry {A B C : Setoid}
  (a : |A|)
  (f : | ProdSetoid A B ==> C |):
  |B ==> C|.
apply (Build_Function B C (fun b => f ` (mkPair a b))).
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
  FunctionEval ` (mkPair (h ` a) b) ==[C] f ` (mkPair a b).
exists (FunctionCurry f). unfold unique_for_setoid. split.
- intros. simpl. setoid_refl C.
- intros. simpl. unfold FunctionEquivalence. intros. simpl. 
unfold FunctionEquivalence. intros. simpl.
specialize (H a0 a1).
simpl in H. assumption.
Qed.

Definition FunctionUnCurry {A B C : Setoid}
  (f : |A ==> B ==> C|) : |ProdSetoid A B ==> C|.
apply (Build_Function (ProdSetoid A B) C
  (fun x => f ` (fst _ _ x) ` (snd _ _ x))).
intros.
destruct a. destruct b. simpl in H. destruct H.
simpl.
apply (FunctionCong snd1 snd0 ).
setoid_symm B. assumption.
destruct f as [map ext].
simpl. apply ext. assumption.
Defined.

Lemma FunctionUnCurrying {A B C: Setoid}
  (f : |A ==> (B ==> C)|) : 
  exists_in [ ProdSetoid A B ==> C ] ! h,
  forall (a : |A|) (b : |B|),
  FunctionEval ` (mkPair (f ` a) b) ==[C] h ` (mkPair a b).
exists (FunctionUnCurry f).
unfold unique_for_setoid. split.
- intros. simpl. setoid_refl C.
- simpl. intros. unfold FunctionEquivalence. intros. simpl.
  destruct a0. simpl.
  specialize (H fst0 snd0).
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
apply (Build_Function (ProdSetoid A B) A (fun x => fst _ _ x)).
intros. destruct a. destruct b.
simpl. simpl in H. intuition.
Defined.

Definition ProdSetoidPr2 {A B : Setoid}: |ProdSetoid A B ==> B|.
apply (Build_Function (ProdSetoid A B) B (fun x => snd _ _ x)).
intros. destruct a. destruct b.
simpl. simpl in H. intuition.
Defined.

Lemma ProdSetoidIsProduct {A B: Setoid} (a : |A|) (b : |B|): 
  ProdSetoidPr1 ` (ProdSetoidMkPair ` a ` b) ==[A] a /\
  ProdSetoidPr2 ` (ProdSetoidMkPair ` a ` b) ==[B] b.
simpl. split. setoid_refl A. setoid_refl B.
Qed.

Definition Pairing {P A B : Setoid} (p1 : |P ==> A|) (p2: |P ==> B|): 
  |P ==> (A # B)|.
apply (Build_Function P (A # B) (fun p => mkPair (p1 ` p) (p2 ` p))).
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
  Pairing p1 p2 |> ProdSetoidPr1 ==[P ==> A] p1 /\
  Pairing p1 p2 |> ProdSetoidPr2 ==[P ==> B] p2.
split.
- simpl. unfold FunctionEquivalence. intros. simpl. setoid_refl A.
- simpl. unfold FunctionEquivalence. intros. simpl. setoid_refl B.
Qed.


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


Definition SumSetoidInl {A B : Setoid} : |A ==> SumSetoid A B|.
apply (Build_Function A ( SumSetoid A B) (fun x => inl _ _ x)).
intros. simpl. assumption.
Defined.

Definition SumSetoidInr {A B : Setoid} : |B ==> SumSetoid A B|.
apply (Build_Function B ( SumSetoid A B) (fun x => inr _ _ x)).
intros. simpl. assumption.
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


Definition IsInjection {A B : Setoid} (f : |A ==> B|) : Prop :=
  forall a b : |A|, f` a ==[B] f` b -> a ==[A] b.

Lemma FunctionInjectionCompositionIsInjection
  {A B C: Setoid}
  (f : |A ==> B|) (g : |B ==> C|) 
  (p : IsInjection f) (q: IsInjection g): IsInjection (f |> g).
unfold IsInjection in *.
simpl.
intros.
specialize (q (f ` a) (f ` b) H).
intuition.
Qed.

Definition IsSurjection {A B : Setoid} (f : |A ==> B|) : Prop :=
  forall b: |B|, exists a: |A|, f ` a ==[B] b.


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


Definition IsBijection {A B : Setoid} (f : |A ==> B|) : Prop :=
  IsInjection f /\ IsSurjection f.

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


Definition IsMono {A B : Setoid} (f : |A ==> B|) : Prop :=
  forall C : Setoid, forall g h: |C ==> A|, g |> f  ==[C ==> B] h |> f -> g ==[C ==> A] h.

Definition IsEpi {A B : Setoid} (f : |A ==> B|) : Prop :=
  forall C : Setoid, forall g h: |B ==> C|, f |> g ==[A ==> C] f |> h -> g ==[B ==> C] h.

Definition IsIso {A B : Setoid} (f : |A ==> B|) : Prop :=
  exists g : |B ==> A|, f |> g ==[A ==> A] IdFunction /\ g |> f ==[B ==> B] IdFunction.

Inductive Unit: Type := Star.

Definition UnitSetoid : Setoid.
  apply (Build_Setoid Unit (fun _ _ => True)).
  apply Build_IsEquivalence; auto.
Defined.

Definition Unit_function {A : Setoid} : |A ==> UnitSetoid|.
apply (Build_Function A UnitSetoid (fun x => Star)). intros. setoid_refl UnitSetoid.
Defined.

Lemma Unit_function_is_unique:
  forall B : Setoid,
    forall g: |B ==> UnitSetoid|, Unit_function ==[B ==> UnitSetoid] g.
intros. simpl. unfold FunctionEquivalence.
intros. simpl. trivial.
Defined.



Lemma MonoInjective {A B : Setoid}:
  forall f : |A ==> B|,
  IsMono f <-> IsInjection f.
intros. split.
- unfold IsMono. unfold IsInjection.
  intros. specialize (H UnitSetoid (ConstFunction a) (ConstFunction b)).
  simpl in H. unfold FunctionEquivalence in H. simpl in H.
  intuition.
- unfold IsMono. unfold IsInjection.
  intros. simpl. unfold FunctionEquivalence; simpl. intros.
  specialize (H (g ` a) (h ` a)).
  simpl in H0.  unfold FunctionEquivalence in H0; simpl.
  specialize (H0 a). intuition.
Qed.


Definition HasRightInverse {A B : Setoid} (f : |A ==> B|) : Prop :=
  exists g : |B ==> A|, g |> f ==[B ==> B] IdFunction.

Lemma HasRightInverseIsSurjection {A B : Setoid}: 
  forall f : |A ==> B|,
  HasRightInverse f -> IsSurjection f.
intros. 
 unfold HasRightInverse. unfold IsSurjection.
  intros. destruct H as [g].
  simpl in H. unfold FunctionEquivalence in H.
  exists (g ` b). apply H.
Qed.


Definition IsChoiceSetoid (S : Setoid) : Prop :=
  forall X : Setoid, forall f : |X ==> S|,
    IsSurjection f -> HasRightInverse f.



Record Subset (A: Setoid) := {
  Subset_Setoid: Setoid ;
  Subset_Injection: |Subset_Setoid ==> A|;
  Subset_InjectionIsInjection: IsInjection Subset_Injection
}.



Definition IsMemberOfSubset {A : Setoid} (a : |A|) (S: Subset A) : Prop :=
  exists x : |Subset_Setoid _ S|, ((Subset_Injection _ S)` x) ==[A] a.

Notation "a ::[ A ] S" := (@IsMemberOfSubset A a S) (at level 66, no associativity).

Definition IsSubsetOf {A : Setoid} (X Y : Subset A) : Prop :=
  forall a : |A|, a ::[A] X -> a ::[A] Y.

Definition IsSubsetEquiv {A : Setoid} (X Y : Subset A): Prop :=
  IsSubsetOf X Y /\ IsSubsetOf Y X.


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
intros. simpl in H. apply H.
Defined.

Definition FunctionImage {A B : Setoid} (f : |A ==> B|): Subset B.
apply (Build_Subset B (FunctionImageSetoid f) (FunctionImageFunction f)).
unfold IsInjection.
intros. simpl in *. assumption.
Defined.




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

Definition SigmaSetoid_pr1 {X : Setoid} {P : Property X}: |SigmaSetoid X P ==> X|.
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

Definition Singleton {A : Setoid} (a : |A|) : Subset A.
assert (Property A).
apply (Build_Property A (fun x => a ==[A] x)).
intros. setoid_tran A a0; assumption.
apply (SubsetComprehension A X).
Defined.

Definition IsSingleton {A : Setoid} (S : Subset A) : Prop :=
  forall a b: |A|, a ::[A] S -> b ::[A] S -> a ==[A] b.

Lemma SingletonIsSingleton {A : Setoid} (a : |A|) : IsSingleton (Singleton a).
unfold IsSingleton.
intros.
apply BetaSubsetMembership in H.
apply BetaSubsetMembership in H0. simpl in *.
setoid_tran A a.
setoid_symm A; assumption.
assumption.
Qed.

Lemma SingletonHasOneMember {A : Setoid}: 
  forall a b: |A|, b ::[A] (Singleton a) -> a ==[A] b.
intros. apply BetaSubsetMembership in H. simpl in H. assumption.
Qed.


Definition FunctionInverseImage {A B : Setoid} (S : Subset B) (f : |A ==> B|) : Subset A.
apply (SubsetComprehension A).
apply (Build_Property A (fun a => (f ` a) ::[B] S)).
intros.
destruct H0.
exists x.
setoid_symm B.
apply (FunctionCong a b). assumption.
setoid_symm B.
assumption.
Defined.


Lemma BijectionInversion {A B : Setoid} 
  (f : |A ==> B|) (p: IsBijection f) (y : |B|):
  exists x : |A|, f ` x ==[B] y /\
  forall z : |A|, f ` z ==[B] y -> x ==[A] z.
destruct p.
unfold IsSurjection in H0.
specialize (H0 y).
destruct H0.
exists x.
split.
assumption.
intros.
assert (f ` x ==[B] f ` z).
setoid_tran B y. assumption. setoid_symm B. assumption.
apply H. assumption.
Qed.
(*
Print BijectionInversion.

Print ex.

(* Definition ExistsPr1 (T : Type) (p : exists x : T, P *)

TODO: bijection inversion. The challenge in defining such a function is
that the impredicative Prop does not allow transfering values to Type.


Definition BijInv {A B : Setoid} 
  (f : |A ==> B|) (p: IsBijection f) : | B ==> A|.
apply (Build_Function B A 
  (fun b => match (BijectionInversion f p b) with
            | ex_intro _ _ x _ => x
            end)).

Lemma BijectionIsoCorrespondence 
  {A B : Setoid} (f : |A ==> B|) : IsBijection f <-> IsIso f.
unfold IsBijection. unfold IsIso. split.
- unfold IsInjection. unfold IsSurjection. intros. destruct H.


Lemma ReverseImage

Lemma SingletonSubsetEquivalentToSingleton {A : Setoid} (S : Subset A) (p: IsSingleton S):
  exists a : |A|, IsSubsetEquiv S (Singleton a).
unfold IsSingleton in p.
unfold IsSubsetEquiv.
unfold IsSubsetOf. red in p.
destruct S. simpl in *.

*)


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
simpl in H.
apply q.
assumption.
Defined.


Lemma QuotientFactors {A B : Setoid} 
  (R: Relation A A) (p : IsEquivalenceRelation R) (f : |A ==> B|)
  (q : forall a b : |A|, R.(Relation_Rel A A) a b -> f`a ==[B] f`b):
  exists h : |QuotientSetoid A R p ==> B|,
  forall x : |A|,
  h ` (Quotient A R p ` x) ==[B] f ` x.
exists (LiftFunctionToQuotient f q). simpl. intros.
setoid_refl B.
Qed.


Definition NatSetoid : Setoid := PropSetoidOf nat.


Definition FinOrdSubset (n : nat) : Subset NatSetoid.
apply (SubsetComprehension ).
apply (Build_Property NatSetoid (fun x => x < n)).
intros. simpl in H. rewrite <- H. assumption.
Defined.

Definition FinSetoid (n : nat): Setoid := Subset_Setoid NatSetoid (FinOrdSubset n).


Definition IsSetoidFinite (S: Setoid): Prop :=
  exists n : nat, exists f : |S ==> FinSetoid n|,  IsBijection f.

Definition IsSubsetFinite {A : Setoid} (S : Subset A) : Prop :=
  IsSetoidFinite (Subset_Setoid A S).


Definition EnumerateSingletonSubset {A : Setoid} (a : |A|) : 
  | Subset_Setoid A (Singleton a) ==> FinSetoid 1|.
assert (0 < 1) as obvious. auto.
apply (Build_Function (Subset_Setoid A (Singleton a)) (FinSetoid 1)
  (fun x => {| pr1 := 0; pr2 := obvious |})). 
simpl. intros. reflexivity.
Defined.

(* Require Import Omega. *)

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
  assert (Sigma (| A |) (fun x : | A | => a ==[ A] x)) as ael.
  apply (Build_Sigma (|A|) _ a). setoid_refl A.
  exists ael.
  destruct b. simpl in *.
  unfold lt in pr4.
  inversion pr4. reflexivity. inversion H0.
Qed.











