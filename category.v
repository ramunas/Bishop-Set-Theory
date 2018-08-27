Load "/Users/ramunas/Desktop/SetTheory/setoid.v".
(* Add LoadPath "/Users/ramunas/Desktop/SetTheory/". *)


Record Category := {
  Category_Objects: Type;

  Category_Arrows (A B : Category_Objects) : Setoid;
  Category_Id {A : Category_Objects} : |Category_Arrows A A|;
  Category_Compose {A B C: Category_Objects}:
    |Category_Arrows B C| -> |Category_Arrows A B| -> |Category_Arrows A C|;

  Category_IdLeft:
    forall A B: Category_Objects, forall f : |Category_Arrows B A|,
    Category_Compose Category_Id f ==[Category_Arrows B A] f;
  Category_IdRight:
    forall A B: Category_Objects, forall f : |Category_Arrows A B|,
    Category_Compose f Category_Id ==[Category_Arrows A B] f;

  Category_ComposeIsAssociative:
    forall A B C D: Category_Objects,
    forall h : |Category_Arrows A B|,
    forall g : |Category_Arrows B C|,
    forall f : |Category_Arrows C D|,
    Category_Compose f (Category_Compose g h) ==[Category_Arrows A D]
    Category_Compose (Category_Compose f g) h;
}.

Record Functor (C D: Category) := {
  Functor_ObjectsMap : C.(Category_Objects) -> D.(Category_Objects);
  Functor_ArrowsMap {A B : C.(Category_Objects)}: 
      |C.(Category_Arrows) A B ==> 
      D.(Category_Arrows) (Functor_ObjectsMap A) (Functor_ObjectsMap B)|;

  Functor_PreservesIdentity:
    forall A : C.(Category_Objects),
    D.(Category_Id) ==[Category_Arrows D (Functor_ObjectsMap A) (Functor_ObjectsMap A)] 
    Functor_ArrowsMap ` (C.(Category_Id));

  Functor_PreservesComposition:
    forall X Y Z: C.(Category_Objects),
    forall f : |Category_Arrows C Y Z|,
    forall g : |Category_Arrows C X Y|,
    Functor_ArrowsMap ` (C.(Category_Compose) f g) ==[Category_Arrows D (Functor_ObjectsMap X) (Functor_ObjectsMap Z)]
    D.(Category_Compose) (Functor_ArrowsMap ` f) (Functor_ArrowsMap ` g)
}.


Definition CategorySetoid: Category.
apply (Build_Category Setoid FunctionSetoid (@IdFunction) (@FunctionCompose)).
- intros. simpl. unfold FunctionEquivalence. simpl. intros. setoid_refl A.
- intros. simpl. unfold FunctionEquivalence. simpl. intros. setoid_refl B.
- intros. simpl. unfold FunctionEquivalence. intros. simpl. setoid_refl D.
Defined.













