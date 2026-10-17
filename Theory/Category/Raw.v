Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Reserved Infix "~>⁻" (at level 90, right associativity).
Reserved Infix "∘⁻" (at level 40, left associativity).

(*
 nLab: https://ncatlab.org/nlab/show/category
   Wikipedia: https://en.wikipedia.org/wiki/Category_(mathematics)

   本文件给出原始/弱化的范畴数据。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class RawCategory := {
  r_obj : Type;                         (* collection of objects *)

  r_uhom := Type : Type;                (* universe of homs (bare Types) *)
  r_hom : r_obj → r_obj → r_uhom where "a ~>⁻ b" := (r_hom a b);  (* morphisms x ~>⁻ y *)

  r_id {x} : r_hom x x;                 (* identity morphism on x *)
  r_compose {x y z} (f: r_hom y z) (g : r_hom x y) : r_hom x z
    where "f ∘⁻ g" := (r_compose f g);  (* composition f ∘⁻ g *)
}.

Declare Scope raw_category_scope.
Declare Scope raw_object_scope.
Declare Scope raw_morphism_scope.

Bind Scope raw_category_scope with RawCategory.
Bind Scope raw_object_scope with r_obj.

Delimit Scope raw_category_scope with raw_category.
Delimit Scope raw_object_scope with raw_object.
Delimit Scope raw_morphism_scope with raw_morphism.

Notation "x ~>⁻ y" := (@r_hom _%raw_category x%raw_object y%raw_object)
  (at level 90, right associativity) : type_scope.
Notation "f ∘⁻ g" :=
  (@r_compose _%raw_category _%raw_object _%raw_object _%raw_object f%raw_morphism g%raw_morphism)
  : raw_morphism_scope.

Coercion r_obj : RawCategory >-> Sortclass.

(*
   本节说明 Raw 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition From_RawCategory
           (raw : RawCategory)
           {homset} {compose_respects}
           {id_left id_right comp_assoc} : Category :=
  {| obj              := r_obj;
     hom              := r_hom;
     homset           := homset;
     id               := @r_id raw;
     compose          := @r_compose raw;
     compose_respects := compose_respects;
     id_left          := id_left;
     id_right         := id_right;
     comp_assoc       := comp_assoc;
     comp_assoc_sym   :=
       fun _ _ _ _ _ _ _ => symmetry (@comp_assoc _ _ _ _ _ _ _) |}.

Open Scope raw_morphism_scope.

(*
   nLab: https://ncatlab.org/nlab/show/functor
   Wikipedia: https://en.wikipedia.org/wiki/Functor

   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class Denotation {C : RawCategory} {D : Category} := {
  dobj : C → D;                                   (* object map  C₀ → D₀ *)
  denote {x y : C} (f : x ~>⁻ y) : dobj x ~> dobj y;  (* morphism map on homs *)

  h_id (x : C) : @denote x x r_id ≈ id;           (* preserves identities *)
  h_compose (x y z : C) (f : y ~>⁻ z) (g : x ~>⁻ y) :
    denote (f ∘⁻ g) ≈ denote f ∘ denote g         (* preserves composition *)
}.

Coercion dobj : Denotation >-> Funclass.

Notation "C ⟶⁻ D" := (@Denotation C%raw_category D%category)
  (at level 90, right associativity) : type_scope.

(*
   本节说明拉回/推出、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition DerivedEquivalence
        `(F : C ⟶⁻ D) : ∀ X Y, Setoid (X ~>⁻ Y) := fun X Y =>
  {| equiv := fun f g => denote f ≈ denote g
   ; setoid_equiv := _ |}.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition LawfulCategory `{F : C ⟶⁻ D} : Category :=
  @From_RawCategory C (DerivedEquivalence F) _ _ _ _.
Next Obligation. proper; now rewrite !h_compose, X, X0. Qed.
Next Obligation. rewrite h_compose, h_id; now cat. Qed.
Next Obligation. rewrite h_compose, h_id; now cat. Qed.
Next Obligation. rewrite !h_compose; now cat. Qed.
