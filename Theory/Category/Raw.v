Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Reserved Infix "~>⁻" (at level 90, right associativity).
Reserved Infix "∘⁻" (at level 40, left associativity).

(*
nLab: https://ncatlab.org/nlab/show/category
   Wikipedia: https://en.wikipedia.org/wiki/Category_(mathematics)

   A [RawCategory] is the bare data of a category -- objects, a hom for each
   pair of objects, an identity for each object, and a composition -- WITHOUT
   any of the structure that [Category] (Theory/Category.v) adds on top:

     - there is no [homset] field, so the hom `a ~>⁻ b` is a plain [Type]
       rather than a setoid, and there is no chosen equivalence `≈` on
       morphisms; and
     - there are no unit or associativity laws.

   So a [RawCategory] is a "lawless category": the signature of a category
   stripped of both the hom-setoid quotient and the categorical axioms. This
   is the "other category using only equality, with a functor from that
   category to this" that Theory/Category.v anticipates: rather than discharge
   the laws directly (often awkward under Coq's restrictive `=`), one defines
   the raw data here and recovers a lawful [Category] through a [Denotation]
   (a functor into a lawful category, see below). The decorated notations
   `~>⁻` and `∘⁻` mirror `~>` and `∘` from Theory/Category.v.

--------
nLab：https://ncatlab.org/nlab/show/category
维基百科：https://en.wikipedia.org/wiki/Category_(mathematics)

[RawCategory] 是一个范畴的裸数据 —— 对象，每一对对象的同构，每个对象的恒等映射，以及复合 —— 不包含 [Category] (Theory/Category.v) 在其上添加的任何结构：

- 没有 [homset] 字段，所以同质 `a ~>⁻ b` 是一个普通的 [Type]，而不是一个集合，并且在态射上没有选择的等价 `≈`；
- 没有单位律或结合律。

所以 [RawCategory] 是一个“无法律范畴”：一个范畴的签名，去掉了同态集合商和范畴公理。这就是 Theory/Category.v 所预期的“使用仅等式的其他范畴，并且有一个从该范畴到此范畴的函子”：不是直接处理那些律（在 Coq 限制的 `=` 下常常很尴尬），而是在这里定义原始数据，并通过 [Denotation]（一个进入合法范畴的函子，见下文）恢复一个合法的 [Category]。带装饰的符号 `~>⁻` 和 `∘⁻` 对应于 Theory/Category.v 中的 `~>` 和 `∘`。
*)
Class RawCategory := {
  r_obj : Type;                         (* collection of objects / 对象的集合 *)

  r_uhom := Type : Type;                (* universe of homs (bare Types) / Homs 宇宙（裸类型） *)
  r_hom : r_obj → r_obj → r_uhom where "a ~>⁻ b" := (r_hom a b);  (* morphisms x ~>⁻ y / 态射 x ~>⁻ y *)

  r_id {x} : r_hom x x;                 (* identity morphism on x / x上的恒等态射 *)
  r_compose {x y z} (f: r_hom y z) (g : r_hom x y) : r_hom x z
    where "f ∘⁻ g" := (r_compose f g);  (* composition f ∘⁻ g / 复合 f ∘⁻ g *)
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
Assemble a lawful [Category] from raw data once the missing setoid
   ([homset]), the [Proper] respectfulness of composition, and the unit and
   associativity laws are supplied externally. The dual associativity law
   [comp_assoc_sym] (present for the built-in duality of Theory/Category.v) is
   filled in here by symmetry of [comp_assoc], so it need not be given.

--------
一旦缺失的集合论 ([homset])、组成的 [Proper] 尊重性，以及单位律和结合律由外部提供，就可以从原始数据组装一个合法的 [Category]。内置的 Theory/Category.v 对偶性存在的对偶结合律 [comp_assoc_sym] 在此通过 [comp_assoc] 的对称性得以填充，因此无需提供。
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

   A [Denotation] is a functor from a lawless [RawCategory] C to a lawful
   [Category] D: an object map [dobj], a morphism map [denote], and the two
   functoriality laws preserving identities ([h_id]) and composition
   ([h_compose]). Because D is lawful and equality of source morphisms is
   defined by their image under [denote] (see [DerivedEquivalence] below),
   these two laws are enough to transport D's unit and associativity laws back
   onto C, recovering a lawful [Category] (see [LawfulCategory] below).

--------
nLab: https://ncatlab.org/nlab/show/functor
   维基百科: https://en.wikipedia.org/wiki/Functor

   一个 [Denotation] 是从一个非法的 [RawCategory] C 到一个合法的 [Category] D 的函子：一个对象映射 [dobj]，一个态射映射 [denote]，以及两个保函律保持恒等 ([h_id]) 和复合 ([h_compose]) 的律。因为 D 是合法的，并且源态射的相等性由它们在 [denote] 下的像来定义（见下文 [DerivedEquivalence]），这两条律足以将 D 的单位律和结合律传回到 C 上，从而恢复一个合法的 [Category]（见下文 [LawfulCategory]）。
*)
Class Denotation {C : RawCategory} {D : Category} := {
  dobj : C → D;                                   (* object map  C₀ → D₀ / 对象映射  C₀ → D₀ *)
  denote {x y : C} (f : x ~>⁻ y) : dobj x ~> dobj y;  (* morphism map on homs / 同态上的态射映射 *)

  h_id (x : C) : @denote x x r_id ≈ id;           (* preserves identities / 保留恒等 *)
  h_compose (x y z : C) (f : y ~>⁻ z) (g : x ~>⁻ y) :
    denote (f ∘⁻ g) ≈ denote f ∘ denote g         (* preserves composition / 保持组成 *)
}.

Coercion dobj : Denotation >-> Funclass.

Notation "C ⟶⁻ D" := (@Denotation C%raw_category D%category)
  (at level 90, right associativity) : type_scope.

(*
The hom-setoid on the raw category induced by a denotation: two raw
   morphisms are equivalent exactly when their images under [denote] are
   equivalent in the lawful target. This is the pullback of D's `≈` along
   [denote], and it is an equivalence relation because `≈` on D is.

--------
由一个指称引起的原始范畴上的同构等价集：当两个原始态射在 [denote] 下的像在合法目标中等价时，它们恰好是等价的。这是 D 的 `≈` 沿 [denote] 的拉回，并且它是一个等价关系，因为 D 上的 `≈` 是等价关系。
*)
Program Definition DerivedEquivalence
        `(F : C ⟶⁻ D) : ∀ X Y, Setoid (X ~>⁻ Y) := fun X Y =>
  {| equiv := fun f g => denote f ≈ denote g
   ; setoid_equiv := _ |}.

(*
Given a lawless [RawCategory], a lawful [Category], and a denotation from
   the former to the latter, re-present the source as a lawful [Category] by
   way of that denotation: take the derived hom-setoid above, then discharge
   the unit and associativity laws by rewriting with [h_id] and [h_compose]
   and appealing to the corresponding laws of the lawful target.

--------
给定一个无法律的 [RawCategory]，一个有法律的 [Category]，以及从前者到后者的指称，通过该指称将源重新表示为有法律的 [Category]：取上面推导出的同态集，然后通过使用 [h_id] 和 [h_compose] 重写，并诉诸有法律目标的相应法则，来解除单位和结合律。
*)
Program Definition LawfulCategory `{F : C ⟶⁻ D} : Category :=
  @From_RawCategory C (DerivedEquivalence F) _ _ _ _.
Next Obligation. proper; now rewrite !h_compose, X, X0. Qed.
Next Obligation. rewrite h_compose, h_id; now cat. Qed.
Next Obligation. rewrite h_compose, h_id; now cat. Qed.
Next Obligation. rewrite !h_compose; now cat. Qed.
