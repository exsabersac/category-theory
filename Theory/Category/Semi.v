Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** * Semigroupoid (semicategory) / * 半群体（半范畴） *)

(*
nLab: https://ncatlab.org/nlab/show/semicategory
   Wikipedia: https://en.wikipedia.org/wiki/Semigroupoid

   A semigroupoid (also called a semicategory or non-unital category) is a
   category without identity morphisms: a collection of objects, a hom
   `semi_hom x y` of morphisms for each pair of objects, and a composition
   `semi_compose f g : x ~> z` for `g : x ~> y` and `f : y ~> z`, subject to
   the associativity law alone. There are no objects' identities and hence no
   unit laws -- that is the defining difference from a [Category], not a
   missing axiom. Having identities is an extra property a semigroupoid may or
   may not possess, not extra structure.

   As in [Category], the hom is a setoid (a hom-setoid) rather than a bare
   set, so morphism equality is the chosen equivalence `≈` rather than Coq's
   `=`. Every [Category] is in particular a [Semigroupoid] by forgetting its
   identities; this is witnessed by the coercion [to_Semigroupoid] below.

--------
nLab: https://ncatlab.org/nlab/show/semicategory
   维基百科: https://en.wikipedia.org/wiki/Semigroupoid

   半群范畴（也称为半范畴或非幺范畴）是一种没有恒等态射的范畴：它由一组对象组成，每对对象之间有一个态射的Hom集合`semi_hom x y`，以及一个用于`g : x ~> y`和`f : y ~> z`的合成`semi_compose f g : x ~> z`，仅满足结合律。不存在对象的恒等元素，因此也不存在单位律——这是它与[Category]的本质区别，而不是缺失的公理。拥有恒等元素是半群范畴可能具备也可能不具备的额外性质，而不是额外结构。

如同在[Category]中，Hom是一个集合等价（hom-setoid），而非单纯的集合，因此态射的等价由选择的等价`≈`定义，而不是Coq的`=`。每一个[Category]特别来说通过忘记其恒等元素后是一个[Semigroupoid]；这一点由下面的强制转换[to_Semigroupoid]所体现。
*)

Class Semigroupoid := {
  semi_obj : Type;                      (* collection of objects / 对象的集合 *)

  semi_uhom := Type : Type;             (* universe of hom-setoids / 同态集合的宇宙 *)
  semi_hom : semi_obj → semi_obj → semi_uhom;  (* morphisms x ~> y / 态射 x ~> y *)
  semi_homset : ∀ X Y, Setoid (semi_hom X Y);  (* hom is a setoid; equality is ≈ / hom 是一个集合等价结构；相等性是 ≈ *)

  semi_compose {x y z} (f: semi_hom y z) (g : semi_hom x y) : semi_hom x z;
                                        (* composition f ∘ g (no identity) / 复合 f ∘ g（无单位元） *)

  semi_compose_respects x y z :         (* compose respects ≈ (bifunctorial Proper) / 组成 respects ≈（双函子 Proper） *)
    Proper (equiv ==> equiv ==> equiv) (@semi_compose x y z);

  semi_dom {x y} (f: semi_hom x y) := x;  (* domain (source) of a morphism / 一个态射的定义域（来源） *)
  semi_cod {x y} (f: semi_hom x y) := y;  (* codomain (target) of a morphism / 一个态射的陪域（目标） *)

  semi_comp_assoc {x y z w} (f : semi_hom z w) (g : semi_hom y z) (h : semi_hom x y) :
    semi_compose f (semi_compose g h) ≈ semi_compose (semi_compose f g) h;
                                        (* associativity / 结合性 *)
  semi_comp_assoc_sym {x y z w} (f : semi_hom z w) (g : semi_hom y z) (h : semi_hom x y) :
    semi_compose (semi_compose f g) h ≈ semi_compose f (semi_compose g h)
                                        (* associativity, dual form (built-in duality) / 结合性，双重形式（内置二重性） *)
}.
#[export] Existing Instance semi_homset.
#[export] Existing Instance semi_compose_respects.

(*
Every category is a semigroupoid: keep the objects, homs, composition and
   associativity, and simply discard the identities and unit laws.

--------
每个范畴都是半群体：保留对象、态射、复合和结合律，只需舍弃单位元和单位律。
*)
Definition to_Semigroupoid (C : Category) : Semigroupoid := {|
  semi_obj              := obj;
  semi_hom              := hom;
  semi_homset           := homset;
  semi_compose          := @compose C;
  semi_compose_respects := @compose_respects C;
  semi_comp_assoc       := @comp_assoc C;
  semi_comp_assoc_sym   := @comp_assoc_sym C;
|}.

Coercion to_Semigroupoid : Category >-> Semigroupoid.
