Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Coq.
Require Import Coq.Sets.Ensembles.

Generalizable All Variables.

(** * The category of ensembles / * 合奏类别 *)

(*
 nLab: https://ncatlab.org/nlab/show/Set
 nLab: https://ncatlab.org/nlab/show/category+of+sets
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_sets

 "Ens" (from the French/Bourbaki "Ensembles") is a traditional name for the
 category Set. In the textbook category of sets the objects are sets and the
 morphisms are *arbitrary* functions between them; injective, surjective and
 bijective functions are then characterized as the monos, epis and isos.

 This file does NOT build that classical category directly. Its objects are
 Coq [Ensemble]s (predicates [T -> Prop], i.e. subsets [A ⊆ T] of a carrier
 type [T]), packaged as a dependent pair [∃ T : Type, Ensemble T]. A morphism
 from [A : Ensemble TA] to [B : Ensemble TB] is a function [f : TA -> TB] on
 the *carrier types* satisfying

 ∀ x : TA,  x ∈ A  ↔  f x ∈ B,

 that is, [A = f⁻¹(B)]: [f] both preserves membership ([x ∈ A → f x ∈ B]) and
 reflects it ([f x ∈ B → x ∈ A]). Note this is membership preservation-and-
 reflection, NOT injectivity: it places no constraint of the form
 [f a = f b → a = b]. Two morphisms are identified when they agree pointwise
 on the whole carrier type. Identity and composition are the identity function
 and ordinary function composition. 

 --------
 nLab:  https://ncatlab.org/nlab/show/Set 
 nLab:  https://ncatlab.org/nlab/show/category+of+sets 
 Wikipedia:  https://en.wikipedia.org/wiki/Category_of_sets 

 “Ens”（来自法语/Bourbaki 的“Ensembles”）是集合范畴（Set）的传统名称。在集合的教科书范畴中，对象是集合，态射是它们之间的*任意*函数；单射、满射和双射函数随后被表征为单态射、满态射和同构。

 此文件并不直接构建该经典范畴。它的对象是 Coq [Ensemble]（谓词 [T -> Prop]，即承载类型 [T] 的子集 [A ⊆ T]），封装为依赖对 [∃ T : Type, Ensemble T]。从 [A : Ensemble TA] 到 [B : Ensemble TB] 的态射是在*承载类型*上满足条件的函数 [f : TA -> TB]

 ∀ x : TA,  x ∈ A  ↔  f x ∈ B,也就是说，[A = f⁻¹(B)] : [f] 既保持成员关系（[x ∈ A → f x ∈ B]），又反映成员关系（[f x ∈ B → x ∈ A]）。请注意，这是成员关系的保持和反映，而不是单射性：它不对形式为 [f a = f b → a = b] 的约束提出要求。当两个态射在整个载体类型上逐点相同时，它们被视为相同。恒等和复合分别是恒等函数和普通函数复合。
*)

(*
 Cross-reference: Mac Lane's Ens_V — objects the members of a set V of sets,
 arrows ALL functions between them (CWM 2nd ed., §I.2, printed p. 11) — is a
 DIFFERENT construction from the two categories below, and it lives in
 Instance/EnsV.v. There an object is a code x : V decoded by El : V → Type,
 and a morphism x ~> y is an arbitrary function El x → El y with no side
 condition at all; here a morphism carries the constraint A = f⁻¹(B). Both are
 kept: [Ens] and [EnsT] record membership preservation-and-reflection, while
 [EnsV] records Mac Lane's set-sized sub-universe of the category of sets. 

 --------
 交叉引用：Mac Lane 的 Ens_V —— 对于一组集合 V 的成员作为对象，所有它们之间的函数作为箭头（CWM 第2版，第I.2节，第11页印刷版）——是与下面两个范畴不同的构造，它位于 Instance/EnsV.v 中。在那里，一个对象是由 El : V → Type 解码的代码 x : V，而一个态射 x ~> y 是任意的函数 El x → El y，并且没有任何附加条件；在这里，一个态射携带约束 A = f⁻¹(B)。两者都保留：[Ens] 和 [EnsT] 记录成员资格的保持与反射，而 [EnsV] 记录 Mac Lane 的集合大小的集合范畴子宇宙。
*)

Program Definition Ens : Category := {|
  obj     := ∃ T : Type, Ensemble T;
  hom     := fun A B =>
    ∃ f : ``A → ``B, ∀ x : ``A, In _ (projT2 A) x ↔ In _ (projT2 B) (f x);
  homset  := fun P Q => {| equiv := fun f g => ∀ x, ``f x = ``g x |};
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g =>  (λ x, ``f (``g x); _)
|}.
Next Obligation. equivalence; rewrite H, H0; reflexivity. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. proper; rewrite H, H0; reflexivity. Qed.

(*
 nLab: https://ncatlab.org/nlab/show/Set
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_sets

 [EnsT T] is the same construction restricted to a single fixed carrier type
 [T]: objects are the [Ensemble]s (subsets) of [T], and a morphism from [A] to
 [B] is an endofunction [f : T -> T] with [∀ x, x ∈ A ↔ f x ∈ B], i.e.
 [A = f⁻¹(B)]. As above this is membership preservation-and-reflection, not
 injectivity. Morphisms are compared pointwise on [T], with identity and
 composition the identity function and function composition. 

 --------
 nLab：https://ncatlab.org/nlab/show/Set
 Wikipedia：https://en.wikipedia.org/wiki/Category_of_sets

 [EnsT T] 是相同构造，但限制于单一固定载体类型
 [T] ：对象是 [Ensemble] 的 [T] 的子集，而从 [A] 到 [B] 的态射是一个自函数 [f : T -> T]，满足 [∀ x, x ∈ A ↔ f x ∈ B]，即 [A = f⁻¹(B)]。如上所述，这是成员保留与反射，而不是单射。态射在 [T] 上按点比较，恒等和复合分别是恒等函数和函数复合。
*)

Program Definition EnsT (T : Type) : Category := {|
  obj     := Ensemble T;
  hom     := fun A B =>
    ∃ f : T → T, ∀ x : T, In _ A x ↔ In _ B (f x);
  homset  := fun P Q => {| equiv := fun f g => ∀ x, ``f x = ``g x |};
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g =>  (λ x, ``f (``g x); _)
|}.
Next Obligation. equivalence; rewrite H, H0; reflexivity. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. proper; rewrite H, H0; reflexivity. Qed.
