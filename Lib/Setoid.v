Local Set Warnings "-notation-overridden". (* needed for Coq <8.16 / Coq < 8.16 所需 *)

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Vectors.Fin.
Require Export Category.Lib.Foundation.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(*
 nLab: https://ncatlab.org/nlab/show/setoid
 nLab: https://ncatlab.org/nlab/show/equivalence+relation
 Wikipedia: https://en.wikipedia.org/wiki/Setoid

 A setoid is a type [A] together with a distinguished equivalence relation
 [equiv] on it, written `≈`. Setoids stand in for quotient sets in a type
 theory that lacks quotient types: rather than identifying elements, one
 carries the equivalence explicitly and proves every operation respects it
 (the respectfulness/[Proper] discipline of Coq's generalized rewriting; see
 Coq.Classes.Morphisms). This is the foundational structure of the library:
 every hom is a setoid (a hom-setoid), so morphism equality throughout is the
 chosen `≈` rather than Coq's `=`. The relation lives in [crelation] (a
 [Type]-valued, hence proof-relevant, relation) so that equivalence proofs
 may carry computational content.

 The defining laws of [equiv], packaged as [Equivalence], are:
 reflexivity   x ≈ x
 symmetry      x ≈ y  ->  y ≈ x
 transitivity  x ≈ y  ->  y ≈ z  ->  x ≈ z 

 --------
 nLab: https://ncatlab.org/nlab/show/setoid
 nLab: https://ncatlab.org/nlab/show/equivalence+relation
 Wikipedia: https://en.wikipedia.org/wiki/Setoid

 setoid 是类型 [A] 连同其上的指定等价关系 [equiv]（写作 `≈`）。在缺少商类型的类型论中，setoid 充当商集：不是把元素等同起来，而是显式携带等价，并证明每个运算都尊重它（Coq 广义重写的尊重性/[Proper] 纪律；见 Coq.Classes.Morphisms）。这是本库的基础结构：每个 hom 都是 setoid（hom-setoid），因而态射相等一律是选定的 `≈` 而非 Coq 的 `=`。该关系取自 [crelation]（`Type` 值、故而证明相关的关系），使等价证明可携带计算内容。

 [equiv] 的定义律打包为 [Equivalence]：
 自反   x ≈ x
 对称   x ≈ y  ->  y ≈ x
 传递   x ≈ y  ->  y ≈ z  ->  x ≈ z
*)
Class Setoid A := {
  equiv : crelation A;                  (* the equivalence ≈ on A / A 上的等价 ≈ *)
  setoid_equiv : Equivalence equiv      (* refl/symm/trans laws for ≈ / ≈ 的自反/对称/传递律 *)
}.
#[export] Existing Instance setoid_equiv.

(*
 A setoid is in particular an [Equivalence], so its instance may be used
 wherever generalized rewriting expects one. 

 --------
 setoid 尤其是一个 [Equivalence]，因此其实例可用于凡是广义重写期望 Equivalence 的地方。
*)
Coercion setoid_equiv : Setoid >-> Equivalence.

Notation "f ≈ g" := (equiv f g) (at level 79) : category_theory_scope.

(*
 Coq's [eq] is an equivalence relation; this is a universe-polymorphic
 repackaging of the standard-library proofs so that the setoids below can be
 built at an arbitrary universe level. 

 --------
 Coq 的 [eq] 是等价关系；这是对标准库证明的宇宙多态再包装，使下文 setoid 可建在任意宇宙层级。
*)
Definition eq_equivalence@{t u} {A : Type@{t}} : @Equivalence@{t u} A (@eq A) :=
  @Build_Equivalence@{t u} A
    (@eq A) (@eq_Reflexive A)
    (@eq_Symmetric A)
    (@eq_Transitive A).

(*
 A universe-polymorphic unit type. Used as the carrier of the terminal
 setoid (see Instance/One.v) where the polymorphism of the standard [unit]
 would be too restrictive. 

 --------
 宇宙多态的单位类型。用作终对象 setoid 的载体（见 Instance/One.v）；标准 [unit] 的多态性在此过窄。
*)
Inductive poly_unit@{u} : Type@{u} := ttt.

(* The terminal/unit setoid: [poly_unit] under propositional equality. / 终/单位 setoid：[poly_unit] 配以命题相等。 *)
Definition unit_setoid@{t u} : Setoid@{t u} poly_unit@{t} :=
  {| equiv := @eq poly_unit@{t}
   ; setoid_equiv := @eq_equivalence@{t u} poly_unit@{t} |}.

(*
 The discrete setoid on [A]: equivalence is just Coq's `=`. This is the
 tightest equivalence on a type and recovers ordinary (extensional) sets. 

 --------
 离散 setoid [A]：等价就是 Coq 的 `=`。这是类型上最紧的等价，恢复通常（外延）集合。
*)
Definition eq_Setoid@{u} (A : Type@{u}) : Setoid@{u u} A :=
  Build_Setoid@{u _} A (λ f g, eq f g) eq_equivalence@{u u}.

(*
 The function setoid: two functions are equivalent when they agree
 pointwise up to the codomain's equivalence. This is extensional equality of
 functions, realised without the [funext] axiom by working up to `≈`. The
 low priority [| 9] keeps it from pre-empting more specific instances during
 resolution. 

 --------
 函数 setoid：两函数等价当且仅当它们在陪域等价下逐点一致。这是函数的外延相等，借由在 `≈` 上工作而无需 [funext] 公理。低优先级 [| 9] 防止解析时抢在更具体实例之前。
*)
#[export]
Program Instance funext_Setoid
        {T : Type} (t : T → Type) (a b : T) `{Setoid (t b)} :
  Setoid (t a → t b) | 9 := {|
  equiv := λ f g, ∀ x, f x ≈ g x
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - symmetry.
    now apply X.
  - now rewrite X, X0.
Qed.

(* The standard finite type [Fin.t n] as a discrete setoid under `=`. / 标准有限类型 [Fin.t n] 作为在 `=` 下的离散 setoid。 *)
#[export]
Program Instance Fin_Setoid {n} : Setoid (Fin.t n) := {|
  equiv := eq
|}.

(*
 Unique existence up to `≈`: a witness [unique_obj] satisfying [P], together
 with the proof [uniqueness] that any other witness is equivalent to it. This
 is the constructive content behind the `∃!` notation below and underlies the
 universal properties (limits, adjunctions) stated throughout the library. 

 --------
 在 `≈` 下的唯一存在：见证 [unique_obj] 满足 [P]，并有证明 [uniqueness] 说任何其他见证都与之等价。这是下文 `∃!` 记号背后的构造性内容，并支撑库中陈述的（余）极限、伴随等泛性质。
*)
Class Unique `{S : Setoid A} (P : A → Type) := {
  unique_obj : A;                          (* the witnessing element / 见证元素 *)
  unique_property : P unique_obj;          (* it satisfies P / 它满足 P *)
  uniqueness      : ∀ v : A, P v → unique_obj ≈ v;  (* and is unique up to ≈ / 且在 ≈ 下唯一 *)
}.

Arguments unique_obj {_ _ _} _.
Arguments unique_property {_ _ _} _.
Arguments uniqueness {_ _ _} _.

Notation "∃! x .. y , P" := (Unique (fun x => .. (Unique (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : category_theory_scope.

(*
 Injectivity and surjectivity of a function between setoids, stated up to
 `≈` rather than `=`. The [not-a-class] warning is silenced because these
 single-field classes are used as plain propositions, not for instance
 resolution; it is restored immediately afterwards. 

 --------
 setoid 之间函数的单射性与满射性，按 `≈` 而非 `=` 陈述。关闭 [not-a-class] 警告是因为这些单字段类当作普通命题使用，而非用于实例解析；之后立即恢复。
*)
Local Set Warnings "-not-a-class".

(* [f] is injective when equal images force equivalent arguments. / [f] 单射：像相等则强制自变量等价。 *)
Class injective {A : Type} `{Setoid A} {B : Type} `{Setoid B} (f : A -> B) :=
  { inj {x y} : f x ≈ f y -> x ≈ y }.

(* [f] is (split) surjective: every [y] has a chosen preimage up to `≈`. / [f]（分裂）满射：每个 [y] 都有选定的、在 `≈` 下的原像。 *)
Class surjective {A : Type} {B : Type} `{Setoid B} (f : A -> B) :=
  { surj {y} : { x & f x ≈ y} }.

Local Set Warnings "not-a-class".
