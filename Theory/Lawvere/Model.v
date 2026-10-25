Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Instance.Fun.
Require Import Category.Construction.Subcategory.
Require Import Category.Theory.Lawvere.

Generalizable All Variables.

(** * Models of a Lawvere theory / * 拉韦理论的模型 *)

(*
nLab:      https://ncatlab.org/nlab/show/Lawvere+theory
   Wikipedia: https://en.wikipedia.org/wiki/Lawvere_theory

   A model (or algebra) of a Lawvere theory [T] in a cartesian category [C]
   is a finite-product-preserving functor [law_cat T ⟶ C].  In this library
   product preservation splits into two separate concerns, mirroring the
   nullary/binary split of finite products themselves:

     - [CartesianFunctor] (Functor/Structure/Cartesian.v): the binary
       comparison F (x × y) ≅ F x × F y is an isomorphism;
     - [TerminalFunctor] (Functor/Structure/Terminal.v): the nullary
       comparison 1 ≅ F 1 is an isomorphism.

   [Model] bundles a functor with both preservation witnesses.

   Morphisms of models are ALL natural transformations between the
   underlying functors — no compatibility condition is imposed, because
   product preservation is property-like structure on the objects, not on
   the morphisms.  Accordingly the category of models [Models T C] is the
   FULL subcategory of the functor category [law_cat T, C] on the
   product-preserving functors, built with Construction/Subcategory.v
   exactly as Construction/Localization.v builds the full subcategory of
   W-local objects: [sobj] selects the preservation witnesses and [shom]
   retains every morphism ([True]).

--------
nLab：https://ncatlab.org/nlab/show/Lawvere+theory
维基百科：https://en.wikipedia.org/wiki/Lawvere_theory

在笛卡尔范畴 [C] 中，Lawvere 理论 [T] 的一个模型（或代数）是一个有限积保持函子 [law_cat T ⟶ C]。在本库中，积的保持分为两个独立的问题，反映了有限积本身的零元/二元划分：

- [CartesianFunctor]（Functor/Structure/Cartesian.v）：二元比较 F (x × y) ≅ F x × F y 是一个同构；
- [TerminalFunctor]（Functor/Structure/Terminal.v）：零元比较 1 ≅ F 1 是一个同构。

[Model] 将一个函子与两个保护见证捆绑在一起。

模型的态射是底层函子之间的所有自然变换——没有施加兼容性条件，因为积保持是对象上的一种属性性结构，而不是态射上的结构。因此，模型的范畴 [Models T C] 是函子范畴 [law_cat T, C] 在积保持函子上的完全子范畴，它是用 Construction/Subcategory.v 构建的，正如 Construction/Localization.v 构建 W-局部对象的完全子范畴一样：[sobj] 选择保持证明，而 [shom] 保留每个态射 ([True])。
*)

Section Model.

Context (T : LawvereTheory).
Context (C : Category).
Context `{@Cartesian C}.
Context `{@Terminal C}.

Record Model := {
  model_fun : @law_cat T ⟶ C;

  model_cartesian :
    @CartesianFunctor (@law_cat T) C model_fun (@law_cartesian T) _;

  model_terminal :
    @TerminalFunctor (@law_cat T) C model_fun (@law_terminal T) _
}.

(**
** The category of models

    The full subcategory of the functor category [law_cat T, C] whose
    objects carry both preservation witnesses.  [shom] retains every
    natural transformation ([True]), so closure under identity and
    composition is trivial ([I]) — the same shape as [C_W] in
    Construction/Localization.v.

--------
** 模型的范畴

函子范畴 [law_cat T, C] 的完全子范畴，其对象都携带两个保持证据。[shom] 保留每个自然变换 ([True])，因此在恒等和复合下的封闭性是显而易见的 ([I])——其形状与 Construction/Localization.v 中的 [C_W] 相同。
*)

Definition Models_sub : Subcategory (@Fun (@law_cat T) C) :=
  @Build_Subcategory (@Fun (@law_cat T) C)
    (fun F : @law_cat T ⟶ C =>
       (@CartesianFunctor (@law_cat T) C F (@law_cartesian T) _ *
        @TerminalFunctor (@law_cat T) C F (@law_terminal T) _)%type)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Models : Category := Sub (@Fun (@law_cat T) C) Models_sub.

(**
** Bridges between the record and subcategory presentations

    A [Model] packs into an object of [Models], and every object of
    [Models] unpacks to a [Model]; the two presentations carry exactly
    the same data.

--------
** 记录展示与子范畴展示之间的桥梁

    一个 [Model] 打包成一个 [Models] 对象，而每一个 [Models] 对象解包成一个 [Model]；这两种展示携带完全相同的数据。
*)

Definition Model_pack (M : Model) : Models :=
  (model_fun M; (model_cartesian M, model_terminal M)).

Definition Model_unpack (x : Models) : Model :=
  {| model_fun       := `1 x
   ; model_cartesian := fst `2 x
   ; model_terminal  := snd `2 x |}.

(**
The two presentations are mutually inverse on the nose: each round
    trip is an eta-expansion, discharged by case analysis.  (Propositional
    [=] on the packed OBJECT data — the sanctioned case; no morphism
    equality is asserted.)

--------
这两个表示方式在本质上是相互逆的：每次往返都是一个 eta 扩展，通过案例分析来完成。（对打包的 OBJECT 数据进行命题 [=] —— 这是被批准的情况；没有断言任何态射相等。）
*)

Lemma Model_unpack_pack (M : Model) : Model_unpack (Model_pack M) = M.
Proof. destruct M; reflexivity. Qed.

Lemma Model_pack_unpack (x : Models) : Model_pack (Model_unpack x) = x.
Proof. destruct x as [F [HC HT]]; reflexivity. Qed.

(**
** Morphisms of models are all natural transformations

    [Models_sub] is a full subcategory: every natural transformation
    between the underlying functors of two models is a morphism of
    models (the [shom] witness is [I]).

--------
** 模型的态射都是自然变换

[Models_sub] 是一个满子范畴：两个模型的底层函子之间的每一个自然变换都是模型的态射（[shom] 的证据是 [I]）。
*)

Definition Models_Full :
  Construction.Subcategory.Full (@Fun (@law_cat T) C) Models_sub :=
  fun _ _ _ _ _ => I.

(**
Concretely: any natural transformation between the underlying
    functors of two models lifts to a morphism in [Models], and it is
    sent back to itself by the (faithful) inclusion.

--------
具体来说：两个模型的基础函子之间的任何自然变换都可以提升为 [Models] 中的一个态射，并且它会通过（忠实的）包含映射返回自身。
*)

Definition Model_hom_of_transform (x y : Models) (f : `1 x ⟹ `1 y) :
  x ~{ Models }~> y := (f; I).

Lemma Model_hom_of_transform_incl (x y : Models) (f : `1 x ⟹ `1 y) :
  fmap[Incl _ Models_sub] (Model_hom_of_transform x y f)
    ≈ (f : `1 x ~{ @Fun (@law_cat T) C }~> `1 y).
Proof. simpl; intros; reflexivity. Qed.

End Model.
