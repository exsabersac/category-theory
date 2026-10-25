Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Terminal.

Generalizable All Variables.

Section SemicocartesianMonoidal.

Context {C : Category}.

(*
 nLab: https://ncatlab.org/nlab/show/semicartesian+monoidal+category
 Wikipedia: no dedicated article; the dual notion is described under
 https://en.wikipedia.org/wiki/Cartesian_monoidal_category

 A semicocartesian (also coaffine) monoidal category is the dual of a
 semicartesian one: a monoidal category whose unit object I is initial
 (nLab, same page: "a monoidal category is semicocartesian if the unit for
 the tensor product is an initial object"). Spelled out in this library's
 notation, that is the pair of conditions

 generate      : I ~> x             (a map out of I for every x),
 unit_initial  : f ≈ g              (any two I ~> x agree),

 so that I has exactly one map into each object: it is initial. It is the
 weaker companion to cocartesian monoidal, where the tensor is the
 categorical coproduct; here only the create maps out of I are guaranteed,
 not the codiagonals.

 With [Monoidal_op] from Construction/Opposite/Monoidal.v this could
 instead read

 Definition SemicocartesianMonoidal `{M : @Monoidal C} :=
 @SemicartesianMonoidal (C^op) Monoidal_op.

 but the derived instance's members would need re-unfolding at every use
 site — the same trade-off documented in Theory/Algebra/Comonoid.v — so
 the direct (dual-by-hand) class below mirrors the
 [SemicartesianMonoidal] fields with directions flipped. Just as initiality
 of I equips every tensor with coprojection maps, defined dually to the
 semicartesian projections from a create on one factor and a unitor inverse,

 embed_left  = (id ⨂ generate) ∘ rho^-1    : x ~> x ⨂ y,
 embed_right = (generate ⨂ id) ∘ lambda^-1 : y ~> x ⨂ y. 

 --------
 nLab:  https://ncatlab.org/nlab/show/semicartesian+monoidal+category
 维基百科: 没有专门的条目；双重概念在 https://en.wikipedia.org/wiki/Cartesian_monoidal_category 下有描述

 半余笛卡尔（也称为共仿射）单体范畴是半笛卡尔范畴的对偶：一个单位对象 I 为初始对象的单体范畴（nLab，同一页：“如果张量积的单位是一个初始对象，则该单体范畴是半笛卡尔的”）。用该库的符号表示，这就是一对条件

 generate      : I ~> x             （对于每个 x，从 I 出发的映射）,
 unit_initial  : f ≈ g              （任意两个 I ~> x 相同）,

 因此 I 对每个对象恰好有一个映射：它是初始对象。它是余笛卡尔单体范畴的较弱对应，其中张量是范畴的余积；这里仅保证从 I 创造映射，而不是确保余对角映射。使用 Construction/Opposite/Monoidal.v 中的 [Monoidal_op]，这可以改为写作

 Definition SemicocartesianMonoidal `{M : @Monoidal C} :=
 @SemicartesianMonoidal (C^op) Monoidal_op.

 但是生成实例的成员在每次使用时都需要重新展开——这是在 Theory/Algebra/Comonoid.v 中记录的相同权衡——所以下面的直接（手动对偶）类镜像了 [SemicartesianMonoidal] 字段，只是方向翻转。正如 I 的初始性使每个张量都配备了副投影映射，这些映射是对一个因子上的生成和一个单位逆元所定义的半笛卡尔投影的对偶定义，

 embed_left  = (id ⨂ generate) ∘ rho^-1    : x ~> x ⨂ y,
 embed_right = (generate ⨂ id) ∘ lambda^-1 : y ~> x ⨂ y.
*)

Class SemicocartesianMonoidal `{@Monoidal C} := {
  (* the create / coprojection-from-unit map, the unique I ~> x / 从单位的创建/共投射映射，唯一的 I ~> x *)
  generate {x} : I ~> x;

  (* uniqueness of maps out of I, i.e. I is initial (up to ≈) / 从 I 出发的映射的唯一性，即 I 是初始的（最多到 ≈） *)
  unit_initial {x} (f g : I ~> x) : f ≈ g;

  (* left coprojection x ~> x ⨂ y: undo the right unitor, then create y / 左余投射 x ~> x ⨂ y：撤销右单位器，然后创建 y *)
  embed_left  {x y} : x ~> x ⨂ y := id ⨂ generate ∘ unit_right⁻¹;
  (* right coprojection y ~> x ⨂ y: undo the left unitor, then create x / 右余投影 y ~> x ⨂ y：撤销左单位器，然后创建 x *)
  embed_right {x y} : y ~> x ⨂ y := generate ⨂ id ∘ unit_left⁻¹
}.

(* Creating before any map is creating: generate is natural, since both sides are maps I ~> B and I is initial. Dual of eliminate_comp. / 在任何地图之前创建就是创建：生成是自然的，因为两边都是地图 I ~> B 且 I 是初始的。eliminate_comp 的对偶。 *)

Corollary generate_comp `{@Monoidal C} `{@SemicocartesianMonoidal _} `{f : A ~> B} :
  f ∘ generate ≈ generate.
Proof. intros; apply unit_initial. Qed.

End SemicocartesianMonoidal.

Require Import Category.Structure.Initial.

(*
 The two directions below witness that "semicocartesian monoidal" and "the
 unit I is initial" are the same condition, packaged as an Initial structure
 on I and as a SemicocartesianMonoidal structure respectively. Cf. Wikipedia,
 https://en.wikipedia.org/wiki/Cartesian_monoidal_category : a cocartesian
 monoidal category has "the monoidal structure given by the coproduct and
 unit the initial object."

 Semicocartesian monoidal ==> I is an initial object, with generate as the
 unique arrow and unit_initial as its uniqueness proof. 

 --------
 下面的两个方向证明了“半余笛卡尔幺半群”和“单位对象 I 是初始对象”是相同的条件，分别以 I 上的初始结构和半余笛卡尔幺半群结构的形式呈现。参见维基百科，https://en.wikipedia.org/wiki/Cartesian_monoidal_category : 一个余笛卡尔幺半群范畴具有“由余积给出的幺半群结构，并且单位对象为初始对象”。

 半余笛卡尔幺半群 ==> I 是一个初始对象，其唯一箭头为 generate，unit_initial 是其唯一性证明。
*)

Program Definition SemicocartesianMonoidal_Initial `{@Monoidal C}
        `{@SemicocartesianMonoidal C _} : @Initial C := {|
  terminal_obj := @I C _;
  one := @generate _ _ _;
  one_unique := @unit_initial _ _ _
|}.

Import EqNotations.

(*
 Conversely, a monoidal category whose initial object 0 coincides with the
 unit object I (the hypothesis Heq : 0 = I) is semicocartesian monoidal:
 transport the unique arrow `zero` along Heq to obtain generate, and
 transport zero_unique to obtain unit_initial. 

 --------
 相反，一个初始对象 0 与单位对象 I 重合的单体范畴（假设 Heq : 0 = I）是半余笛卡尔单体的：沿 Heq 传递唯一箭头 `zero` 以获得 generate，并传递 zero_unique 以获得 unit_initial。
*)

Program Definition Initial_SemicocartesianMonoidal `{M : @Monoidal C}
        `{T : @Initial C} (Heq : @initial_obj C T = @I C M) :
  @SemicocartesianMonoidal C _ := {|
  generate := fun x => _ (@zero C T x);
  unit_initial := fun x f g => _ (@zero_unique C T x) f g
|}.
Next Obligation. rewrite Heq in x0; apply x0. Defined.
