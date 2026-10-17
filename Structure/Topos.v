Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* 初等 topos。

   nLab:      https://ncatlab.org/nlab/show/topos
   nLab:      https://ncatlab.org/nlab/show/power+object
   Wikipedia: https://en.wikipedia.org/wiki/Topos

   初等 topos 是有有限极限、笛卡尔闭且有子对象分类子的范畴。有限极限此处*显式*携带为
   终对象 + 二元积 + 拉回，故意不把等化子加入类。

   该冗余现是*选择*而非缺口。拉回到积与等化子的归约及其逆*已*形式化——
   [Structure/Pullback/Reduction.v] 的 [pullback_of_equalizer] /
   [HasPullbacks_of_Cartesian_HasEqualizers] 与 [equalizer_of_pullback]，反向有
   [Cartesian_of_HasPullbacks_Terminal] 与 [HasEqualizers_of_HasPullbacks_Terminal]。
   类仍显式保留分量，使实例可供给它实际计算用的那些，消费者不必为不需要的归约付费。

   精确划定范围，因冗余声称窄于「有限极限冗余」：相关的是二元与平行对生成子。等化子现对
   每个 topos 导出，见 [Structure/Topos/Monadic.v] 的 [topos_HasEqualizers]；有限完备性
   在四个初等生成子层陈述——终对象、二元积、拉回、等化子——为 [topos_finitely_complete]。
   [Limit]-形读法现是 [Structure/Limit/Finite.v] 的 [FinitelyComplete]，由类的终对象与拉回经
   [finitely_complete_of_pullbacks_terminal] 导出。有限余极限是 Structure/Topos/Colimits.v
   的 [topos_has_finite_colimits]——Paré 定理，经 [Structure/Topos/Monadic.v] 的单子幂对象函子——
   仍在生成子层：初始对象、二元余积、余等化子、推出。

   宇宙注记：类是分量类的普通记录，各对环境范畴宇宙多态；除其字段外不引入宇宙约束。 *)

(*
   关于toposes的来源与用途

   nLab:      https://ncatlab.org/nlab/show/topos
   Wikipedia: https://en.wikipedia.org/wiki/Lawvere%E2%80%93Tierney_topology
   Book:  Artin, Grothendieck, Verdier, "Théorie des topos et cohomologie
   Paper: Lawvere, "Quantifiers and Sheaves", Actes du Congrès

   本节说明topos、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class ElementaryTopos (C : Category) := {
  topos_terminal   : @Terminal C;
  topos_cartesian  : @Cartesian C;
  topos_pullbacks  : @HasPullbacks C;
  topos_closed     : @Closed C topos_cartesian;
  topos_classifier : @SubobjectClassifier C topos_terminal
}.

#[export] Existing Instance topos_terminal.
#[export] Existing Instance topos_cartesian.
#[export] Existing Instance topos_pullbacks.
#[export] Existing Instance topos_closed.
#[export] Existing Instance topos_classifier.

(* The power object of a: the exponential Ω^a.  Mind the argument order of
   Structure/Cartesian/Closed.v: [exponent_obj x y] displays as y ^ x, so
   [Ω ^ a] is [exponent_obj a Ω]. *)
Definition Pow {C : Category} {H : ElementaryTopos C} (a : C) : C := Ω ^ a.

(*
   本节说明hom、同构、子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition relations_iso {C : Category} {H : ElementaryTopos C} (a b : C) :
  @Isomorphism Sets {| carrier := SubObj (a × b) |}
                    {| carrier := a ~> Pow b |} :=
  iso_compose exp_iso (classifier_classifies (a × b)).
