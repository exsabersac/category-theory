Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Cartesian.
Require Import Category.Instance.Cat.Cartesian.Closed.
Require Import Category.Instance.Cat.Exponential.

Generalizable All Variables.

(* * * The evaluation functor as [Cat]'s exponential evaluation / * * 作为 [Cat] 指数评估的评估函子 *)

(*
 Satellite of Instance/Fun/Eval.v (Mac Lane §V.3, maclane:V.3:construction1):
 the two-variable evaluation is [Cat]'s exponential counit, named, and the
 fixed-object evaluation is its partial application.

 WHAT IS DELIVERED (6 constants, every one closed under the global
 context).
 - [CatEval P X : [P, X] ∏ P ⟶ X := @eval Cat Cat_Cartesian Cat_Closed P
 X] — the functor Instance/Cat/Cartesian/Closed.v describes in
 prose and leaves unnamed.
 - [CatEval_obj]/[CatEval_map]: its two data fields ARE Instance/Fun/
 Eval.v's [EvalBi]'s, at [eq_refl] — which is why [EvalBi] uses the
 arrow order [fmap[K] f ∘ transform[σ] p].
 - [eval_is_CatEval_partial_obj] at [eq_refl] and
 [eval_is_CatEval_partial_map] at [≈]: the fixed-object [Eval p] is
 the partial application of [Cat]'s own evaluation (the [≈] is
 [eval_partial_map]'s: [Partial_l] carries an [fmap id]).
 - [eval_transpose J P X : [J ∏ P, X] ≅[Cat] [J, [P, X]] :=
 Cat_exp_prod_l J P X] — the issue's “record the parameter/adjunct
 passage” is Instance/Cat/Exponential.v's existing isomorphism,
 cited, not rebuilt.

 UNIVERSES (measured by [About] under [Set Printing Universes]).  The
 price of the [Cat] route, and the reason Instance/Fun/Eval.v builds
 [EvalBi] directly: the five [CatEval*] constants carry [u0 = u1],
 [u0 = u5], [u0 = u6] — P's and X's object and hom levels collapse into
 one universe ([Functor@{u0 u0 u0 u5 u6 u6}] with [u0 = u5 = u6]).  The
 binder [P X : Cat] is innocent: [EvalBi] restated at the same binder
 carries NO equation (measured), so the collapse comes from
 [Cat_Closed]'s exponential structure itself, not from being at [Cat].
 At arbitrary [P X : Category], [EvalBi] carries only Instance/Fun.v's
 [jh = ch].  [eval_transpose@{u u0}] lives at [Cat]'s
 single level ([Fun@{u u u u u u u0}]) with no equation.  All six carry
 [Basics.compose], [eq_rect] and [prod_rect] bounds; no word-bounded
 [Set], no [JMeq]/[EqdepFacts]/[eq_rect_r].  This is measured by [About],
 not by a refutation: the route typechecks.

 COUNTS.  6 constants (5 [def], 1 [prf]); one [Qed]; closure 33 files
 excluding self (Instance/Cat/Exponential.v costs 8 at the margin,
 Instance/Fun/Eval.v 1, the other fourteen [Require]s 0).  Precedent for
 an Instance/Fun/ file requiring Instance/Cat/*: Instance/Fun/Discrete.v
 and Instance/Fun/Action.v. 

 --------
 实例/函数/评估.v 的卫星 (Mac Lane §V.3, maclane:V.3:construction1): 
 双变量评估是 [Cat] 的指数余单位，被命名为，而固定对象评估是它的部分应用。传递的内容是什么（6 个常量，每一个在全局上下文下都是封闭的）。- [CatEval P X : [P, X] ∏ P ⟶ X := @eval Cat Cat_Cartesian Cat_Closed P X] — Instance/Cat/Cartesian/Closed.v 中以文字形式描述的函子，保持未命名。- [CatEval_obj] / [CatEval_map] ：其两个数据字段是 Instance/Fun/Eval.v 中 [EvalBi] 的数据字段，在 [eq_refl] — 这就是为什么 [EvalBi] 使用箭头顺序 [fmap[K] f ∘ transform [σ] p]。- [eval_is_CatEval_partial_obj] 在 [eq_refl] 以及 [eval_is_CatEval_partial_map] 在 [≈] ：固定对象 [Eval p] 是 [Cat] 自身计算的部分应用（[≈] 是 [eval_partial_map] 的：[Partial_l] 携带一个 [fmap id] ）。-  [eval_transpose J P X : [J ∏ P, X]  ≅ [Cat]   [J, [P, X] ] :=
 Cat_exp_prod_l J P X] — 该问题的“记录参数/附加项通路”是 Instance/Cat/Exponential.v 中已存在的同构，
 被引用，而不是重新构建。宇宙（由 [About] 在 [Set Printing Universes] 下测量）。[Cat] 路径的价格，以及 Instance/Fun/Eval.v 直接构建 [EvalBi] 的原因：那五个 [CatEval*] 常量承载 [u0 = u1]、[u0 = u5]、[u0 = u6]——P 的对象和 X 的同伦层级在一个宇宙中坍缩（[Functor@{u0 u0 u0 u5 u6 u6}] 与 [u0 = u5 = u6]）。绑定器 [P X : Cat] 是无辜的：在同一绑定器下重述的 [EvalBi] 不带任何方程（已测量），因此坍缩源于 [Cat_Closed] 自身的指数结构，而不是因为处于 [Cat]。在任意 [P X : Category] 下，[EvalBi] 仅承载 Instance/Fun.v 的 [jh = ch]。[eval_transpose@{u u0}] 位于 [Cat] 的单一层级（[Fun@{u u u u u u u0}]），没有方程。六者都承载 [Basics.compose]、[eq_rect] 和 [prod_rect] 的界限；没有字界限的 [Set]，也没有 [JMeq] / [EqdepFacts] / [eq_rect_r]。这是通过 [About] 测量的，而不是通过反驳：该路径类型检查通过。

 计数。6 个常量（5 个 [def]，1 个 [prf]）；一个 [Qed]；闭包 33 个文件，不包括自身（Instance/Cat/Exponential.v 在边际成本为 8，Instance/Fun/Eval.v 为 1，其他十四个 [Require] 为 0）。Instance/Fun/ 文件需要 Instance/Cat/* 的先例：Instance/Fun/Discrete.v 和 Instance/Fun/Action.v。
*)

Section CatEval.

Context (P X : Cat).

(*
 [Cat]'s exponential is the functor category (Instance/Cat/Cartesian/
 Closed.v's [Cat_Closed]), so the closed structure's own [eval] IS a
 functor [[P, X] ∏ P ⟶ X].  Named here; it is reachable only at [Cat]'s
 universes, which is why Instance/Fun/Eval.v builds [EvalBi] directly
 (see the header's universe measurement). 

 --------
 [Cat] 的指数是函子范畴 (Instance/Cat/Cartesian/Closed.v 的 [Cat_Closed])，所以闭结构自身的 [eval] 是一个函子 [[P, X] ∏ P ⟶ X]。这里命名它；它只能在 [Cat] 的宇宙中访问，这就是为什么 Instance/Fun/Eval.v 直接构建 [EvalBi]（见文件头的宇宙测量）。
*)
Definition CatEval : ([P, X] ∏ P) ⟶ X := @eval Cat Cat_Cartesian Cat_Closed P X.

(* Its two data fields ARE [EvalBi]'s, on the nose. / 它的两个数据字段正好是 [EvalBi] 的。 *)
Definition CatEval_obj (Hp : ([P, X] ∏ P)) :
  fobj[CatEval] Hp = fobj[EvalBi] Hp := eq_refl.

Definition CatEval_map (Hp Kq : ([P, X] ∏ P)) :
  @fmap _ _ CatEval Hp Kq = @fmap _ _ (@EvalBi P X) Hp Kq := eq_refl.

(*
 So the fixed-object evaluation is the partial application of [Cat]'s
 own evaluation: on objects on the nose, on arrows up to ≈ (through
 Instance/Fun/Eval.v's [eval_partial_map]). 

 --------
 因此，固定对象的评估是 [Cat] 自身评估的部分应用：在对象本身上，在箭头上直到 ≈（通过 Instance/Fun/Eval.v 的 [eval_partial_map]）。
*)
Definition eval_is_CatEval_partial_obj (p : P) (H : [P, X]) :
  fobj[Eval p] H = fobj[Partial_l CatEval p] H := eq_refl.

Lemma eval_is_CatEval_partial_map (p : P) (H K : [P, X]) (s : H ~{[P, X]}~> K) :
  fmap[Eval p] s ≈ fmap[Partial_l CatEval p] s.
Proof. exact (eval_partial_map p H K s). Qed.

End CatEval.

(*
 The parameter/adjunct passage the issue asks to record already exists as
 an isomorphism in [Cat]: Instance/Cat/Exponential.v's [Cat_exp_prod_l].
 Cited, not rebuilt. 

 --------
 参数/附加段落——该问题要求记录的内容——已经作为同构存在于 [Cat] : Instance/Cat/Exponential.v 的 [Cat_exp_prod_l] 中。已引用，未重建。
*)
Definition eval_transpose (J P X : Cat) :
  @Isomorphism Cat ([J ∏ P, X]) ([J, [P, X]]) := Cat_exp_prod_l J P X.
