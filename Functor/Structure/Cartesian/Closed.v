Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Functor.Structure.Cartesian.

Generalizable All Variables.

(** Cartesian closed functors *)

(*
nLab: https://ncatlab.org/nlab/show/cartesian+closed+functor
   nLab: https://ncatlab.org/nlab/show/closed+functor
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_functor

   A cartesian closed functor F : C ⟶ D between cartesian closed categories
   preserves both finite products and exponentials (internal homs). Product
   preservation is assumed here as [CartesianFunctor], so [prod_in]/[prod_out]
   already witness F (x × y) ≅ F x × F y. Whenever F preserves products there
   is a canonical exponential comparison map

       F (y^x) ~> F y ^ F x

   obtained as the transpose (curry) of the composite

       F (y^x) × F x ≅ F (y^x × x) --F eval--> F y,

   i.e. curry (fmap eval ∘ prod_in). F is cartesian closed exactly when this
   comparison is an isomorphism for all x, y. Viewing CCCs as cartesian closed
   monoidal categories, this is a strong monoidal functor that is also strong
   closed.

   Rather than building the comparison and asserting it is invertible, this
   class postulates the iso [fobj_exp_iso] directly and pins [exp_out] down to
   the canonical comparison via the coherence laws [fmap_curry]/[fmap_uncurry]
   (whence [fmap_eval] below recovers F eval = uncurry exp_out ∘ prod_out). The
   two presentations are equivalent. Cartesian closed functors are exactly the
   morphisms of models of the simply-typed lambda calculus. 

--------
nLab：https://ncatlab.org/nlab/show/cartesian+closed+functor
 nLab：https://ncatlab.org/nlab/show/closed+functor
 维基百科：https://en.wikipedia.org/wiki/Cartesian_closed_category
 维基百科：https://en.wikipedia.org/wiki/Monoidal_functor

笛卡尔闭类别之间的笛卡尔闭函子 F : C ⟶ D
 保留有限乘积和指数（内部 homs）。 产品展示
 此处假设保存为 [CartesianFunctor]，因此 [prod_in]/[prod_out]
 已经见证 F (x × y) ≅ F x × F y。 每当F在那里保存产品时
 是规范指数比较图

F (y^x) ~> F y ^ F x

作为复合材料的转置（咖喱）获得

F (y^x) × F x ≅ F (y^x × x) --F eval--> F y,

即咖喱（fmap eval ∘ prod_in）。 F 恰好在以下情况下为笛卡尔闭集
 比较是所有 x, y 的同构。 将 CCC 视为笛卡尔封闭
 幺半群类别，这是一个强幺半群函子，也很强
 关闭。

这不是建立比较并断言它是可逆的，而是
 类直接假定 iso [fobj_exp_iso] 并将 [exp_out] 固定到
 通过相干律 [fmap_curry]/[fmap_uncurry] 进行规范比较
 （因此下面的 [fmap_eval] 恢复 F eval = uncurry exp_out ∘ prod_out）。 的
 两个演示文稿是等效的。 笛卡尔闭函子正是
 简单类型 lambda 演算模型的态射。 
*)

Section ClosedFunctor.

Context `{F : C ⟶ D}.
Context `{@CartesianFunctor C D F CA CB}.
Context `{@Closed C CA}.
Context `{@Closed D CB}.

Class ClosedFunctor := {
  fobj_exp_iso {x y : C} : F (y^x) ≅ F y ^ F x;   (* exponential comparison iso *)

  exp_in  := fun x y => from (@fobj_exp_iso x y);  (* F y ^ F x ~> F (y^x) *)
  exp_out := fun x y => to   (@fobj_exp_iso x y);  (* comparison: F (y^x) ~> F y ^ F x *)

  (* Coherence: F commutes with currying up to the comparison.  / 连贯性：F 通过柯里化进行通勤以达到比较。*)
  fmap_curry {x y z : C} {f : x × y ~> z} :
    fmap (curry f) ≈ exp_in _ _ ∘ curry (fmap f ∘ prod_in);
  (* Coherence: F commutes with uncurrying up to the comparison.  / 连贯性：F 通过非柯里化进行通勤直至比较。*)
  fmap_uncurry {x y z : C} (f : x ~> z^y) :
    fmap (uncurry f) ≈ uncurry (exp_out _ _ ∘ fmap f) ∘ prod_out
}.

Context `{@ClosedFunctor}.

Arguments exp_in {_ _ _} /.
Arguments exp_out {_ _ _} /.

(*
F eval factors through the comparison: F eval ≈ uncurry exp_out ∘ prod_out,
   since curry eval ≈ id. This is the nLab map F (y^x × x) --F eval--> F y read
   through prod_out and exp_out. 

--------
通过比较 F eval 因子：F eval ≈ unccurry exp_out ∘ prod_out，
 因为柯里 eval ≈ id。 这是 nLab 映射 F (y^x × x) --F eval--> F y read
 通过 prod_out 和 exp_out。 
*)
Corollary fmap_eval {x y : C} :
  fmap (@eval C _ _ x y) ≈ uncurry (curry eval ∘ exp_out) ∘ prod_out.
Proof.
  intros.
  unfold eval, eval'.
  rewrite fmap_uncurry; cat.
Qed.

Corollary exp_in_out {x y : C} :
  exp_in ∘ exp_out ≈ @id _ (F (y^x)).
Proof. apply iso_from_to. Qed.

#[local] Hint Rewrite @exp_in_out : functors.

Corollary exp_out_in {x y : C} :
  exp_out ∘ exp_in ≈ @id _ (F y ^ F x).
Proof. apply iso_to_from. Qed.

#[local] Hint Rewrite @exp_out_in : functors.

Corollary exp_in_inj {x y z : C} (f g : F x ~> F z ^ F y) :
  exp_in ∘ f ≈ exp_in ∘ g ↔ f ≈ g.
Proof.
  split; intros Hexp.
  - rewrite <- id_left.
    rewrite <- exp_out_in.
    rewrite <- comp_assoc.
    rewrite Hexp.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  - subst.
    rewrite Hexp.
    reflexivity.
Qed.

Corollary exp_out_inj {x y z : C} (f g : F x ~> F (z^y)) :
  exp_out ∘ f ≈ exp_out ∘ g ↔ f ≈ g.
Proof.
  split; intros Hexp.
  - rewrite <- id_left.
    rewrite <- exp_in_out.
    rewrite <- comp_assoc.
    rewrite Hexp.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  - subst.
    rewrite Hexp.
    reflexivity.
Qed.

End ClosedFunctor.

Arguments exp_in {_ _ _ _ _ _ _ _ _ _ _} /.
Arguments exp_out {_ _ _ _ _ _ _ _ _ _ _} /.

#[export] Hint Rewrite @exp_in_out : functors.
#[export] Hint Rewrite @exp_out_in : functors.
