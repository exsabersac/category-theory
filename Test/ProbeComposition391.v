Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Natural.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.Coend.
Require Import Category.Construction.Enriched.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Composition.

Generalizable All Variables.

(** * Probe for Structure/Cartesian/Closed/Composition.v (issue #391) / * 探针用于结构/笛卡尔/闭合/组合.v（问题 #391） *)

(*
Mac Lane §IV.6 Exercise 4 (`maclane:IV.6:ex4`).  Everything the target
   MEASURES and does not itself state is pinned here, from OUTSIDE that
   file, so that a rename of a target constant breaks this probe rather
   than silently turning a guard green.  The `Require` list above mirrors
   the target's exactly, plus the target itself.

   FIVE negatives of THREE kinds, told apart by the error text:

     1  CONVERSION  the [Sets] agreement does not hold at Leibniz equality
                    on whole MORPHISMS -- only pointwise
     2  TYPING      the naive functorial action in [b] is not well typed,
                    which is why there is no naturality square in [b]
     3  CONVERSION  the two candidate hom-TYPES of that action differ
     4  CONVERSION  a functor whose [fobj] is elaborated inside its own
                    [Program Definition] converts with nothing
     5  FORMABILITY [Cartesian] identifies a category's hom and proof
                    universes, which is where the target's binder
                    [Category@{u u0 u0}] comes from

   plus one scope-free instrument check.  Each was stripped one at a time,
   compiled alone, and its whole error read.

--------
Mac Lane §IV.6 练习 4 (`maclane:IV.6:ex4`)。所有目标所测量且自身未声明的内容都在这里固定，来自该文件之外，以便目标常量的重命名会破坏此探测器，而不是默默地将保护标记为绿色。上面的 `Require` 列表完全反映了目标的列表，加上目标本身。

三种类型的五个负面，通过错误文本区分：

1  转换  [Sets] 协议在整个 MORPHISMS 上不遵守 Leibniz 等价 —— 只在点上遵守
2  类型  [b] 中的天真函子作用类型不正确，这就是为什么在 [b] 中没有自然性方形
3  转换  该作用的两个候选 hom-TYPES 不同
4  转换  其 [fobj] 在其自身 [Program Definition] 内部展开的函子与任何东西都不转换
5  可形成性 [Cartesian] 识别一个范畴的 hom 和证明宇宙，这就是目标的绑定器 [Category@{u u0 u0}] 的来源

加上一个无范围限制的仪器检查。每个仪器一次拆解，单独编译，然后读取其全部错误。
*)

(*
Instrument check: a name that cannot exist must be rejected, so that no
   negative below can pass for the wrong reason.

--------
工具检查：一个不可能存在的名称必须被拒绝，以便下面的任何负面情况都不会因错误的原因而通过。
*)
Fail Check no_such_constant_exists_in_this_development.

(** ** Controls: every constant a negative names, outside any rejection / ** 控制：每个常数都是负名称，位于任何拒绝之外 *)

Check @internal_compose.
Check @internal_id.
Check @internal_compose_assoc.
Check @internal_compose_dinatural.
Check @internal_compose_natural_a.
Check @internal_compose_natural_c.
Check @internal_compose_Wedge.
Check @CCC_Enriched.
Check @Sets_Enriched.
Check @ExpBase.
Check @expBase_fobj.
Check @ComposeSrcC.
Check @composeSrcC_fobj.
Check @sets_internal_compose.
Check @sets_internal_compose_underlying.
Check @sets_internal_compose_morphism.
Check @sets_internal_id.
Check @ihom.
Check @Cartesian.
Check @Closed.
Check @split.
Check @fobj.
Check Sets.

(** ** Negative 1 (CONVERSION): the [Set] agreement is pointwise only / ** 负 1（转换）：[Set] 协议仅适用于点对点 *)

(*
The value at each point IS [g (f t)] on the nose -- that is the shipped
   [sets_internal_compose].  The two WHOLE morphisms of [Sets] are not
   Leibniz-equal: [SetoidMorphism] carries a [proper_morphism] certificate
   that the two sides build differently.  The two underlying FUNCTIONS do
   agree at [eq_refl] (control below), which locates the difference in the
   certificate and nowhere else.

--------
每一点的值正好是 [g (f t)] —— 也就是出厂的 [sets_internal_compose]。[Sets] 的两个整体态射并不是莱布尼茨相等的：[SetoidMorphism] 拥有一个 [proper_morphism] 证书，说明两边的构建不同。两个底层函数在 [eq_refl] 处确实一致（下面的控制），这说明差异仅存在于证书中，而不存在于其他任何地方。
*)

Example p391_ctrl_pointwise (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) (t : a) :
  @internal_compose Sets _ _ a b c (g, f) t = g (f t) := eq_refl.

Example p391_ctrl_underlying (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) :
  (fun t : a => @internal_compose Sets _ _ a b c (g, f) t)
    = (fun t : a => (g ∘[Sets] f) t) := eq_refl.

Example p391_ctrl_equiv (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) :
  @internal_compose Sets _ _ a b c (g, f) ≈[Sets] g ∘ f.
Proof. intro t; reflexivity. Qed.

Fail Example p391_neg1 (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) :
  (@internal_compose Sets _ _ a b c (g, f) : a ~{Sets}~> c) = g ∘ f
  := eq_refl.

Section ProbeGeneral.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

(** ** Negative 2 (TYPING): there is no functorial action in [b] / ** 负 2（打字）：在 [b] 中没有函子作用 *)

(*
In [c^b × b^a] the variable [b] is contravariant on the left and
   covariant on the right.  An arrow [f : b1 ~> b2] therefore acts on the
   two factors in OPPOSITE directions, and the resulting morphism runs
   between the MIXED objects [c^b2 × b1^a] and [c^b1 × b2^a] -- not
   between [c^b1 × b1^a] and [c^b2 × b2^a], which is what a functor of [b]
   would have to supply.  So this action does not give a functor of [b],
   and hence gives no [Transform] in [b] for a naturality square to live
   in; what holds instead is the cowedge condition
   [internal_compose_dinatural], controlled above and again here.

--------
在 [c^b × b^a] 中，变量 [b] 在左边是逆变的，在右边是协变的。因此，箭头 [f : b1 ~> b2] 对两个因子起作用的方向是相反的，结果的态射在混合对象 [c^b2 × b1^a] 和 [c^b1 × b2^a] 之间运行——而不是在 [c^b1 × b1^a] 和 [c^b2 × b2^a] 之间，这是 [b] 的函子必须提供的。因此，这种作用不会产生 [b] 的函子，因此在 [b] 中不会产生自然性方格所需的 [Transform]；取而代之的是上面和这里再次提到的牛楔条件 [internal_compose_dinatural]。
*)

(* The action, at the type it actually has. / 该动作，其实际类型。 *)
Example p391_ctrl_b_action (a c b1 b2 : C) (f : b1 ~{C}~> b2) :
  (c^b2 × b1^a) ~{C}~> (c^b1 × b2^a) :=
  split (ihom f id) (ihom id f).

(* The honest statement in [b], as a passing control. / 作为一个通过的控制，[b]中的诚实声明。 *)
Example p391_ctrl_dinatural (a c b1 b2 : C) (f : b1 ~{C}~> b2) :
  @internal_compose C _ _ a b1 c ∘ split (ihom f id) id
    ≈ @internal_compose C _ _ a b2 c ∘ split id (ihom id f)
  := internal_compose_dinatural f.

Fail Example p391_neg2 (a c b1 b2 : C) (f : b1 ~{C}~> b2) :
  (c^b1 × b1^a) ~{C}~> (c^b2 × b2^a) :=
  split (ihom f id) (ihom id f).

(** ** Negative 3 (CONVERSION): the two hom-types are not the same type / ** 负 3（转换）：两个同源类型不是同一种类型 *)

(*
Stated on the TYPES rather than on an inhabitant, so that no coercion
   can make it pass for the wrong reason.

--------
陈述在类型上，而不是在居民上，这样没有强制手段可以使其因为错误的原因而通过。
*)

Example p391_ctrl_type_refl (a c b1 b2 : C) :
  ((c^b2 × b1^a) ~{C}~> (c^b1 × b2^a))
    = ((c^b2 × b1^a) ~{C}~> (c^b1 × b2^a)) := eq_refl.

Fail Example p391_neg3 (a c b1 b2 : C) :
  ((c^b2 × b1^a) ~{C}~> (c^b1 × b2^a))
    = ((c^b1 × b1^a) ~{C}~> (c^b2 × b2^a)) := eq_refl.

(** ** Negative 4 (CONVERSION): the [Program]-elaborated [fobj] is opaque / ** 负4（转换）：由 [Program] 制作的 [fobj] 不透明 *)

(*
Structure/Cartesian/Closed/Natural.v records that writing the
   object action INSIDE a [Program Definition] lets [Program] defer an
   unresolved instance argument of [product_obj] into an obligation, which
   Lib/Foundation.v's [Unset Transparent Obligations] makes opaque; the
   resulting [fobj] then converts with nothing.  The target met that
   hazard again and elaborates its object actions first.

   The boundary is MEASURED here rather than assumed, and it is narrower
   than "any inline object action": [NaiveExpBase], whose object action is
   an [exponent_obj] alone, DOES reduce (control below), while
   [NaiveComposeSrcC], whose object action is a [product_obj], does not.
   What the two commands establish is that separation; that the deferred
   argument is [product_obj]'s is the donor's own attribution, quoted
   above and not re-derived here.

--------
Structure/Cartesian/Closed/Natural.v 记录了在 [Program Definition] 内部编写对象操作可以让 [Program] 将 [product_obj] 的未解决实例参数延迟为义务，而 Lib/Foundation.v 的 [Unset Transparent Obligations] 使其不透明；生成的 [fobj] 然后可以无转换地处理。目标再次遇到了该风险，并首先展开了其对象操作。

这里的边界是 MEASURED，而非假设的，并且它比“任何内联对象操作”更窄：[NaiveExpBase]，其对象操作仅为 [exponent_obj]，确实会减少（下方控制），而 [NaiveComposeSrcC]，其对象操作为 [product_obj]，则不会。两个命令所确立的是这种分离；延迟参数属于 [product_obj]，这是捐赠者自身的归属，如上文所引用，这里不再重新推导。
*)

Program Definition NaiveExpBase (a : C) : C ⟶ C := {|
  fobj := fun c => c^a;
  fmap := fun _ _ g => ihom id g
|}.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. apply ihom_id. Qed.
Next Obligation. rewrite ihom_comp; now rewrite id_left. Qed.

Program Definition NaiveComposeSrcC (a b : C) : C ⟶ C := {|
  fobj := fun c => c^b × b^a;
  fmap := fun _ _ g => first (ihom id g)
|}.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. rewrite ihom_id; apply first_id. Qed.
Next Obligation.
  rewrite <- first_comp, ihom_comp; now rewrite id_left.
Qed.

(* The target's functor, which does reduce ... / 目标的函子，它确实减少... *)
Example p391_ctrl_fobj (a b c : C) :
  fobj[ComposeSrcC a b] c = c^b × b^a := eq_refl.

(* ... and the exponent-only naive functor, which also does. / ... 以及仅指数的天真函子，它也如此。 *)
Example p391_ctrl_naive_exp (a c : C) :
  fobj[NaiveExpBase a] c = c^a := eq_refl.

Fail Example p391_neg4 (a b c : C) :
  fobj[NaiveComposeSrcC a b] c = c^b × b^a := eq_refl.

End ProbeGeneral.

(** ** Negative 5 (FORMABILITY): [Cartesian] identifies hom with proof / ** 负 5（可成型性）：[Cartesian] 使用证据识别同源 *)

(*
Every constant of the target is over [C : Category@{u u0 u0}] in its
   BINDER, while not one of its constraint BLOCKS contains a universe
   equation -- reading the blocks alone would report no identification.
   The identification is inherited, and [Cartesian] alone already forces
   it: at a category whose hom and proof universes are declared strictly
   apart the category itself, its objects, its hom-sets and its identities
   are all accepted, and only [Cartesian] is rejected.

--------
目标的每个常量在它的 BINDER 中都超过 [C : Category@{u u0 u0}]，而没有一个约束 BLOCK 包含宇宙方程——仅阅读这些块不会报告任何标识。标识是继承的，而 [Cartesian] 本身已经强制了它：在一个其 Hom 和证明宇宙被宣告严格分开的范畴中，该范畴自身、其对象、其 Hom 集合及其同一性都被接受，只有 [Cartesian] 被拒绝。
*)

Section ProbeUniverses.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).

Check obj[Cu].
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => id[x]).
Check (fun (x y z : Cu) (f : y ~{Cu}~> z) (g : x ~{Cu}~> y) => f ∘ g).

Fail Check (@Cartesian Cu).

End ProbeUniverses.
