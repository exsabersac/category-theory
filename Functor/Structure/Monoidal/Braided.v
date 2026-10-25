Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Id.
Require Import Category.Functor.Structure.Monoidal.Compose.

Generalizable All Variables.

(** * Braided and symmetric monoidal functors  / * 编织和对称幺半群函子*)

(*
nLab: https://ncatlab.org/nlab/show/braided+monoidal+functor
   nLab: https://ncatlab.org/nlab/show/symmetric+monoidal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_functor

   A monoidal functor F between braided monoidal categories C and D is
   BRAIDED when its tensor comparison commutes with the two braidings: for
   all x y, the square

       F x ⨂ F y --- braid^D ---> F y ⨂ F x
           |                          |
         μ_{x,y}                    μ_{y,x}
           ↓                          ↓
       F (x ⨂ y) -- F braid^C --> F (y ⨂ x)

   commutes.  Being braided is a PROPERTY of a (lax or strong) monoidal
   functor, not extra structure: no new data is involved beyond the single
   compatibility equation.  [BraidedLaxMonoidalFunctor] states it over the
   lax tensor comparison [lax_ap]; [BraidedMonoidalFunctor] states it over
   the strong comparison [ap_iso].  A braided monoidal functor between
   SYMMETRIC monoidal categories is called a symmetric monoidal functor;
   the condition is literally the same equation, so
   [SymmetricMonoidalFunctor] below is a definition, not a new class.

   The identity functor is braided monoidal, and braided monoidal functors
   compose (paste the outer compatibility square with the image of the
   inner one under the outer functor), so braided monoidal categories,
   braided (strong) monoidal functors, and monoidal natural transformations
   form a 2-category BrMonCat, with symmetric monoidal categories and
   symmetric monoidal functors as a full sub-2-category. 

--------
nLab：https://ncatlab.org/nlab/show/braided+monoidal+functor
 nLab：https://ncatlab.org/nlab/show/symmetric+monoidal+functor
 维基百科：https://en.wikipedia.org/wiki/Monoidal_functor

辫状幺半群类别 C 和 D 之间的幺半群函子 F 为
 当张量比较与两个编织进行交换时为 BRAIDED：
 所有 x y，平方

F x ⨂ F y --- 编织^D ---> F y ⨂ F x
 | |
 μ_{x,y} μ_{y,x}
 ↓ ↓
 F (x ⨂ y) -- F 编织^C --> F (y ⨂ x)

通勤。 编织是（松散或强）幺半群的一个属性
 函子，而不是额外的结构：除了单个数据之外，不涉及任何新数据
 相容方程。 [BraidedLaxMonoidalFunctor] 指出
 松弛张量比较 [lax_ap]； [BraidedMonoidalFunctor] 说明了这一点
 对比[ap_iso]强。 之间的编织幺半群函子
 对称幺半群范畴称为对称幺半群函子；
 条件实际上是相同的方程，所以
 下面的 [SymmetricMonoidalFunctor] 是一个定义，而不是一个新类。

恒等函子是辫状幺半群，而辫状幺半群函子
 撰写（将外部兼容性方块与图像粘贴在一起）
 内部函子位于外部函子之下），因此编织幺半群类别，
 编织（强）幺半群函子和幺半群自然变换
 形成一个 2 类 BrMonCat，具有对称幺半群类别，并且
 对称幺半群函子作为完整的子 2 范畴。 
*)

Section BraidedMonoidalFunctor.

Context {C D : Category}.
Context `{BC : @BraidedMonoidal C}.
Context `{BD : @BraidedMonoidal D}.
Context {F : C ⟶ D}.

(* Lax variant: F β ∘ μ ≈ μ ∘ β over the lax tensor comparison.  / Lax 变体：F β ∘ μ ≈ μ ∘ β 在松弛张量比较上。*)
Class BraidedLaxMonoidalFunctor : Type := {
  braided_is_lax : @LaxMonoidalFunctor C D _ _ F;

  lax_braid_compat {x y : C} :
    fmap[F] (@braid C _ x y) ∘ lax_ap
      ≈ lax_ap ∘ @braid D _ (F x) (F y)
}.
#[export] Existing Instance braided_is_lax.

Coercion braided_is_lax :
  BraidedLaxMonoidalFunctor >-> LaxMonoidalFunctor.

(* Strong variant: the same square over the invertible comparison.  / 强变体：同平方以上的可逆比较。*)
Class BraidedMonoidalFunctor : Type := {
  braided_is_strong : @MonoidalFunctor C D _ _ F;

  braid_compat {x y : C} :
    fmap[F] (@braid C _ x y) ∘ to ap_iso
      ≈ to ap_iso ∘ @braid D _ (F x) (F y)
}.
#[export] Existing Instance braided_is_strong.

Coercion braided_is_strong :
  BraidedMonoidalFunctor >-> MonoidalFunctor.

(*
A braided strong monoidal functor is in particular braided lax monoidal:
   forgetting invertibility of the comparisons preserves the compatibility
   square, since the lax comparison of [MonoidalFunctor_Is_Lax] is the [to]
   component of [ap_iso]. 

--------
编织的强幺半群函子特别是编织的松散幺半群：
 忘记比较的可逆性保留了兼容性
 方形，因为 [MonoidalFunctor_Is_Lax] 的松散比较是 [to]
 [ap_iso] 的组件。 
*)
Program Definition BraidedMonoidalFunctor_Is_Lax
  (S : BraidedMonoidalFunctor) : BraidedLaxMonoidalFunctor := {|
  braided_is_lax := MonoidalFunctor_Is_Lax braided_is_strong
|}.
Next Obligation. apply braid_compat. Qed.

End BraidedMonoidalFunctor.

Arguments BraidedLaxMonoidalFunctor {C D _ _} F.
Arguments BraidedMonoidalFunctor {C D _ _} F.

(*
Over symmetric bases the braided compatibility IS the symmetric
   condition — a symmetric monoidal functor is just a braided monoidal
   functor between symmetric monoidal categories, with no new data or
   axioms (nLab: symmetric+monoidal+functor).  The braided structures are
   selected through the [symmetric_is_braided] instances. 

--------
在对称基础上，编织兼容性是对称的
 条件 — 对称幺半群函子只是一个编织幺半群
 对称幺半群类别之间的函子，没有新数据或
 公理（nLab：对称+幺半群+函子）。 编织结构是
 通过 [symmetric_is_braided] 实例选择。 
*)
Definition SymmetricMonoidalFunctor {C D : Category}
  `{@SymmetricMonoidal C} `{@SymmetricMonoidal D} (F : C ⟶ D) : Type :=
  @BraidedMonoidalFunctor C D _ _ F.

Definition SymmetricLaxMonoidalFunctor {C D : Category}
  `{@SymmetricMonoidal C} `{@SymmetricMonoidal D} (F : C ⟶ D) : Type :=
  @BraidedLaxMonoidalFunctor C D _ _ F.

(** ** The identity functor is braided monoidal  / ** 恒等函子是编织幺半群*)

(*
Both comparison maps of [Id_MonoidalFunctor] are identities, so the
   compatibility square degenerates to braid ∘ id ≈ id ∘ braid. 

--------
[Id_MonoidalFunctor] 的两个比较图都是恒等式，因此
 兼容性方退化为 braid ∘ id ≈ id ∘ braid。 
*)

Section BraidedMonoidalId.

Context {C : Category}.
Context `{BC : @BraidedMonoidal C}.

#[export] Program Instance Id_BraidedMonoidalFunctor :
  BraidedMonoidalFunctor (Id[C]) := {
  braided_is_strong := Id_MonoidalFunctor
}.

#[export] Program Instance Id_BraidedLaxMonoidalFunctor :
  BraidedLaxMonoidalFunctor (Id[C]) := {
  braided_is_lax := Id_LaxMonoidalFunctor
}.

End BraidedMonoidalId.

(** ** Braided monoidal functors compose  / ** 编织幺半群函子组成*)

(*
The composite comparison of [Compose_MonoidalFunctor] is
   fmap[G] μ^F ∘ μ^G (G outer, F inner).  Its compatibility square is the
   pasting of the outer square (for G, at F x and F y) with the image
   under fmap[G] of the inner square (for F, at x and y). 

--------
[Compose_MonoidalFunctor]的综合比较是
 fmap[G] μ^F ∘ μ^G（G 外，F 内）。 其相容平方为
 将外部正方形（对于 G，在 F x 和 F y 处）与图像粘贴
 在内部正方形的 fmap[G] 下（对于 F，在 x 和 y 处）。 
*)

Section BraidedMonoidalCompose.

Context {C D E : Category}.
Context `{BC : @BraidedMonoidal C}.
Context `{BD : @BraidedMonoidal D}.
Context `{BE : @BraidedMonoidal E}.
Context {G : D ⟶ E}.
Context {F : C ⟶ D}.

#[export] Program Instance Compose_BraidedMonoidalFunctor
  `{@BraidedMonoidalFunctor D E BD BE G}
  `{@BraidedMonoidalFunctor C D BC BD F} :
  BraidedMonoidalFunctor (G ◯ F) := {
  braided_is_strong := Compose_MonoidalFunctor braided_is_strong
                                               braided_is_strong
}.
Next Obligation.
  (*
Goal: fmap[G] (fmap[F] braid) ∘ (fmap[G] μ^F ∘ μ^G)
             ≈ (fmap[G] μ^F ∘ μ^G) ∘ braid. 

--------
目标：fmap[G] (fmap[F] 辫子) ∘ (fmap[G] μ^F ∘ μ^G)
 ≈ (fmap[G] μ^F ∘ μ^G) ∘ 辫子。 
*)
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  spose (@braid_compat C D BC BD F _ x y) as XF.
  rewrites.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  spose (@braid_compat D E BD BE G _ (F x) (F y)) as XG.
  rewrites.
  now rewrite comp_assoc.
Qed.

#[export] Program Instance Compose_BraidedLaxMonoidalFunctor
  `{@BraidedLaxMonoidalFunctor D E BD BE G}
  `{@BraidedLaxMonoidalFunctor C D BC BD F} :
  BraidedLaxMonoidalFunctor (G ◯ F) := {
  braided_is_lax := Compose_LaxMonoidalFunctor braided_is_lax
                                               braided_is_lax
}.
Next Obligation.
  unfold lax_ap; simpl.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  spose (@lax_braid_compat C D BC BD F _ x y) as XF.
  rewrites.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  spose (@lax_braid_compat D E BD BE G _ (F x) (F y)) as XG.
  rewrites.
  now rewrite comp_assoc.
Qed.

End BraidedMonoidalCompose.

(*
The bridge packaging a symmetric (strong) monoidal functor that
   preserves the SCFA generators as a weakened Fong–Spivak hypergraph
   functor, [SymmetricMonoidalFunctor_HypergraphFunctor], lives in
   Functor/Structure/Monoidal/Hypergraph.v, keeping this class file
   independent of the Frobenius/hypergraph chain. 

--------
该桥封装了一个对称（强）幺半群函子
 保留 SCFA 生成器作为弱化的 Fong-Spivak 超图
 函子 [SymmetricMonoidalFunctor_HypergraphFunctor] 位于
 Functor/Structure/Monoidal/Hypergraph.v，保留此类文件
 独立于 Frobenius/hypergraph 链。 
*)
