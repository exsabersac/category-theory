Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Strong.
Require Import Category.Functor.Structure.Monoidal.

Generalizable All Variables.

(** The applicative [pure] from a strong lax monoidal functor.  / 来自强松散幺半群函子的应用 [pure]。*)

(*
nLab: https://ncatlab.org/nlab/show/applicative+functor
   Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor

   For a strong lax monoidal endofunctor F on a monoidal category, the unit
   comparison lax_pure : I ~> F I and the tensorial strength combine into the
   point operation pure : A ~> F A.  This is the categorical source of the
   Haskell [Applicative] method pure : a -> F a (McBride and Paterson,
   “Applicative programming with effects”, JFP 18(1), 2008).

   Following nLab, pure[A] is the composite (read right to left, with ρ the
   right unitor unit_right, ε = lax_pure the unit comparison and st = strength)

       A  --ρ⁻¹-->  A ⨂ I  --id ⨂ ε-->  A ⨂ F I
          --st-->  F (A ⨂ I)  --F ρ-->  F A,

   i.e. pure ≈ fmap unit_right ∘ strength ∘ (id ⨂ lax_pure) ∘ unit_right⁻¹.
   The right unitor is used here, matching the nLab presentation; the left
   unitor would give the mirror-image construction. 

--------
nLab：https://ncatlab.org/nlab/show/applicative+functor
 维基百科：https://en.wikipedia.org/wiki/Applicative_functor

 对于幺半群范畴上的强松弛幺半群内函子 F，单位
 比较 lax_pure : I ~> F I 和张量强度合并为
 纯点操作：A ~> F A。这是
 Haskell [Applicative] 方法 pure : a -> F a (McBride 和 Paterson,
 “具有效果的应用程序编程”，JFP 18(1)，2008）。 

在 nLab 之后，pure[A] 是复合材料（从右到左阅读，其中 ρ 为
 右单位unit_right，ε = lax_pure 单位比较，st = 强度）

 A --ρ⁻1--> A ⨂ I --id ⨂ ε--> A ⨂ F I
 --st--> F (A ⨂ I) --F ρ--> F A,

 即纯 ≈ fmap unit_right ∘ 强度 ∘ (id ⨂ lax_pure) ∘ unit_right⁻¹。 
这里使用了正确的单位器，与 nLab 演示相匹配； 左边
 unitor 会给出镜像结构。 
*)

Section Pure.

Context {C : Category}.
Context `{@Monoidal C}.
Context {F : C ⟶ C}.
Context `{@StrongFunctor C _ F}.
Context `{@LaxMonoidalFunctor C C _ _ F}.

Definition pure {A} : A ~> F A :=
  fmap unit_right ∘ strength ∘ id[A] ⨂ lax_pure ∘ unit_right⁻¹.

(* pure is natural in A: it is a natural transformation Id ⟹ F.  / pure 在 A 中是自然的：它是自然变换 Id ⟹ F。*)
Lemma pure_natural : natural (@pure).
Proof.
  simpl; intros.
  unfold pure.
  normal.
  rewrite to_unit_right_natural.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  spose (strength_natural _ _ g I I id) as X.
  normal.
  rewrites.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite <- from_unit_right_natural.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  normal.
  rewrite fmap_id; cat.
Qed.

(* The naturality square of pure as a rewrite: fmap f commutes past pure.  / pure 的自然性平方作为重写：fmap f 通勤过去 pure。*)
Lemma fmap_pure {a b} (f : a ~> b) : pure ∘ f ≈ fmap f ∘ pure.
Proof.
  symmetry.
  sapply pure_natural.
Qed.

End Pure.

Arguments pure {C _ F _ _ A}.

Notation "pure[ F ]" := (@pure _ _ F _ _ _)
  (at level 0, format "pure[ F ]") : morphism_scope.
