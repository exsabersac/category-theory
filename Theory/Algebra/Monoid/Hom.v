Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.

Generalizable All Variables.

(** * Monoid homomorphisms and the category of internal monoids / * 幺半群同态与内部幺半群范畴 *)

(*
nLab: https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category

   Given internal monoids (x, mu[Mx], eta[Mx]) and (y, mu[My], eta[My]) in a
   monoidal category (C, ⨂, I), a morphism f : x ~> y is a monoid
   homomorphism when it commutes with the multiplications and units:

     multiplication square   f ∘ mu[Mx] ≈ mu[My] ∘ (f ⨂ f)
     unit triangle           f ∘ eta[Mx] ≈ eta[My]

   Monoid homomorphisms contain the identities and are closed under
   composition, so internal monoids and their homomorphisms form a category
   Mon(C), packaged here with sigma objects and homs — the same pattern as
   [Sub] in Construction/Subcategory.v, where morphism equivalence is
   equivalence of the underlying C-morphisms.  Projecting out the underlying
   object and morphism gives the forgetful functor Mon(C) ⟶ C, faithful by
   construction ([Mon_Forget_Faithful]).

--------
nLab: https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category

在一个幺半范畴 (C, ⨂, I) 中，给定内部幺半群 (x, mu[Mx], eta[Mx]) 和 (y, mu[My], eta[My])，一个态射 f : x ~> y 是一个幺半群同态，当且仅当它与乘法和单位交换：

  乘法方形   f ∘ mu[Mx] ≈ mu[My] ∘ (f ⨂ f)
  单位三角   f ∘ eta[Mx] ≈ eta[My]

幺半群同态包含恒等态射并在复合下封闭，因此内部幺半群及其同态构成一个范畴 Mon(C)，这里与 σ 对象和 homs 一起打包——这与 Construction/Subcategory.v 中的 [Sub] 模式相同，其中态射等价是基础 C-态射的等价。投射出基础对象和态射得到遗忘函子 Mon(C) ⟶ C，根据构造它是忠实的 ([Mon_Forget_Faithful])。
*)

Section MonoidHom.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class MonoidHom {x y : C} (Mx : Monoid x) (My : Monoid y) (f : x ~> y) :
  Type := {
  (* f preserves multiplication: f ∘ mu[Mx] ≈ mu[My] ∘ (f ⨂ f) / f 保持乘法：f ∘ mu[Mx] ≈ mu[My] ∘ (f ⨂ f) *)
  hom_mu  : f ∘ mu[Mx] ≈ mu[My] ∘ (f ⨂ f);
  (* f preserves the unit: f ∘ eta[Mx] ≈ eta[My] / f 保持单位：f ∘ eta[Mx] ≈ eta[My] *)
  hom_eta : f ∘ eta[Mx] ≈ eta[My]
}.

(* The identity is a monoid homomorphism. / 该恒等映射是一个幺半群同态。 *)
Lemma MonoidHom_id {x} (Mx : Monoid x) : MonoidHom Mx Mx id.
Proof. split; cat. Qed.

(*
Monoid homomorphisms are closed under composition: paste the two
   preservation squares, fusing (f ⨂ f) ∘ (g ⨂ g) into (f ∘ g) ⨂ (f ∘ g)
   by the interchange law [bimap_comp].

--------
幺半群同态在复合运算下是封闭的：将两个保持图拼接，将 (f ⨂ f) ∘ (g ⨂ g) 通过交换律 [bimap_comp] 融合为 (f ∘ g) ⨂ (f ∘ g)。
*)
Lemma MonoidHom_comp {x y z} {Mx : Monoid x} {My : Monoid y} {Mz : Monoid z}
      {f : y ~> z} {g : x ~> y} :
  MonoidHom My Mz f → MonoidHom Mx My g → MonoidHom Mx Mz (f ∘ g).
Proof.
  intros F G.
  split.
  - rewrite <- comp_assoc.
    rewrite (@hom_mu _ _ _ _ _ G).
    rewrite comp_assoc.
    rewrite (@hom_mu _ _ _ _ _ F).
    rewrite <- comp_assoc.
    now rewrite <- bimap_comp.
  - rewrite <- comp_assoc.
    rewrite (@hom_eta _ _ _ _ _ G).
    apply (@hom_eta _ _ _ _ _ F).
Qed.

(* Being a monoid homomorphism transports along ≈ (bimap respects ≈). / 作为一个幺半群同态沿 ≈ 传递（双映射尊重 ≈）。 *)
Lemma MonoidHom_equiv {x y} {Mx : Monoid x} {My : Monoid y} {f g : x ~> y} :
  f ≈ g → MonoidHom Mx My f → MonoidHom Mx My g.
Proof.
  intros E F.
  split.
  - rewrite <- E.
    apply (@hom_mu _ _ _ _ _ F).
  - rewrite <- E.
    apply (@hom_eta _ _ _ _ _ F).
Qed.

(*
The category Mon(C) of internal monoids in C: objects are objects of C
   equipped with a monoid structure, morphisms are C-morphisms equipped with
   a proof of homomorphy, and equivalence is equivalence of the underlying
   morphisms — exactly the sigma packaging of [Sub] in
   Construction/Subcategory.v.

--------
C 中内部单子的范畴 Mon(C)：对象是带有单子结构的 C 对象，态射是带有同态性证明的 C 态射，且等价性是基础态射的等价性——完全相当于 Construction/Subcategory.v 中 [Sub] 的 sigma 封装。
*)
Program Definition Mon : Category := {|
  obj     := { x : C & Monoid x };
  hom     := fun X Y => { f : `1 X ~> `1 Y & MonoidHom `2 X `2 Y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun X => (id; MonoidHom_id `2 X);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; MonoidHom_comp `2 f `2 g)
|}.

(*
The forgetful functor Mon(C) ⟶ C projects out the underlying object and
   morphism; it is faithful by construction ([Mon_Forget_Faithful] below).

--------
遗忘函子 Mon(C) ⟶ C 投射出其底层对象和态射；它由构造决定是忠实的（见下文 [Mon_Forget_Faithful]）。
*)
Program Definition Mon_Forget : Mon ⟶ C := {|
  fobj := fun X => `1 X;
  fmap := fun _ _ f => `1 f
|}.

(*
Faithfulness is definitional: morphism equivalence in Mon(C) IS
   equivalence of the underlying C-morphisms, which is what [fmap] projects
   out.

--------
忠实性是定义性的：Mon(C)中的态射等价就是底层C-态射的等价，这正是[fmap]投射出的内容。
*)
#[export] Instance Mon_Forget_Faithful : Faithful Mon_Forget.
Proof.
  constructor.
  intros X Y f g E.
  exact E.
Qed.

End MonoidHom.

Arguments Mon C {M}.
