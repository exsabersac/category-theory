Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.

Generalizable All Variables.

(** The identity functor is monoidal.  / 恒等函子是幺半群的。*)

(*
nLab: https://ncatlab.org/nlab/show/monoidal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_functor

   The identity functor Id[C] on a monoidal category C is canonically a strong
   (indeed strict) monoidal functor.  Because Id x = x on the nose, the two
   comparison maps are identities,

       η     = id : I ~> Id I        (unit comparison, here pure_iso = iso_id),
       μ_x_y = id : Id x ⨂ Id y ~> Id (x ⨂ y)   (tensor comparison),

   so both are trivially invertible (strong) and equal to identities (strict).
   The three coherence squares — left and right unitality against λ and ρ, and
   associativity against the associator α — collapse to the monoidal axioms of
   C itself, discharged below by tensor_assoc and bimap_id_id.  This instance
   is the unit of the 2-category MonCat of monoidal categories and (strong)
   monoidal functors.  [Id_MonoidalFunctor] gives the strong form and
   [Id_LaxMonoidalFunctor] the lax form, both axiom-free. 

--------
nLab：https://ncatlab.org/nlab/show/monoidal+functor
 维基百科：https://en.wikipedia.org/wiki/Monoidal_functor

 幺半群类别 C 上的恒等函子 Id[C] 是典型的强函数
 （实际上是严格的）幺半群函子。 因为Id x = x在鼻子上，所以两个
 比较图是身份，

 η = id : I ~> Id I（单位比较，这里pure_iso = iso_id），
 μ_x_y = id : Id x ⨂ Id y ~> Id (x ⨂ y) （张量比较），

 所以两者都是可逆的（强）并且等于恒等式（严格）。 
三个相干平方——针对 λ 和 ρ 的左右单位性，以及
 与关联子 α 相关的结合性 — 崩溃为幺半群公理
 C本身，由tensor_assoc和bimap_id_id在下面释放。 本实例
 是幺半群类别的 2 类别 MonCat 的单位，并且（强）
 幺半群函子。 [Id_MonoidalFunctor] 赋予坚固的形状和
 [Id_LaxMonoidalFunctor] 宽松形式，两者均无公理。 
*)

Section MonoidalFunctors.

Context {C : Category}.
Context `{@Monoidal C}.
Context {D : Category}.
Context `{@Monoidal D}.
Context {G : C ⟶ D}.

Context {E : Category}.
Context `{@Monoidal E}.
Context {F : D ⟶ E}.

#[local] Obligation Tactic := program_simpl.

#[export] Program Instance Id_MonoidalFunctor :
  @MonoidalFunctor C C _ _ Id[C] := {
  pure_iso := iso_id;
  ap_functor_iso := {| to   := {| transform := fun _ => _ |}
                     ; from := {| transform := fun _ => _ |} |}
}.
Next Obligation.
  simpl; intros.
  destruct H0; simpl.
  exact id.
Defined.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation.
  simpl; intros.
  destruct H1; simpl.
  exact id.
Defined.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. apply tensor_assoc. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite !bimap_id_id; cat. Qed.

#[export] Program Instance Id_LaxMonoidalFunctor :
  @LaxMonoidalFunctor C C _ _ Id[C] := {
  lax_pure := id;
  ap_functor_nat := {| transform := fun _ => _ |}
}.
Next Obligation.
  simpl; intros.
  destruct H0; simpl.
  exact id.
Defined.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. simpl; intros; simplify; cat. Qed.
Next Obligation. apply tensor_assoc. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite bimap_id_id; cat. Qed.
Next Obligation. rewrite !bimap_id_id; cat. Qed.

End MonoidalFunctors.
