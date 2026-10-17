Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Naturality.
Require Import Category.Functor.Construction.Product.

Generalizable All Variables.

(** Strong functors (functors with a tensorial strength) *)

(* nLab: https://ncatlab.org/nlab/show/tensorial+strength
   Wikipedia: https://en.wikipedia.org/wiki/Strong_monad

   强函子是幺半范畴 (C, ⊗, I) 上配备张量（左）强度的自函子 F : C ⟶ C：自然族

     strength[x,y] : x ⨂ F y ~> F (x ⨂ y)          （左强度）

   服从两条与幺半结构相关的连贯定律。库记号中写 λ = [unit_left]、α = [tensor_assoc]：

     - 单位：F(λ) ∘ strength[I,x]                 ≈ λ_{F x}    ([strength_id_left])
     - 结合：F(α) ∘ strength[x⨂y,z]
                ≈ strength[x,y⨂z] ∘ (id ⨂ strength[y,z]) ∘ α    ([strength_assoc])

   这是 Kock 的两条件；此类族与强度的对应即「张量强度」之名的依据（Kock 1972,
   "Strong functors and monoidal monads"）。对偶 [RightStrongFunctor] 携带右强度
   F x ⨂ y ~> F (x ⨂ y)，镜像定律经 ρ = [unit_right] 与 α⁻¹ 陈述。在对称幺半 C 上两强度
   可经辫互推，且重合。

   此处「强」指张量强度，*不是*「强（即伪）幺半函子」；两概念无关。在闭幺半 C 上强度
   等价于 F 的 C-充实；单子底层函子上（与 η、μ 相容）的强度恰是内化 Kleisli 复合所需，
   从而得到强单子。 *)

Class StrongFunctor `{@Monoidal C} (F : C ⟶ C) := {
  strength {x y} : x ⨂ F y ~> F (x ⨂ y);          (* left strength A ⨂ FB ~> F(A ⨂ B) *)
  strength_natural : natural (@strength);          (* natural in both arguments *)

  strength_id_left {x} :                           (* unit law: F(λ) ∘ str ≈ λ *)
    fmap[F] (to unit_left) ∘ strength
      << I ⨂ F x ~~> F x >>
    to (@unit_left _ _ (F x));

  strength_assoc {x y z} :                          (* associativity law w.r.t. α *)
    fmap[F] (to (@tensor_assoc _ _ x y z)) ∘ strength
      << (x ⨂ y) ⨂ F z ~~> F (x ⨂ y ⨂ z) >>
    strength ∘ bimap id strength ∘ to (@tensor_assoc _ _ x y (F z))
}.

Class RightStrongFunctor `{@Monoidal C} (F : C ⟶ C) := {
  rstrength_nat : (⨂) ◯ F ∏⟶ Id ⟹ F ◯ (⨂);        (* right strength as a natural transformation *)

  rstrength {x y} : F x ⨂ y ~> F (x ⨂ y) := transform[rstrength_nat] (x, y);

  rrstrength_id_right {x} :                          (* unit law: F(ρ) ∘ rstr ≈ ρ *)
    fmap[F] (to unit_right) ∘ rstrength ≈ to (@unit_right _ _ (F x));
  rstrength_assoc {x y z} :                          (* associativity law w.r.t. α⁻¹ *)
    rstrength ∘ bimap rstrength id ∘ from (@tensor_assoc _ _ (F x) y z)
      ≈ fmap[F] (from (@tensor_assoc _ _ x y z)) ∘ rstrength
}.

Section Strong.

Context `{@Monoidal C}.
Context {F : C ⟶ C}.

(* The identity functor is strong, with the identity as its strength. *)
#[export] Program Instance Id_StrongFunctor : StrongFunctor Id[C] := {
  strength := fun _ _ => id
}.

#[local] Obligation Tactic := program_simpl.

(* Strong functors are closed under composition: the strength of F ◯ G is
   built by first sliding through G, then lifting that through F's strength. *)
#[export] Program Instance Compose_StrongFunctor (F G : C ⟶ C) :
  StrongFunctor F → StrongFunctor G → StrongFunctor (F ◯ G) := {
  strength := fun _ _ => fmap[F] strength ∘ strength
}.
Next Obligation.
  repeat match reverse goal with [ H : StrongFunctor _ |- _ ] => destruct H end; simpl in *.
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (strength0 _ _)).
  rewrite <- strength_natural0; clear strength_natural0.
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- strength_natural1; clear strength_natural1.
  rewrite <- fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  repeat match reverse goal with [ H : StrongFunctor _ |- _ ] => destruct H end; simpl in *.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite strength_id_left1.
  apply strength_id_left0.
Qed.
Next Obligation.
  repeat match reverse goal with [ H : StrongFunctor _ |- _ ] => destruct H end; simpl in *.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite strength_assoc1.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite strength_assoc0.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  specialize (strength_natural0
                x x (id[x]) (y ⨂ G z)%object (G (y ⨂ z))%object
                (strength1 y z)).
  rewrite !bimap_id_id in strength_natural0.
  rewrite !fmap_id in strength_natural0.
  rewrite !id_right in strength_natural0.
  rewrite strength_natural0.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite comp_assoc.
  apply compose_respects; [|reflexivity].
  rewrite <- bimap_comp.
  apply fmap_respects.
  split; simpl; cat.
Qed.

End Strong.

(* [strength[F]] names the strength of a given strong functor F at implicit
   arguments, mirroring the [fmap[F]] convention. *)
Notation "strength[ F ]" := (@strength _ _ F%functor _ _ _)
  (at level 9, format "strength[ F ]") : morphism_scope.
