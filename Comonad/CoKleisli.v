Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Kleisli.
Require Import Category.Comonad.Core.

Generalizable All Variables.

(* * * The co-Kleisli 范畴 余单子 （已译） *)

(* nLab:      https://ncatlab.org/nlab/show/co-Kleisli+category
   Wikipedia: https://en.wikipedia.org/wiki/Kleisli_category

   范畴 C 上余单子 (W, extract, duplicate) = (W, ε, δ) 的 co-Kleisli 范畴 C_W 与 C
   有相同对象，而 co-Kleisli 态射 x ⇸ y 是普通 C-态射 W x ~> y。x 上的恒等是余单位
   extract（ε_x），f : W y ~> z 在 g : W x ~> y 之后的 co-Kleisli 复合是

       f ∘_W g  ≈  f ∘ fmap[W] g ∘ duplicate    (f ∘ W g ∘ δ),

   恰是 f 复合到 g 的扩展上（f ∘ extend g）。

   因 [Comonad C W] 按定义是 [@Monad (C^op) (W^op)]，co-Kleisli 范畴此处取为该对偶单子的
   Kleisli 范畴的对偶，而非重证范畴定律：

       CoKleisli := (Kleisli (C^op) (W^op))^op

   因对偶使 C^op^op = C 由 reflexivity 成立，此构造的共变分量定义上即所期望：hom 集字面上是
   W x ~{C}~> y（[cokleisli_hom]），恒等字面上是 [extract]，范畴复合 [cokleisli_compose f g]
   字面上是 f ∘ extend g。范畴定律由 Monad/Kleisli.v 经对偶继承，共变重读为 Comonad/Core.v
   的 co-Kleisli 三定律。 *)

(*
   nLab:  https://ncatlab.org/nlab/show/exponential+modality
   Paper: Uustalu, Vene, "The Essence of Dataflow Programming", APLAS
   Paper: Petricek, Orchard, Mycroft, "Coeffects: a calculus of

   本节说明余单子、Kleisli、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CoKleisli.

Context {C : Category} {W : C ⟶ C} {H : @Comonad C W}.

Definition CoKleisli : Category := (@Kleisli (C^op) (W^op) H)^op.

(** The hom-sets co-Kleisli 范畴 definitionally the
 covariant hom-sets [W x ~> y] base 范畴. （已译） *)
Lemma cokleisli_hom (x y : C) : (x ~{CoKleisli}~> y) = (W x ~{C}~> y).
Proof. reflexivity. Qed.

(** The 恒等 at x counit ε_x. （已译） *)
Lemma cokleisli_id {x : C} : @id CoKleisli x ≈ @extract C W H x.
Proof. reflexivity. Qed.

Definition cokleisli_compose `(f : W b ~{C}~> c) `(g : W a ~{C}~> b) :
  W a ~{C}~> c := @compose CoKleisli a b c f g.

(*
   本节说明单子、余单子、Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Notation "f =>= g" :=
  (cokleisli_compose g f) (at level 40, left associativity) : morphism_scope.
Notation "f =<= g" :=
  (cokleisli_compose f g) (at level 40, left associativity) : morphism_scope.

(*
   本节说明余单子、Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cokleisli_compose_extend `(f : W a ~{C}~> b) `(g : W b ~{C}~> c) :
  f =>= g ≈ g ∘ extend f.
Proof. reflexivity. Qed.

Corollary cokleisli_compose_extend_flip
  `(f : W b ~{C}~> c) `(g : W a ~{C}~> b) :
  f =<= g ≈ f ∘ extend g.
Proof. reflexivity. Qed.

(*
   本节说明单子、余单子、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Corollary comonad_id_left `(f : W x ~{C}~> y) : extract =>= f ≈ f.
Proof. unfold cokleisli_compose; cat. Qed.

Corollary comonad_id_right `(f : W x ~{C}~> y) : f =>= extract ≈ f.
Proof. unfold cokleisli_compose; cat. Qed.

Corollary comonad_comp_assoc `(f : W x ~{C}~> y) `(g : W y ~{C}~> z)
  `(h : W z ~{C}~> w) : f =>= (g =>= h) ≈ (f =>= g) =>= h.
Proof. exact (@comp_assoc_sym CoKleisli x y z w h g f). Qed.

End CoKleisli.

Notation "f =>= g" :=
  (cokleisli_compose g f)
  (at level 40, left associativity) : morphism_scope.
Notation "f =<= g" :=
  (cokleisli_compose f g)
  (at level 40, left associativity) : morphism_scope.

(* Explicit-endofunctor forms, the robust fallback when higher-order
   unification cannot infer [W] through the bare [=>=]/[=<=] holes
   (Monad/Kleisli.v exports the analogous [>=[ M ]=>]/[<=[ M ]=<]). *)
Notation "f =>[ W ]=> g" := (@cokleisli_compose _ W _ _ _ g _ f)
  (at level 40, left associativity) : morphism_scope.
Notation "f =<[ W ]=< g" := (@cokleisli_compose _ W _ _ _ f _ g)
  (at level 40, left associativity) : morphism_scope.
