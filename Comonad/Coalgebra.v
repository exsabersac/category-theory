Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Comonad.Core.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(* * * Coalgebras over 余单子; co-Eilenberg–Moore 范畴 （已译） *)

(* nLab:      https://ncatlab.org/nlab/show/coalgebra+over+a+comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   对范畴 C 上的余单子 (W, extract, duplicate) = (W, ε, δ)——共变 API 见 Comonad/Core.v——
   对象 a 上的 W-余代数是余结构映射 γ : a ~> W a（[w_coalg]），服从余单位律 ε ∘ γ ≈ id
   （[w_counit_law]）与余作用律 W γ ∘ γ ≈ δ ∘ γ（[w_coaction]）。W-余代数态射
   (a, γ^a) ~> (b, γ^b) 是交织余结构映射的 C-态射 f : a ~> b，
   γ^b ∘ f ≈ W f ∘ γ^a（[w_coalg_hom_commutes]）。

   因 [Comonad C W] 按定义是 [@Monad (C^op) (W^op)]（Theory/Monad.v），W-余代数恰是该对偶
   单子的 Eilenberg–Moore 代数（[TAlgebra]，Monad/Algebra.v），W-余代数范畴——co-Eilenberg–Moore
   范畴 C_W——此处对偶于 Monad/Eilenberg/Moore.v，取为对偶单子的 Eilenberg–Moore 范畴的对偶：

       CoEilenbergMoore := (EilenbergMoore (W^op))^op

   因对偶使 C^op^op = C 由 reflexivity 成立，两呈现定义上一致；共变范畴 [WCoalgebras]
   在 Cat 中同构于 [CoEilenbergMoore]。 *)

(*
   nLab:  https://ncatlab.org/nlab/show/comonadic+functor
   nLab:  https://ncatlab.org/nlab/show/store+comonad
   Paper: O'Connor, "Functor is to Lens as Applicative is to Biplate:
   Paper: Bénabou, Roubaud, "Monades et descente", C. R. Acad. Sc. Paris,

   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明 Coalgebra 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class WCoalgebra {C : Category} (W : C ⟶ C) {H : @Comonad C W} (a : C) := {
  w_coalg : a ~> W a;

  w_counit_law : @extract C W H a ∘ w_coalg ≈ id;
  w_coaction :
    fmap[W] w_coalg ∘ w_coalg ≈ @duplicate C W H a ∘ w_coalg
}.

Notation "w_coalg[ F ]" := (@w_coalg _ _ _ _ F)
  (at level 9, format "w_coalg[ F ]") : morphism_scope.

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class WCoalgebraHom {C : Category} (W : C ⟶ C) {H : @Comonad C W}
      (a b : C) (F : @WCoalgebra C W H a) (G : @WCoalgebra C W H b) := {
  w_coalg_hom : a ~> b;

  w_coalg_hom_commutes :
    w_coalg[G] ∘ w_coalg_hom ≈ fmap[W] w_coalg_hom ∘ w_coalg[F]
}.

Notation "w_coalg_hom[ f ]" := (@w_coalg_hom _ _ _ _ _ _ _ f)
  (at level 9, format "w_coalg_hom[ f ]") : morphism_scope.

Section CoEilenbergMoore.

Context {C : Category} {W : C ⟶ C} {H : @Comonad C W}.

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition WCoalgebra_to_TAlgebra {a : C} (F : @WCoalgebra C W H a) :
  @TAlgebra (C^op) (W^op) H a :=
  @Build_TAlgebra (C^op) (W^op) H a
    (@w_coalg C W H a F)
    (@w_counit_law C W H a F)
    (@w_coaction C W H a F).

Definition TAlgebra_to_WCoalgebra {a : C} (F : @TAlgebra (C^op) (W^op) H a) :
  @WCoalgebra C W H a :=
  @Build_WCoalgebra C W H a
    (@t_alg (C^op) (W^op) H a F)
    (@t_id (C^op) (W^op) H a F)
    (@t_action (C^op) (W^op) H a F).

(** 本节：The costructure map untouched round trip (and likewise the
 other direction): conversions repackage fields. （已译） *)

Lemma WCoalgebra_to_TAlgebra_alg {a : C} (F : @WCoalgebra C W H a) :
  t_alg[WCoalgebra_to_TAlgebra F] ≈ w_coalg[F].
Proof. reflexivity. Qed.

Lemma TAlgebra_to_WCoalgebra_coalg {a : C} (F : @TAlgebra (C^op) (W^op) H a) :
  w_coalg[TAlgebra_to_WCoalgebra F] ≈ t_alg[F].
Proof. reflexivity. Qed.

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition WCoalgebraHom_to_TAlgebraHom {a b : C}
  {F : @WCoalgebra C W H a} {G : @WCoalgebra C W H b}
  (f : @WCoalgebraHom C W H a b F G) :
  @TAlgebraHom (C^op) (W^op) H b a
    (WCoalgebra_to_TAlgebra G) (WCoalgebra_to_TAlgebra F) :=
  @Build_TAlgebraHom (C^op) (W^op) H b a
    (WCoalgebra_to_TAlgebra G) (WCoalgebra_to_TAlgebra F)
    (@w_coalg_hom C W H a b F G f)
    (@w_coalg_hom_commutes C W H a b F G f).

Definition TAlgebraHom_to_WCoalgebraHom {a b : C}
  {F : @TAlgebra (C^op) (W^op) H a} {G : @TAlgebra (C^op) (W^op) H b}
  (f : @TAlgebraHom (C^op) (W^op) H b a G F) :
  @WCoalgebraHom C W H a b
    (TAlgebra_to_WCoalgebra F) (TAlgebra_to_WCoalgebra G) :=
  @Build_WCoalgebraHom C W H a b
    (TAlgebra_to_WCoalgebra F) (TAlgebra_to_WCoalgebra G)
    (@t_alg_hom (C^op) (W^op) H b a G F f)
    (@t_alg_hom_commutes (C^op) (W^op) H b a G F f).

(* * ** The co-Eilenberg–Moore 范畴, duality （已译） *)

Definition CoEilenbergMoore : Category :=
  (@EilenbergMoore (C^op) (W^op) H)^op.

(** The hom-sets co-Eilenberg–Moore 范畴 definitionally the
 algebra homomorphisms opposite 单子, source target
 swapped. （已译） *)

Lemma coeilenberg_moore_hom (x y : CoEilenbergMoore) :
  (x ~{CoEilenbergMoore}~> y) =
  @TAlgebraHom (C^op) (W^op) H ``y ``x (projT2 y) (projT2 x).
Proof. reflexivity. Qed.

(*
   本节说明单子、Eilenberg–Moore相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition WCoalgebras : Category := {|
  obj     := ∃ a : C, @WCoalgebra C W H a;
  hom     := fun x y => @WCoalgebraHom C W H ``x ``y (projT2 x) (projT2 y);
  homset  := fun _ _ => {| equiv := fun f g => w_coalg_hom[f] ≈ w_coalg_hom[g] |};
  id      := fun _ => {| w_coalg_hom := id |};
  compose := fun _ _ _ f g => {| w_coalg_hom := w_coalg_hom[f] ∘ w_coalg_hom[g] |}
|}.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite w_coalg_hom_commutes.
  rewrite <- comp_assoc.
  rewrite w_coalg_hom_commutes.
  now rewrite comp_assoc.
Qed.

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := program_simpl.

Program Definition WCoalgebras_to_CoEM : WCoalgebras ⟶ CoEilenbergMoore := {|
  fobj := fun x => (``x; WCoalgebra_to_TAlgebra (projT2 x));
  fmap := fun x y f => WCoalgebraHom_to_TAlgebraHom f
|}.
Next Obligation. proper. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

Program Definition CoEM_to_WCoalgebras : CoEilenbergMoore ⟶ WCoalgebras := {|
  fobj := fun x => (``x; TAlgebra_to_WCoalgebra (projT2 x));
  fmap := fun x y f => TAlgebraHom_to_WCoalgebraHom f
|}.
Next Obligation. proper. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition coem_roundtrip (x : CoEilenbergMoore) :
  WCoalgebras_to_CoEM (CoEM_to_WCoalgebras x) ≅[CoEilenbergMoore] x := {|
  to   := {| t_alg_hom := id |};
  from := {| t_alg_hom := id |}
|}.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.

Program Definition wcoalgebras_roundtrip (x : WCoalgebras) :
  CoEM_to_WCoalgebras (WCoalgebras_to_CoEM x) ≅[WCoalgebras] x := {|
  to   := {| w_coalg_hom := id |};
  from := {| w_coalg_hom := id |}
|}.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.

Lemma WCoalgebras_to_CoEM_inverse :
  WCoalgebras_to_CoEM ◯ CoEM_to_WCoalgebras ≈ Id[CoEilenbergMoore].
Proof.
  exists coem_roundtrip.
  intros x y f; cbn; cat.
Qed.

Lemma CoEM_to_WCoalgebras_inverse :
  CoEM_to_WCoalgebras ◯ WCoalgebras_to_CoEM ≈ Id[WCoalgebras].
Proof.
  exists wcoalgebras_roundtrip.
  intros x y f; cbn; cat.
Qed.

Definition WCoalgebras_CoEilenbergMoore_Iso :
  WCoalgebras ≅[Cat] CoEilenbergMoore :=
  @Build_Isomorphism Cat WCoalgebras CoEilenbergMoore
    WCoalgebras_to_CoEM CoEM_to_WCoalgebras
    WCoalgebras_to_CoEM_inverse CoEM_to_WCoalgebras_inverse.

End CoEilenbergMoore.
