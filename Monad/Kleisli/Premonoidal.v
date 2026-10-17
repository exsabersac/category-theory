Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Binoidal.
Require Import Category.Structure.Premonoidal.
Require Import Category.Functor.Strong.
Require Import Category.Monad.Strong.
Require Import Category.Monad.Strong.Symmetric.
Require Import Category.Monad.Kleisli.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

(*
    nLab: https://ncatlab.org/nlab/show/premonoidal+category
    nLab: https://ncatlab.org/nlab/show/strong+monad

   本文件给出 Kleisli 范畴相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section KleisliPremonoidal.

Context `{@SymmetricMonoidal C}.
Context {M : C ⟶ C}.
Context `{@StrongMonad C _ M}.

(* ------------------------------------------------------------------ *)
(** ** Tier 1: the Kleisli binoidal structure.                         *)
(* ------------------------------------------------------------------ *)

(*
   本节说明hom、Kleisli、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition kl_left_fmap (y' : C) {x z : C} (f : x ~{C}~> M z) :
  (x ⨂ y')%object ~{C}~> M ((z ⨂ y')%object) :=
  rstr ∘ (f ⨂ id[y']).

(* The action of x' ⊗ - on a Kleisli morphism f : y ~> M z, through the
   left strength. *)
Definition kl_right_fmap (x' : C) {y z : C} (f : y ~{C}~> M z) :
  (x' ⨂ y)%object ~{C}~> M ((x' ⨂ z)%object) :=
  strength[M] ∘ (id[x'] ⨂ f).

Lemma kl_left_respects (y' : C) {x z : C} :
  Proper (equiv ==> equiv) (fun f : x ~{C}~> M z => kl_left_fmap y' f).
Proof.
  repeat intro.
  unfold kl_left_fmap.
  apply compose_respects; [reflexivity|].
  apply bimap_respects; [assumption|reflexivity].
Qed.

(* Identity preservation is the η-compat law of the derived right
   strength. *)
Lemma kl_left_id (y' x : C) :
  kl_left_fmap y' (ret[M]) ≈ (ret[M] : x ⨂ y' ~> M (x ⨂ y')).
Proof. apply rstr_ret. Qed.

(* Composition preservation is the μ-compat law [rstr_join], with the
   naturality corollary [rstr_natural_l] sliding the tensored middle map
   past the strength. *)
Lemma kl_left_comp (y' : C) {x y z : C} (f : y ~> M z) (g : x ~> M y) :
  kl_left_fmap y' (join[M] ∘ fmap[M] f ∘ g)
    ≈ join[M] ∘ fmap[M] (kl_left_fmap y' f) ∘ kl_left_fmap y' g.
Proof.
  unfold kl_left_fmap.
  transitivity
    ((rstr ∘ (join[M] ⨂ id[y'])) ∘ ((fmap[M] f ⨂ id[y']) ∘ (g ⨂ id[y']))).
  { rewrite <- !comp_assoc.
    apply compose_respects; [reflexivity|].
    rewrite <- !bimap_comp.
    rewrite !id_left.
    now rewrite !comp_assoc. }
  rewrite rstr_join.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  rewrite <- rstr_natural_l.
  reflexivity.
Qed.

Definition Kleisli_Tensor_Left (y' : C) :
  @AFunctor Kleisli Kleisli (fun x : C => (x ⨂ y')%object) :=
  @Build_AFunctor Kleisli Kleisli (fun x : C => (x ⨂ y')%object)
    (fun x z (f : x ~{Kleisli}~> z) => kl_left_fmap y' f)
    (fun x z => kl_left_respects y')
    (fun x => kl_left_id y' x)
    (fun x y z f g => kl_left_comp y' f g).

Lemma kl_right_respects (x' : C) {y z : C} :
  Proper (equiv ==> equiv) (fun f : y ~{C}~> M z => kl_right_fmap x' f).
Proof.
  repeat intro.
  unfold kl_right_fmap.
  apply compose_respects; [reflexivity|].
  apply bimap_respects; [reflexivity|assumption].
Qed.

(* Identity preservation is the η-compat law of the left strength. *)
Lemma kl_right_id (x' y : C) :
  kl_right_fmap x' (ret[M]) ≈ (ret[M] : x' ⨂ y ~> M (x' ⨂ y)).
Proof. apply strength_ret. Qed.

(* Composition preservation is the μ-compat law [strength_join], glued by
   [strength_natural_r]. *)
Lemma kl_right_comp (x' : C) {x y z : C} (f : y ~> M z) (g : x ~> M y) :
  kl_right_fmap x' (join[M] ∘ fmap[M] f ∘ g)
    ≈ join[M] ∘ fmap[M] (kl_right_fmap x' f) ∘ kl_right_fmap x' g.
Proof.
  unfold kl_right_fmap.
  transitivity
    ((strength[M] ∘ (id[x'] ⨂ join[M]))
       ∘ ((id[x'] ⨂ fmap[M] f) ∘ (id[x'] ⨂ g))).
  { rewrite <- !comp_assoc.
    apply compose_respects; [reflexivity|].
    rewrite <- !bimap_comp.
    rewrite !id_left.
    now rewrite !comp_assoc. }
  rewrite strength_join.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  rewrite <- strength_natural_r.
  reflexivity.
Qed.

Definition Kleisli_Tensor_Right (x' : C) :
  @AFunctor Kleisli Kleisli (fun y : C => (x' ⨂ y)%object) :=
  @Build_AFunctor Kleisli Kleisli (fun y : C => (x' ⨂ y)%object)
    (fun y z (f : y ~{Kleisli}~> z) => kl_right_fmap x' f)
    (fun y z => kl_right_respects x')
    (fun y => kl_right_id x' y)
    (fun x y z f g => kl_right_comp x' f g).

(* The Power–Robinson binoidal structure on Kl(M): the object tensor is
   inherited from C, and the two one-variable tensoring functors are the
   strength-mediated actions above. *)
Definition Kleisli_Binoidal : @Binoidal Kleisli :=
  @Build_Binoidal Kleisli
    (fun x y : C => (x ⨂ y)%object)
    Kleisli_Tensor_Left
    Kleisli_Tensor_Right.

(*
   本节说明函子、Kleisli、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma kl_inj_left_fmap {y' x z : C} (f : x ~{C}~> M z) :
  fmap[@inj_left Kleisli Kleisli_Binoidal y'] f ≈ rstr ∘ (f ⨂ id[y']).
Proof. reflexivity. Qed.

Lemma kl_inj_right_fmap {x' y z : C} (f : y ~{C}~> M z) :
  fmap[@inj_right Kleisli Kleisli_Binoidal x'] f ≈ strength[M] ∘ (id[x'] ⨂ f).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** Normal forms for the two centrality squares.                    *)
(* ------------------------------------------------------------------ *)

(*
   本节说明Kleisli、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma kl_square_lr {a b c d} (f : a ~> M b) (g : c ~> M d) :
  @compose Kleisli _ _ _
    (fmap[@inj_left _ Kleisli_Binoidal d] f)
    (fmap[@inj_right _ Kleisli_Binoidal a] g)
    ≈ dstr' ∘ (f ⨂ g).
Proof.
  simpl.
  unfold kl_left_fmap, kl_right_fmap, dstr'.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  apply compose_respects; [reflexivity|].
  (* fmap (f ⨂ id) ∘ (strength ∘ (id ⨂ g)) ≈ strength ∘ (f ⨂ g) *)
  rewrite comp_assoc.
  rewrite strength_natural_l.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  now rewrite id_left, id_right.
Qed.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma kl_square_rl {a b c d} (f : a ~> M b) (g : c ~> M d) :
  @compose Kleisli _ _ _
    (fmap[@inj_right _ Kleisli_Binoidal b] g)
    (fmap[@inj_left _ Kleisli_Binoidal c] f)
    ≈ dstr ∘ (f ⨂ g).
Proof.
  simpl.
  unfold kl_left_fmap, kl_right_fmap, dstr.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  apply compose_respects; [reflexivity|].
  (* fmap (id ⨂ g) ∘ (rstr ∘ (f ⨂ id)) ≈ rstr ∘ (f ⨂ g) *)
  rewrite comp_assoc.
  rewrite rstr_natural_r.
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  now rewrite id_left, id_right.
Qed.

(*
   本节说明单子、Kleisli、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma kleisli_central_iff {a b} (f : a ~> M b) :
  @central Kleisli Kleisli_Binoidal a b f
    ↔ ∀ c d (g : c ~> M d),
        (dstr ∘ (f ⨂ g) ≈ dstr' ∘ (f ⨂ g))
      ∧ (dstr ∘ (g ⨂ f) ≈ dstr' ∘ (g ⨂ f)).
Proof.
  split.
  - intros central_f c d g.
    destruct (central_f c d g) as [sq1 sq2].
    split.
    + rewrite <- kl_square_lr, <- kl_square_rl.
      now symmetry.
    + rewrite <- kl_square_lr, <- kl_square_rl.
      now symmetry.
  - intros commutes c d g.
    split.
    + rewrite kl_square_lr, kl_square_rl.
      symmetry; apply commutes.
    + rewrite kl_square_lr, kl_square_rl.
      symmetry; apply commutes.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tier 2: the pure functor C ⟶ Kl(M).                             *)
(* ------------------------------------------------------------------ *)

(* A pure Kleisli morphism: an ordinary C-morphism followed by the unit. *)
Definition kpure {x y : C} (f : x ~{C}~> y) : x ~{Kleisli}~> y :=
  ret[M] ∘ f.

(* Postcomposing a Kleisli morphism with a pure map is functorial action:
   the unit collapses through [join_fmap_ret]. *)
Lemma kl_pure_post {x y z : C} (u : y ~{C}~> z) (h : x ~{Kleisli}~> y) :
  @compose Kleisli _ _ _ (kpure u) h ≈ fmap[M] u ∘ h.
Proof.
  simpl.
  unfold kpure.
  apply compose_respects; [|reflexivity].
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite join_fmap_ret.
  now rewrite id_left.
Qed.

(* Precomposing a Kleisli morphism with a pure map is plain C-level
   precomposition: the unit collapses through [fmap_ret] and [join_ret]. *)
Lemma kl_pure_pre {x y z : C} (h : y ~{C}~> M z) (u : x ~{C}~> y) :
  @compose Kleisli _ _ _ h (kpure u) ≈ h ∘ u.
Proof.
  simpl.
  unfold kpure.
  rewrite comp_assoc.
  apply compose_respects; [|reflexivity].
  rewrite <- comp_assoc.
  rewrite <- fmap_ret.
  rewrite comp_assoc.
  rewrite join_ret.
  now rewrite id_left.
Qed.

(* Kleisli composition of pure maps is pure composition. *)
Lemma kl_pure_comp {x y z : C} (u : y ~{C}~> z) (v : x ~{C}~> y) :
  @compose Kleisli _ _ _ (kpure u) (kpure v) ≈ kpure (u ∘ v).
Proof.
  rewrite kl_pure_pre.
  unfold kpure.
  now rewrite comp_assoc.
Qed.

Lemma kpure_respects {x y : C} :
  Proper (equiv ==> equiv) (fun f : x ~{C}~> y => (kpure f : x ~{C}~> M y)).
Proof.
  repeat intro.
  unfold kpure.
  apply compose_respects; [reflexivity|assumption].
Qed.

(* Congruence for [kpure] in apply-friendly form, stated over the C-level
   homset so that no Kleisli unification is required of the caller. *)
Lemma kpure_proper {x y : C} {f g : x ~{C}~> y} (E : f ≈ g) :
  (kpure f : x ~{C}~> M y) ≈ kpure g.
Proof.
  unfold kpure.
  now rewrite E.
Qed.

Lemma kpure_id {x : C} : kpure (@id C x) ≈ @id Kleisli x.
Proof.
  unfold kpure; simpl.
  now rewrite id_right.
Qed.

Lemma kpure_comp_functor {x y z : C} (u : y ~{C}~> z) (v : x ~{C}~> y) :
  kpure (u ∘ v) ≈ @compose Kleisli _ _ _ (kpure u) (kpure v).
Proof. symmetry; apply kl_pure_comp. Qed.

(*
   本节说明伴随、函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Kleisli_Pure : C ⟶ Kleisli := {|
  fobj := fun x : C => (x : Kleisli);
  fmap := fun (x y : C) (f : x ~{C}~> y) => kpure f;
  fmap_respects := fun x y : C => @kpure_respects x y;
  fmap_id := fun x : C => @kpure_id x;
  fmap_comp := fun (x y z : C) f g => kpure_comp_functor f g
|}.

(* Pure maps slide through the left tensoring: the unit exits through the
   η-compat law [rstr_ret] of the derived right strength. *)
Lemma pure_inj_left {x y : C} (f : x ~{C}~> y) (z : C) :
  fmap[@inj_left Kleisli Kleisli_Binoidal z] (kpure f) ≈ kpure (f ⨂ id[z]).
Proof.
  rewrite kl_inj_left_fmap.
  unfold kpure.
  rewrite bimap_comp_id_right.
  rewrite comp_assoc.
  rewrite rstr_ret.
  reflexivity.
Qed.

(* Pure maps slide through the right tensoring, through [strength_ret]. *)
Lemma pure_inj_right {x y : C} (f : x ~{C}~> y) (z : C) :
  fmap[@inj_right Kleisli Kleisli_Binoidal z] (kpure f) ≈ kpure (id[z] ⨂ f).
Proof.
  rewrite kl_inj_right_fmap.
  unfold kpure.
  rewrite bimap_comp_id_left.
  rewrite comp_assoc.
  rewrite strength_ret.
  reflexivity.
Qed.

(*
   本节说明单子、Kleisli、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem pure_central {x y : C} (f : x ~{C}~> y) :
  @central Kleisli Kleisli_Binoidal x y (kpure f).
Proof.
  apply kleisli_central_iff; intros c d g.
  split.
  - assert (E : ((kpure f : x ~{C}~> M y) ⨂ g) ≈ (ret[M] ⨂ id[M d]) ∘ (f ⨂ g)).
    { unfold kpure.
      rewrite <- bimap_comp.
      now rewrite id_left. }
    rewrite E.
    rewrite !comp_assoc.
    now rewrite dstr_ret_left, dstr'_ret_left.
  - assert (E : (g ⨂ (kpure f : x ~{C}~> M y)) ≈ (id[M d] ⨂ ret[M]) ∘ (g ⨂ f)).
    { unfold kpure.
      rewrite <- bimap_comp.
      now rewrite id_left. }
    rewrite E.
    rewrite !comp_assoc.
    now rewrite dstr_ret_right, dstr'_ret_right.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Tier 3: the premonoidal structure on Kl(M).                     *)
(* ------------------------------------------------------------------ *)

(* An isomorphism of C becomes an isomorphism of Kl(M) through the pure
   functor: both inverse laws are the C-level laws under [kl_pure_comp]. *)
Lemma kl_pure_iso_law {x y : C} (u : x ~{C}~> y) (v : y ~{C}~> x) :
  u ∘ v ≈ id[y] →
  @compose Kleisli _ _ _ (kpure u) (kpure v) ≈ @id Kleisli y.
Proof.
  intros E.
  rewrite kl_pure_comp.
  unfold kpure.
  rewrite E.
  simpl.
  now rewrite id_right.
Qed.

Definition Kleisli_pure_iso {x y : C} (i : x ≅ y) : @Isomorphism Kleisli x y := {|
  to := kpure (to i);
  from := kpure (from i);
  iso_to_from := kl_pure_iso_law (to i) (from i) (iso_to_from i);
  iso_from_to := kl_pure_iso_law (from i) (to i) (iso_from_to i)
|}.

(* Naturality of the left unitor in Kl(M): after the pure-map exchange
   laws, this is Kock's unit coherence [strength_id_left] composed with
   naturality of λ in C. *)
Lemma kl_unit_left_natural {x y : C} (g : x ~{Kleisli}~> y) :
  @compose Kleisli _ _ _ g (kpure (to (@unit_left C _ x)))
    ≈ @compose Kleisli _ _ _ (kpure (to (@unit_left C _ y)))
        (fmap[@inj_right Kleisli Kleisli_Binoidal (@I C _)] g).
Proof.
  rewrite kl_pure_pre, kl_pure_post.
  rewrite kl_inj_right_fmap.
  rewrite comp_assoc.
  rewrite strength_id_left.
  apply (@to_unit_left_natural C _ x (M y) g).
Qed.

(* Naturality of the right unitor: the mirror argument through the derived
   right strength's ρ-coherence [rstr_id_right]. *)
Lemma kl_unit_right_natural {x y : C} (g : x ~{Kleisli}~> y) :
  @compose Kleisli _ _ _ g (kpure (to (@unit_right C _ x)))
    ≈ @compose Kleisli _ _ _ (kpure (to (@unit_right C _ y)))
        (fmap[@inj_left Kleisli Kleisli_Binoidal (@I C _)] g).
Proof.
  rewrite kl_pure_pre, kl_pure_post.
  rewrite kl_inj_left_fmap.
  rewrite comp_assoc.
  rewrite rstr_id_right.
  apply (@to_unit_right_natural C _ x (M y) g).
Qed.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma kl_assoc_natural_left {x y z w : C} (g : x ~{Kleisli}~> y) :
  @compose Kleisli _ _ _
    (fmap[@inj_left Kleisli Kleisli_Binoidal (z ⨂ w)%object] g)
    (kpure (to (@tensor_assoc C _ x z w)))
  ≈ @compose Kleisli _ _ _
      (kpure (to (@tensor_assoc C _ y z w)))
      (fmap[@inj_left Kleisli Kleisli_Binoidal w]
         (fmap[@inj_left Kleisli Kleisli_Binoidal z] g)).
Proof.
  rewrite kl_pure_pre, kl_pure_post.
  rewrite !kl_inj_left_fmap.
  rewrite bimap_comp_id_right.
  rewrite !comp_assoc.
  rewrite rstr_assoc_to.
  pose proof (@to_tensor_assoc_natural
                C _ x (M y) z z w w g (id[z]) (id[w])) as AN.
  rewrite bimap_id_id in AN.
  rewrite <- !comp_assoc.
  rewrite <- AN.
  reflexivity.
Qed.

(*
   本节说明单子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma kl_assoc_natural_middle {x z w y : C} (h : z ~{Kleisli}~> w) :
  @compose Kleisli _ _ _
    (fmap[@inj_right Kleisli Kleisli_Binoidal x]
       (fmap[@inj_left Kleisli Kleisli_Binoidal y] h))
    (kpure (to (@tensor_assoc C _ x z y)))
  ≈ @compose Kleisli _ _ _
      (kpure (to (@tensor_assoc C _ x w y)))
      (fmap[@inj_left Kleisli Kleisli_Binoidal y]
         (fmap[@inj_right Kleisli Kleisli_Binoidal x] h)).
Proof.
  rewrite kl_pure_pre, kl_pure_post.
  rewrite !kl_inj_right_fmap.
  rewrite !kl_inj_left_fmap.
  rewrite bimap_comp_id_left.
  rewrite bimap_comp_id_right.
  rewrite !comp_assoc.
  rewrite strength_rstr_assoc.
  pose proof (@to_tensor_assoc_natural
                C _ x x z (M w) y y (id[x]) h (id[y])) as AN.
  rewrite <- !comp_assoc.
  rewrite <- AN.
  reflexivity.
Qed.

(* Naturality of the associator in the RIGHT tensor position: Kock's
   associativity coherence [strength_assoc] absorbs the two stacked right
   tensorings. *)
Lemma kl_assoc_natural_right {x y z w : C} (i : z ~{Kleisli}~> w) :
  @compose Kleisli _ _ _
    (fmap[@inj_right Kleisli Kleisli_Binoidal x]
       (fmap[@inj_right Kleisli Kleisli_Binoidal y] i))
    (kpure (to (@tensor_assoc C _ x y z)))
  ≈ @compose Kleisli _ _ _
      (kpure (to (@tensor_assoc C _ x y w)))
      (fmap[@inj_right Kleisli Kleisli_Binoidal (x ⨂ y)%object] i).
Proof.
  rewrite kl_pure_pre, kl_pure_post.
  rewrite !kl_inj_right_fmap.
  rewrite bimap_comp_id_left.
  rewrite !comp_assoc.
  rewrite strength_assoc.
  pose proof (@to_tensor_assoc_natural
                C _ x x y y z (M w) (id[x]) (id[y]) i) as AN.
  rewrite bimap_id_id in AN.
  rewrite <- !comp_assoc.
  rewrite <- AN.
  reflexivity.
Qed.

(* The triangle coherence transfers from C: all three structural maps are
   pure, so the equation is the image of C's triangle under [kpure]. *)
Lemma kl_triangle {x y : C} :
  fmap[@inj_left Kleisli Kleisli_Binoidal y] (kpure (to (@unit_right C _ x)))
  ≈ @compose Kleisli _ _ _
      (fmap[@inj_right Kleisli Kleisli_Binoidal x]
         (kpure (to (@unit_left C _ y))))
      (kpure (to (@tensor_assoc C _ x (@I C _) y))).
Proof.
  rewrite pure_inj_left, pure_inj_right.
  rewrite kl_pure_comp.
  apply kpure_proper.
  apply triangle_identity.
Qed.

(* The pentagon coherence transfers from C the same way. *)
Lemma kl_pentagon {x y z w : C} :
  @compose Kleisli _ _ _
    (@compose Kleisli _ _ _
       (fmap[@inj_right Kleisli Kleisli_Binoidal x]
          (kpure (to (@tensor_assoc C _ y z w))))
       (kpure (to (@tensor_assoc C _ x (y ⨂ z)%object w))))
    (fmap[@inj_left Kleisli Kleisli_Binoidal w]
       (kpure (to (@tensor_assoc C _ x y z))))
  ≈ @compose Kleisli _ _ _
      (kpure (to (@tensor_assoc C _ x y (z ⨂ w)%object)))
      (kpure (to (@tensor_assoc C _ (x ⨂ y)%object z w))).
Proof.
  rewrite pure_inj_right, pure_inj_left.
  rewrite !kl_pure_comp.
  apply kpure_proper.
  apply pentagon_identity.
Qed.

(*
   本节说明幺半结构、函子、单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Kleisli_Premonoidal : @Premonoidal Kleisli Kleisli_Binoidal :=
  @Build_Premonoidal Kleisli Kleisli_Binoidal
    (@I C _)
    (fun x : C => Kleisli_pure_iso (@unit_left C _ x))
    (fun x : C => Kleisli_pure_iso (@unit_right C _ x))
    (fun x y z : C => Kleisli_pure_iso (@tensor_assoc C _ x y z))
    (fun x : C => pure_central (to (@unit_left C _ x)))
    (fun x : C => pure_central (to (@unit_right C _ x)))
    (fun x y z : C => pure_central (to (@tensor_assoc C _ x y z)))
    (fun (x y : C) (g : x ~{Kleisli}~> y) => kl_unit_left_natural g)
    (fun (x y : C) (g : x ~{Kleisli}~> y) => kl_unit_right_natural g)
    (fun (x y z w : C) (g : x ~{Kleisli}~> y) => kl_assoc_natural_left g)
    (fun (x z w y : C) (h : z ~{Kleisli}~> w) => kl_assoc_natural_middle h)
    (fun (x y z w : C) (i : z ~{Kleisli}~> w) => kl_assoc_natural_right i)
    (fun x y : C => @kl_triangle x y)
    (fun x y z w : C => @kl_pentagon x y z w).

End KleisliPremonoidal.
