Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Braided.Proofs.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Semicartesian.
Require Import Category.Structure.Monoidal.Semicartesian.Proofs.
Require Import Category.Structure.Monoidal.CompactClosed.
Require Import Category.Structure.Monoidal.Heunen_Vicary.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.

Generalizable All Variables.

(*
    nLab: https://ncatlab.org/nlab/show/Frobenius+algebra
    nLab: https://ncatlab.org/nlab/show/no-cloning+theorem *)

   本文件给出幺半相关结构。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半结构、幺半群、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FrobeniusCollapse.

Context {C : Category}.
Context `{M : @Monoidal C}.
Context `{SM : @SemicartesianMonoidal C M}.

(* 相关说明。 （已译） *)
Lemma proj_right_delta {X : C} (Co : Comonoid X) :
  proj_right ∘ delta[Co] ≈ id[X].
Proof.
  unfold proj_right.
  rewrite <- comp_assoc.
  rewrite (unit_terminal (@eliminate C M SM X) epsilon[Co]).
  rewrite (delta_counit_left (Comonoid := Co)).
  apply iso_to_from.
Qed.

(* Mirror image: proj_left retracts delta via the right counit law. *)
Lemma proj_left_delta {X : C} (Co : Comonoid X) :
  proj_left ∘ delta[Co] ≈ id[X].
Proof.
  unfold proj_left.
  rewrite <- comp_assoc.
  rewrite (unit_terminal (@eliminate C M SM X) epsilon[Co]).
  rewrite (delta_counit_right (Comonoid := Co)).
  apply iso_to_from.
Qed.

Section FrobeniusObject.

Context {X : C}.
Context (F : @Frobenius C M X).

(*
   本节说明 Collapse 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma frobenius_mu_collapse : mu[F] ≈ @proj_right C M SM X X.
Proof.
  rewrite <- (id_left (mu[F])).
  rewrite <- (proj_right_delta F).
  rewrite <- comp_assoc.
  rewrite <- (frob_law_left (Frobenius := F)).
  rewrite !comp_assoc.
  rewrite proj_right_natural.
  rewrite id_left.
  rewrite <- proj_right_right.
  rewrite <- comp_assoc.
  rewrite proj_right_natural.
  rewrite comp_assoc.
  rewrite (proj_right_delta F).
  apply id_left.
Qed.

(* The monoid's right unit law μ ∘ (id ⨂ η) ≈ ρ evaluated at
   μ ≈ proj_right forces η to be a two-sided inverse of ε on X. *)
Lemma frobenius_eta_epsilon : eta[F] ∘ epsilon[F] ≈ id[X].
Proof using C F M SM X.
  pose proof (mu_unit_right (Monoid := F)) as MU.
  rewrite frobenius_mu_collapse in MU.
  rewrite proj_right_natural in MU.
  rewrite (unit_terminal epsilon[F] (proj_right ∘ unit_right⁻¹)).
  rewrite comp_assoc.
  rewrite MU.
  apply iso_to_from.
Qed.

(* A Frobenius 对象 semicartesian 幺半范畴 isomorphic to
 monoidal unit, counit unit Frobenius structure as
 two directions. （已译） *)
Theorem frobenius_collapse_semicartesian : X ≅ I.
Proof using C F M SM X.
  isomorphism.
  - exact (epsilon[F]).
  - exact (eta[F]).
  - apply unit_terminal.
  - apply frobenius_eta_epsilon.
Qed.

End FrobeniusObject.

End FrobeniusCollapse.

(*
   本节说明幺半结构、幺半群、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem frobenius_collapse {C : Category} `{H : @CartesianMonoidal C} {X : C}
        (F : @Frobenius C _ X) : X ≅ I.
Proof.
  exact (frobenius_collapse_semicartesian F).
Qed.

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section NoCloning.

Context {C : Category}.
Context `{R : @RelevanceMonoidal C}.
Context `{CC : @CompactClosed C (@relevance_is_symmetric C R)}.

(* Naturality diagonal, rewriting form: ∆ natural
 transformation 恒等 函子 squaring 函子. （已译） *)
Lemma diagonal_natural' {a b : C} (f : a ~> b) :
  f ⨂ f ∘ ∆a ≈ ∆b ∘ f.
Proof.
  spose (@diagonal_natural C R) as X0.
  apply X0.
Qed.

(* The middle-four interchange involutive: swapping middle two
 factors twice 恒等. (The two instances have middle
 arguments transposed.) （已译） *)
Lemma braid2_invol {a b c e : C} :
  @braid2 C R a c b e ∘ @braid2 C R a b c e ≈ id[((a ⨂ b) ⨂ (c ⨂ e))%object].
Proof.
  unfold braid2.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to tensor_assoc) (tensor_assoc⁻¹)).
  rewrite iso_to_from, id_left.
  normal.
  rewrite <- (comp_assoc _ (tensor_assoc⁻¹) (to tensor_assoc)).
  rewrite iso_from_to, id_right.
  rewrite <- (comp_assoc _ (braid ⨂ id) (braid ⨂ id)).
  rewrite <- bimap_comp.
  rewrite braid_invol, id_left.
  rewrite bimap_id_id, id_right.
  rewrite iso_to_from, bimap_id_id, id_right.
  apply iso_from_to.
Qed.

(* [braid2] is a definitional field of [RelevanceMonoidal]; statements of
   other fields (e.g. [diagonal_braid2]) carry its body inlined.  This fold
   lemma lets those occurrences be rewritten back to the named form. *)
Lemma braid2_unfold {a b c e : C} :
  @braid2 C R a b c e ≈
  tensor_assoc⁻¹ ∘ id ⨂ (tensor_assoc ∘ braid ⨂ id ∘ tensor_assoc⁻¹)
    ∘ tensor_assoc.
Proof. reflexivity. Qed.

(*
   本节说明幺半结构、幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Cloning.

Context {x : C}.

Notation d := (dual x).

(* The two parallel cups η ⨂ η, as a single state of (x* ⨂ x) ⨂ (x* ⨂ x). *)
Definition cups : I ~> ((d ⨂ x) ⨂ (d ⨂ x))%object :=
  cc_unit x ⨂ cc_unit x ∘ unit_left⁻¹.

(* The same state regrouped by colour, as a state of (x* ⨂ x* ) ⨂ (x ⨂ x). *)
Definition cups_mid : I ~> ((d ⨂ d) ⨂ (x ⨂ x))%object :=
  braid2 ∘ cups.

(* 相关说明。 （已译） *)
Lemma cups_diagonal : cups ≈ ∆(d ⨂ x) ∘ cc_unit x.
Proof.
  unfold cups.
  rewrite <- diagonal_unit.
  apply diagonal_natural'.
Qed.

(* 相关说明。 （已译） *)
Lemma cups_mid_diagonal : cups_mid ≈ ∆d ⨂ ∆x ∘ cc_unit x.
Proof.
  unfold cups_mid.
  rewrite cups_diagonal.
  rewrite diagonal_braid2.
  rewrite <- braid2_unfold.
  rewrite !comp_assoc.
  rewrite braid2_invol.
  now rewrite id_left.
Qed.

(* 相关说明。 （已译） *)
Lemma cups_mid_braid :
  id[(d ⨂ d)%object] ⨂ braid ∘ cups_mid ≈ cups_mid.
Proof.
  rewrite !cups_mid_diagonal.
  rewrite comp_assoc.
  rewrite <- bimap_comp.
  rewrite braid_diagonal, id_left.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma cups_split :
  cups ≈ id[(d ⨂ x)%object] ⨂ cc_unit x ∘ unit_right⁻¹ ∘ cc_unit x.
Proof.
  unfold cups.
  rewrite unit_identity_from.
  rewrite <- bimap_id_left_right.
  rewrite <- comp_assoc.
  rewrite from_unit_right_natural.
  rewrite comp_assoc.
  reflexivity.
Qed.

(* A single yanking stage: cap leading x against leading dual and
 pass remainder through. [bend] at Z := x, precomposed cup, is
 left snake 恒等. （已译） *)
Definition bend {Z : C} : (x ⨂ (d ⨂ Z))%object ~> Z :=
  unit_left ∘ cc_counit x ⨂ id[Z] ∘ tensor_assoc⁻¹.

(* bend is natural in the pass-through component. *)
Lemma bend_natural {Z Z' : C} (q : Z ~> Z') :
  bend ∘ id[x] ⨂ (id[d] ⨂ q) ≈ q ∘ bend.
Proof.
  unfold bend.
  rewrite <- comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  rewrite bimap_id_id.
  rewrite (comp_assoc (unit_left ∘ cc_counit x ⨂ id[Z'])
             (id[(x ⨂ d)%object] ⨂ q) (tensor_assoc⁻¹)).
  rewrite <- (comp_assoc unit_left (cc_counit x ⨂ id[Z'])
                (id[(x ⨂ d)%object] ⨂ q)).
  rewrite bimap_id_right_left.
  rewrite <- bimap_id_left_right.
  rewrite comp_assoc.
  rewrite <- to_unit_left_natural.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(* The left snake 恒等, phrased [bend]. （已译） *)
Lemma bend_snake : bend ∘ id[x] ⨂ cc_unit x ∘ unit_right⁻¹ ≈ id[x].
Proof.
  unfold bend.
  apply snake_left.
Qed.

(* A 推论 second hexagon: braiding whole pair past x then
 swapping inside left factor braiding two inner x-wires. （已译） *)
Lemma braid_pass {y : C} :
  braid ⨂ id[x] ∘ tensor_assoc⁻¹ ∘ @braid C _ (y ⨂ x)%object x
    ≈ tensor_assoc⁻¹ ∘ id[y] ⨂ braid ∘ tensor_assoc.
Proof.
  pose proof (@hexagon_identity_sym C _ y x x) as HX.
  assert (HX' : (@tensor_assoc C _ x y x)⁻¹ ∘ @braid C _ (y ⨂ x)%object x
                  ≈ braid ⨂ id[x] ∘ tensor_assoc⁻¹ ∘ id[y] ⨂ braid
                      ∘ tensor_assoc).
  { rewrite <- HX.
    rewrite <- !comp_assoc.
    rewrite iso_from_to, id_right.
    reflexivity. }
  rewrite <- comp_assoc.
  rewrite HX'.
  rewrite !comp_assoc.
  rewrite <- bimap_comp.
  rewrite braid_invol, id_left.
  rewrite bimap_id_id, id_left.
  reflexivity.
Qed.

(*
   本节说明 Collapse 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cup_pass :
  tensor_assoc ∘ braid ⨂ id[x] ∘ tensor_assoc⁻¹ ∘ id[x] ⨂ cc_unit x
      ∘ unit_right⁻¹
    ≈ id[d] ⨂ braid ∘ tensor_assoc ∘ cc_unit x ⨂ id[x] ∘ unit_left⁻¹.
Proof.
  rewrite <- braid_unit_right_from.
  rewrite comp_assoc.
  rewrite <- (comp_assoc _ (id[x] ⨂ cc_unit x) (@braid C _ I x)).
  rewrite bimap_braid.
  rewrite <- (comp_assoc (to tensor_assoc) (braid ⨂ id[x]) (tensor_assoc⁻¹)).
  rewrite (comp_assoc _ (@braid C _ (d ⨂ x)%object x) (cc_unit x ⨂ id[x])).
  rewrite <- (comp_assoc (to tensor_assoc) (braid ⨂ id[x] ∘ tensor_assoc⁻¹)
                (@braid C _ (d ⨂ x)%object x)).
  rewrite braid_pass.
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

(*
   本节说明 Collapse 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cups_mid_nested :
  to tensor_assoc ∘ cups_mid
    ≈ id[d] ⨂ (id[d] ⨂ braid ∘ tensor_assoc ∘ cc_unit x ⨂ id[x]
                 ∘ unit_left⁻¹)
        ∘ cc_unit x.
Proof.
  unfold cups_mid.
  rewrite cups_split.
  rewrite braid2_unfold.
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  rewrite <- (@bimap_id_id C C C (@tensor C _) d x).
  rewrite <- (comp_assoc _ (to tensor_assoc) ((id[d] ⨂ id[x]) ⨂ cc_unit x)).
  rewrite <- to_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to tensor_assoc) (unit_right⁻¹) (cc_unit x)).
  rewrite tensor_assoc_unit_right.
  normal.
  rewrite cup_pass.
  reflexivity.
Qed.

(* The left snake 恒等, solved inverse unitor. （已译） *)
Lemma snake_left_from :
  cc_counit x ⨂ id[x] ∘ tensor_assoc⁻¹ ∘ id[x] ⨂ cc_unit x ∘ unit_right⁻¹
    ≈ unit_left⁻¹.
Proof.
  apply (iso_to_monic unit_left).
  rewrite iso_to_from.
  rewrite !comp_assoc.
  apply snake_left.
Qed.

(* Yanking spectator: inserting cup beside wire capping it
 against leading input 恒等 both wires. （已译） *)
Lemma spectator_snake :
  bend ∘ id[x] ⨂ (tensor_assoc ∘ cc_unit x ⨂ id[x] ∘ unit_left⁻¹)
    ≈ id[(x ⨂ x)%object].
Proof.
  unfold bend.
  rewrite !bimap_comp_id_left.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (tensor_assoc⁻¹) (id[x] ⨂ to tensor_assoc)).
  rewrite pentagon_step.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (tensor_assoc⁻¹) (id[x] ⨂ (cc_unit x ⨂ id[x]))).
  rewrite <- from_tensor_assoc_natural.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (tensor_assoc⁻¹) (id[x] ⨂ unit_left⁻¹)).
  rewrite tensor_assoc_from_unit_left.
  rewrite <- (@bimap_id_id C C C (@tensor C _) x x).
  rewrite <- (comp_assoc unit_left (cc_counit x ⨂ (id[x] ⨂ id[x]))
                (to tensor_assoc)).
  rewrite to_tensor_assoc_natural.
  rewrite !comp_assoc.
  normal.
  rewrite snake_left_from.
  rewrite <- triangle_identity_left.
  normal.
  rewrite iso_to_from.
  normal.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Definition close (v : I ~> ((d ⨂ d) ⨂ (x ⨂ x))%object) :
  (x ⨂ x)%object ~> (x ⨂ x)%object :=
  bend ∘ id[x] ⨂ (bend ∘ id[x] ⨂ (to tensor_assoc ∘ v) ∘ unit_right⁻¹).

#[local] Instance close_respects : Proper (equiv ==> equiv) close.
Proof.
  proper.
  unfold close.
  rewrites.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma close_braid (v : I ~> ((d ⨂ d) ⨂ (x ⨂ x))%object) :
  close (id[(d ⨂ d)%object] ⨂ braid ∘ v) ≈ braid ∘ close v.
Proof.
  unfold close.
  rewrite (comp_assoc (to tensor_assoc) (id[(d ⨂ d)%object] ⨂ braid) v).
  rewrite <- (@bimap_id_id C C C (@tensor C _) d d).
  rewrite <- to_tensor_assoc_natural.
  rewrite <- (comp_assoc (id[d] ⨂ (id[d] ⨂ braid)) (to tensor_assoc) v).
  rewrite (bimap_comp_id_left (id[d] ⨂ (id[d] ⨂ braid)) (to tensor_assoc ∘ v)).
  rewrite (comp_assoc bend (id[x] ⨂ (id[d] ⨂ (id[d] ⨂ braid)))).
  rewrite bend_natural.
  rewrite <- (comp_assoc (id[d] ⨂ braid) bend (id[x] ⨂ (to tensor_assoc ∘ v))).
  rewrite <- (comp_assoc (id[d] ⨂ braid)
                (bend ∘ id[x] ⨂ (to tensor_assoc ∘ v)) unit_right⁻¹).
  rewrite (bimap_comp_id_left (id[d] ⨂ braid)
             (bend ∘ id[x] ⨂ (to tensor_assoc ∘ v) ∘ unit_right⁻¹)).
  rewrite (comp_assoc bend (id[x] ⨂ (id[d] ⨂ braid))).
  rewrite bend_natural.
  rewrite <- comp_assoc.
  reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma close_cups_mid : close cups_mid ≈ braid.
Proof.
  unfold close.
  rewrite cups_mid_nested.
  rewrite (bimap_comp_id_left
             (id[d] ⨂ (id[d] ⨂ braid ∘ tensor_assoc ∘ cc_unit x ⨂ id[x]
                         ∘ unit_left⁻¹))
             (cc_unit x)).
  rewrite (comp_assoc bend
             (id[x] ⨂ (id[d] ⨂ (id[d] ⨂ braid ∘ tensor_assoc
                                  ∘ cc_unit x ⨂ id[x] ∘ unit_left⁻¹)))).
  rewrite bend_natural.
  rewrite <- (comp_assoc _ bend (id[x] ⨂ cc_unit x)).
  rewrite <- (comp_assoc _ (bend ∘ id[x] ⨂ cc_unit x) unit_right⁻¹).
  rewrite bend_snake.
  rewrite id_right.
  rewrite <- !comp_assoc.
  rewrite (bimap_comp_id_left (id[d] ⨂ braid)
             (to tensor_assoc ∘ (cc_unit x ⨂ id[x] ∘ unit_left⁻¹))).
  rewrite comp_assoc.
  rewrite bend_natural.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (to tensor_assoc) (cc_unit x ⨂ id[x]) (unit_left⁻¹)).
  rewrite spectator_snake.
  rewrite id_right.
  reflexivity.
Qed.

(*
   本节说明 Collapse 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem no_cloning : @braid C _ x x ≈ id[(x ⨂ x)%object].
Proof using C CC R x.
  pose proof close_cups_mid as E1.
  assert (E2 : close cups_mid ≈ braid ∘ close cups_mid).
  { transitivity (close (id[(d ⨂ d)%object] ⨂ braid ∘ cups_mid)).
    - symmetry.
      now rewrite cups_mid_braid.
    - apply close_braid. }
  rewrite E1 in E2.
  rewrite braid_invol in E2.
  exact E2.
Qed.

End Cloning.

End NoCloning.
