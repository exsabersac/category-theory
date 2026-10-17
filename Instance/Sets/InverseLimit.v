Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Chain.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cone.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cartesian.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Streams.

Generalizable All Variables.

(*
   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Open Scope category_scope.

(* Obligations are written out rather than left to the tree default, so
   that each [intros] pattern is predictable -- the Instance/Sets/Cone.v
   idiom. *)
#[local] Obligation Tactic := idtac.

(** * Inverse limits of towers of sets *)

(*
   nLab:      https://ncatlab.org/nlab/show/inverse+limit
   Wikipedia: https://en.wikipedia.org/wiki/Inverse_limit

   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** (A) The tower's own compatibility condition *)

Section Tower.

Context (F : Omega^op ⟶ Sets).

(*
   本节说明 InverseLimit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition tower_step (n : nat) : @hom (Omega^op) (S n) n := omega_step n.

(*
   本节说明（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example tower_step_is_omega_step (n : nat) :
  tower_step n = omega_step n := eq_refl.

(*
   本节说明 InverseLimit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example step_is_le_t_S (m k : nat) (f : @hom (Omega^op) k m) :
  @compose (Omega^op) (S k) k m f (tower_step k) = le_t_S f := eq_refl.

(* Mac Lane's matching-string condition: successive entries are carried to
   one another.  Compare [Sets_limit_compatible] (Instance/Sets/
   Complete.v), which quantifies over EVERY arrow of the shape. *)
Definition tower_compat (x : Sets_iprod_obj (fun n : nat => F n)) : Type :=
  ∀ n : nat, fmap[F] (tower_step n) (x (S n)) ≈ x n.

(* The product the two presentations are cut out of is one and the same. *)
Example tower_inner_strict :
  Sets_iprod_obj (fun d : Omega^op => F d)
  = Sets_iprod_obj (fun n : nat => F n) := eq_refl.

(*
   本节说明 InverseLimit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma tower_compat_all (x : Sets_iprod_obj (fun n : nat => F n))
  (H : tower_compat x) {m n : nat} (f : @hom (Omega^op) n m) :
  fmap[F] f (x n) ≈ x m.
Proof.
  induction f as [| k f' IH].
  - exact (@fmap_id _ _ F m (x m)).
  - transitivity (fmap[F] f' (fmap[F] (tower_step k) (x (S k)))).
    + exact (@fmap_comp _ _ F (S k) k m f' (tower_step k) (x (S k))).
    + transitivity (fmap[F] f' (x k)).
      * apply proper_morphism; exact (H k).
      * exact IH.
Qed.

(** ** (B) The set of matching strings, and its projections *)

Program Definition tower_obj : obj[Sets] := {|
  carrier   := { x : Sets_iprod_obj (fun n : nat => F n) & tower_compat x };
  is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |}
|}.
Next Obligation.
  constructor.
  - intros p n; reflexivity.
  - intros p q Hpq n; symmetry; exact (Hpq n).
  - intros p q r Hpq Hqr n; transitivity (`1 q n);
    [exact (Hpq n)|exact (Hqr n)].
Qed.

(* "with the coordinate projections as the legs". *)
Program Definition tower_proj (n : nat) : tower_obj ~{Sets}~> F n := {|
  morphism := fun p => `1 p n
|}.
Next Obligation. intros n p q Hpq; exact (Hpq n). Qed.

(* An element of the inverse limit is determined by its coordinates: this
   is the definition of [tower_obj]'s setoid, restated in the form a
   consumer wants. *)
Lemma tower_ext (p q : tower_obj) :
  (∀ n : nat, tower_proj n p ≈ tower_proj n q) → p ≈ q.
Proof. intros Hn n; exact (Hn n). Qed.

(** ** (C) The two presentations agree *)

Program Definition tower_fwd :
  Sets_limit_obj F ~{Sets}~> tower_obj := {|
  morphism := fun p => (`1 p ; fun n => _)
|}.
Next Obligation. intros p n; exact (`2 p (S n) n (tower_step n)). Defined.
Next Obligation. intros p q Hpq n; exact (Hpq n). Qed.

Program Definition tower_bwd :
  tower_obj ~{Sets}~> Sets_limit_obj F := {|
  morphism := fun p => (`1 p ; fun m n f => _)
|}.
Next Obligation.
  intros p m n f; exact (tower_compat_all (`1 p) (`2 p) f).
Defined.
Next Obligation. intros p q Hpq n; exact (Hpq n). Qed.

(* The compatible-family limit IS the set of matching strings. *)
Program Definition tower_iso :
  @Isomorphism Sets (Sets_limit_obj F) tower_obj := {|
  to := tower_fwd; from := tower_bwd
|}.
Next Obligation. intros p n; reflexivity. Qed.
Next Obligation. intros p n; reflexivity. Qed.

(** ** (D) The matching strings are a limit *)

Program Definition tower_acone : ACone tower_obj F := {|
  vertex_map := tower_proj
|}.
Next Obligation. intros m n f p; exact (tower_compat_all (`1 p) (`2 p) f). Qed.

Definition tower_cone : Cone F :=
  {| vertex_obj := tower_obj; coneFrom := tower_acone |}.

(* The mediator out of a competing cone: bundle its legs at a point, whose
   step compatibility is the cone's own coherence read at [tower_step]. *)
Program Definition tower_med (N : Cone F) :
  vertex_obj[N] ~{Sets}~> tower_obj := {|
  morphism := fun e =>
    (fun n => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) n e;
     fun n => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) (S n) n
                (tower_step n) e)
|}.
Next Obligation.
  intros N e e' Hee' n.
  exact (proper_morphism (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) n)
                         e e' Hee').
Qed.

Lemma tower_med_commutes (N : Cone F) (n : nat) :
  tower_proj n ∘ tower_med N
    ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) n.
Proof. intros e; reflexivity. Qed.

Lemma tower_med_unique (N : Cone F)
  (v : vertex_obj[N] ~{Sets}~> tower_obj)
  (Hv : ∀ n : nat,
          tower_proj n ∘ v ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) n) :
  v ≈ tower_med N.
Proof. intros e n; exact (Hv n e). Qed.

Program Definition Sets_tower_limit : IsALimit F tower_obj := {|
  limit_acone := tower_acone;
  ump_limit := fun N => {| unique_obj := tower_med N |}
|}.
Next Obligation. intros N n e; reflexivity. Qed.
Next Obligation. intros N v Hv e n; symmetry; exact (Hv n e). Qed.

Program Definition Sets_tower_Limit : Limit F := {|
  limit_cone := tower_cone;
  ump_limits := fun N => {| unique_obj := tower_med N |}
|}.
Next Obligation. intros N n e; reflexivity. Qed.
Next Obligation. intros N v Hv e n; symmetry; exact (Hv n e). Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_tower_limit_iso_cone_limit : tower_obj ≅ cone_apex F :=
  limit_unique_iso Sets_tower_limit (cone_set_IsALimit F).

End Tower.

(** ** (E) The named notion, its notation, and [Cochain]'s first consumer *)

Definition inverse_limit (F : Omega^op ⟶ Sets) : SetoidObject := tower_obj F.

(* By DELTA, like [tower_step_is_omega_step] above: [inverse_limit] is
   defined as [tower_obj], so this guards the name against drift and
   measures nothing. *)
Example inverse_limit_is_tower (F : Omega^op ⟶ Sets) :
  inverse_limit F = tower_obj F := eq_refl.

(* An OPT-IN scope, on the [power_scope] precedent of
   Structure/Limit/Power.v: the token is not forced on any consumer. *)
Declare Scope inverse_limit_scope.
Delimit Scope inverse_limit_scope with invlim.
Notation "'lim←' F" := (inverse_limit F)
  (at level 9, format "'lim←'  F") : inverse_limit_scope.

(*
   本节说明（余）极限、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition cochain_inverse_limit@{su +}
  (G : Sets@{Set su} ⟶ Sets@{Set su}) : obj[Sets@{Set su}] :=
  inverse_limit (Cochain G).

Definition cochain_tower_limit@{su +}
  (G : Sets@{Set su} ⟶ Sets@{Set su}) :
  IsALimit (Cochain G) (cochain_inverse_limit G) :=
  Sets_tower_limit (Cochain G).

(* The tower's stages are the iterated images of the terminal object. *)
Example cochain_stage_zero@{su +} (G : Sets@{Set su} ⟶ Sets@{Set su}) :
  fobj[Cochain G] 0%nat = @terminal_obj Sets@{Set su} Sets_Terminal
  := eq_refl.

Example cochain_stage_succ@{su +} (G : Sets@{Set su} ⟶ Sets@{Set su})
  (n : nat) : fobj[Cochain G] (S n) = G (fobj[Cochain G] n) := eq_refl.

(** ** (F) What the two identifications read back *)

(* The legs of the tower limit ARE the coordinate projections. *)
Example tower_limit_leg (F : Omega^op ⟶ Sets) (n : nat) :
  limit_leg (Sets_tower_limit F) n = tower_proj F n := eq_refl.

(* And the comparison with the cone set is not a bare [≅]: it carries both
   leg families, by the general essential-uniqueness theorem. *)
Definition Sets_tower_limit_iso_cone_limit_legs (F : Omega^op ⟶ Sets) :
  (∀ n : nat, cone_leg_at F n ∘ to (Sets_tower_limit_iso_cone_limit F)
                ≈ tower_proj F n) *
  (∀ n : nat, tower_proj F n ∘ from (Sets_tower_limit_iso_cone_limit F)
                ≈ cone_leg_at F n) :=
  limit_unique_iso_legs (Sets_tower_limit F) (cone_set_IsALimit F).

(*
   本节说明 InverseLimit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example tower_fwd_underlying (F : Omega^op ⟶ Sets)
  (p : Sets_limit_obj F) : `1 (tower_fwd F p) = `1 p := eq_refl.

Example tower_bwd_underlying (F : Omega^op ⟶ Sets)
  (p : tower_obj F) : `1 (tower_bwd F p) = `1 p := eq_refl.

(** ** (G) A tower whose limit is not a singleton *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The constant tower is [Functor/Diagonal.v]'s diagonal at the shape,
   consumed rather than rebuilt: its arrow action is [id] at every arrow,
   which is exactly the identity system. *)
Definition ConstTower (X : obj[Sets]) : Omega^op ⟶ Sets :=
  Diagonal (Omega^op) X.

Example const_tower_fmap (X : obj[Sets]) (n : nat) :
  fmap[ConstTower X] (tower_step n) = id[X] := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma const_string_compat (b : bool) :
  tower_compat (ConstTower bool_setoid_object) (fun _ : nat => b).
Proof. intros n; reflexivity. Qed.

Definition const_string (b : bool) :
  inverse_limit (ConstTower bool_setoid_object) :=
  (fun _ => b; const_string_compat b).

Example const_string_coord (b : bool) (n : nat) :
  tower_proj (ConstTower bool_setoid_object) n (const_string b) = b
  := eq_refl.

(* Two provably distinct points of the inverse limit. *)
Lemma const_string_separates :
  const_string true ≈ const_string false → False.
Proof. intros H; specialize (H 0%nat); discriminate H. Qed.

(** ** (H) Streams: the classical tower, and the comparison map *)


Section StreamTower.

Context (A : SetoidObject@{Set Set}).

Definition StreamTower : Omega^op ⟶ Sets@{Set _} := Cochain (StreamF A).

Example stream_tower_zero :
  fobj[StreamTower] 0%nat = @terminal_obj Sets Sets_Terminal := eq_refl.

Example stream_tower_succ (n : nat) :
  fobj[StreamTower] (S n)
  = @product_obj Sets Sets_Cartesian A (fobj[StreamTower] n) := eq_refl.

Fixpoint stream_trunc (n : nat) (s : Stream A) : fobj[StreamTower] n :=
  match n as m return fobj[StreamTower] m with
  | O   => ttt
  | S k => (shead A s, stream_trunc k (stail A s))
  end.

Lemma stream_trunc_compat (s : Stream A) :
  tower_compat StreamTower (fun n => stream_trunc n s).
Proof.
  intros n; revert s.
  induction n as [| k IH]; intros s; simpl.
  - destruct (fmap[StreamTower] (tower_step 0%nat) (stream_trunc 1%nat s)).
    reflexivity.
  - split; [reflexivity | exact (IH (stail A s))].
Qed.

Lemma stream_trunc_respects (n : nat) (s t : Stream A)
  (H : bisim A s t) : stream_trunc n s ≈ stream_trunc n t.
Proof.
  revert s t H.
  induction n as [| k IH]; intros s t H; simpl.
  - destruct (stream_trunc 0%nat s), (stream_trunc 0%nat t); reflexivity.
  - split; [exact (bisim_head A H) | exact (IH _ _ (bisim_tail A H))].
Qed.

(*
   本节说明（余）极限、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition stream_to_tower :
  Stream_SO A ~{Sets}~> inverse_limit StreamTower := {|
  morphism := fun s => (fun n => stream_trunc n s ; stream_trunc_compat s)
|}.
Next Obligation. intros s t Hst n; exact (stream_trunc_respects n s t Hst). Qed.

(* Its coordinates are the truncations, on the nose. *)
Example stream_to_tower_coord (s : Stream A) (n : nat) :
  tower_proj StreamTower n (stream_to_tower s) = stream_trunc n s := eq_refl.

Example stream_to_tower_one (s : Stream A) :
  tower_proj StreamTower 1%nat (stream_to_tower s) = (shead A s, ttt)
  := eq_refl.

End StreamTower.
