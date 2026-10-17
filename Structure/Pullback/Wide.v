Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.

Generalizable All Variables.

(** * Wide pullbacks, and products as wide pullbacks over a terminal object *)

(*
   nLab:      https://ncatlab.org/nlab/show/pullback
   Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

   本文件给出 wide 相关构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The elementary universal property *)

(*
   本节说明拉回/推出、等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record IsWidePullback {C : Category} {I : Type} {A : I → C} {z : C}
  (f : ∀ i : I, A i ~> z) (P : C) (p : ∀ i : I, P ~> A i) := {
  (* every leg is carried to the common codomain in the same way *)
  wpull_commutes : ∀ i j : I, f i ∘ p i ≈ f j ∘ p j;

  (* universal property: every jointly agreeing family factors uniquely *)
  wpull_ump {Q : C} (q : ∀ i : I, Q ~> A i)
    (Hq : ∀ i j : I, f i ∘ q i ≈ f j ∘ q j) :
    ∃! u : Q ~> P, ∀ i : I, p i ∘ u ≈ q i
}.

Arguments wpull_commutes {_ _ _ _ _ _ _} _ _ _.
Arguments wpull_ump {_ _ _ _ _ _ _} _ {_} _ _.

(** ** The bundled record *)

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record WidePullback {C : Category} {I : Type} {A : I → C} {z : C}
  (f : ∀ i : I, A i ~> z) := {
  WPull : C;                             (* the wide pullback object *)
  wide_pullback_proj : ∀ i : I, WPull ~> A i;   (* the projections *)

  wide_pullback_commutes : ∀ i j : I,
    f i ∘ wide_pullback_proj i ≈ f j ∘ wide_pullback_proj j;

  ump_wide_pullbacks : ∀ (Q : C) (q : ∀ i : I, Q ~> A i),
    (∀ i j : I, f i ∘ q i ≈ f j ∘ q j)
    → ∃! u : Q ~> WPull, ∀ i : I, wide_pullback_proj i ∘ u ≈ q i
}.

Arguments WPull {_ _ _ _ _} _.
Arguments wide_pullback_proj {_ _ _ _ _} _ _.
Arguments wide_pullback_commutes {_ _ _ _ _} _ _ _.
Arguments ump_wide_pullbacks {_ _ _ _ _} _ _ _ _.

Coercion WPull : WidePullback >-> obj.

(* Both conversions are field repackagings, mirroring
   [pullback_is_pullback] and [is_pullback_pullback] of
   Theory/Morphisms/Stability.v. *)

Definition wide_pullback_is_pullback {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} (W : WidePullback f) :
  IsWidePullback f (WPull W) (wide_pullback_proj W) :=
  {| wpull_commutes := wide_pullback_commutes W
   ; wpull_ump      := fun Q q Hq => ump_wide_pullbacks W Q q Hq |}.

Definition is_wide_pullback_pullback {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} {P : C} {p : ∀ i : I, P ~> A i}
  (W : IsWidePullback f P p) : WidePullback f :=
  {| WPull                  := P
   ; wide_pullback_proj     := p
   ; wide_pullback_commutes := wpull_commutes W
   ; ump_wide_pullbacks     := fun Q q Hq => wpull_ump W q Hq |}.

(* MEASURED STRICT: both composites are the identity on the nose, on the
   WHOLE record, because both records have primitive projections with eta.
   Neither is merely an equivalence up to ≈. *)

Example wide_pullback_predicate_round {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} {P : C} {p : ∀ i : I, P ~> A i}
  (W : IsWidePullback f P p) :
  wide_pullback_is_pullback (is_wide_pullback_pullback W) = W := eq_refl.

Example wide_pullback_bundled_round {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} (W : WidePullback f) :
  is_wide_pullback_pullback (wide_pullback_is_pullback W) = W := eq_refl.

(*
   本节说明拉回/推出、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class HasWidePullbacks (C : Category) := {
  wide_pullback {I : Type} {A : I → C} {z : C} (f : ∀ i : I, A i ~> z) :
    WidePullback f
}.

Arguments wide_pullback {C _ I A z} f.

(** ** The projections are jointly monic *)

(*
   本节说明始/终对象、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma wide_pullback_jointly_monic {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} {P : C} {p : ∀ i : I, P ~> A i}
  (W : IsWidePullback f P p) {Q : C} (u v : Q ~> P)
  (Hd : ∀ i : I, p i ∘ u ≈ p i ∘ v) : u ≈ v.
Proof.
  assert (Hq : ∀ i j : I, f i ∘ (p i ∘ u) ≈ f j ∘ (p j ∘ u)).
  { intros i j.
    rewrite !comp_assoc.
    now rewrite (wpull_commutes W i j). }
  transitivity (unique_obj (wpull_ump W (fun i => p i ∘ u) Hq)).
  - symmetry.
    apply (uniqueness (wpull_ump W (fun i => p i ∘ u) Hq)).
    intro i; reflexivity.
  - apply (uniqueness (wpull_ump W (fun i => p i ∘ u) Hq)).
    intro i; symmetry; apply Hd.
Qed.

(** ** Wide pullbacks are unique up to isomorphism *)

(*
   本节说明 Wide 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma wide_pullback_unique {C : Category} {I : Type} {A : I → C} {z : C}
  {f : ∀ i : I, A i ~> z} {P1 P2 : C}
  {p1 : ∀ i : I, P1 ~> A i} {p2 : ∀ i : I, P2 ~> A i}
  (W1 : IsWidePullback f P1 p1) (W2 : IsWidePullback f P2 p2) : P1 ≅ P2.
Proof.
  pose proof (wpull_ump W2 p1 (wpull_commutes W1)) as D12.
  pose proof (wpull_ump W1 p2 (wpull_commutes W2)) as D21.
  pose proof (wpull_ump W1 p1 (wpull_commutes W1)) as D11.
  pose proof (wpull_ump W2 p2 (wpull_commutes W2)) as D22.
  unshelve refine {| to := unique_obj D12; from := unique_obj D21 |}.
  - transitivity (unique_obj D22).
    + symmetry.
      apply (uniqueness D22).
      intro i.
      rewrite comp_assoc, (unique_property D12 i).
      exact (unique_property D21 i).
    + apply (uniqueness D22).
      intro i; apply id_right.
  - transitivity (unique_obj D11).
    + symmetry.
      apply (uniqueness D11).
      intro i.
      rewrite comp_assoc, (unique_property D21 i).
      exact (unique_property D12 i).
    + apply (uniqueness D11).
      intro i; apply id_right.
Defined.

(** ** The empty index: the wide pullback is the terminal object *)

(* Over an empty index there is exactly one family of legs into any apex,
   namely the empty function. *)
Definition wpull_empty_legs {C : Category} {I : Type} {A : I → C}
  (Hempty : I → False) (Q : C) : ∀ i : I, Q ~> A i.
Proof. intro i; destruct (Hempty i). Defined.

(* ... and it agrees with itself vacuously. *)
Lemma wpull_empty_comm {C : Category} {I : Type} {A : I → C} {z : C}
  (f : ∀ i : I, A i ~> z) (Hempty : I → False) {Q : C}
  (q : ∀ i : I, Q ~> A i) : ∀ i j : I, f i ∘ q i ≈ f j ∘ q j.
Proof. intros i j; destruct (Hempty i). Qed.

(*
   本节说明拉回/推出、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma wide_pullback_empty_terminal {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} {P : C} {p : ∀ i : I, P ~> A i}
  (Hempty : I → False) (W : IsWidePullback f P p) : IsTerminalObj P.
Proof.
  intro Q.
  pose proof (wpull_ump W (wpull_empty_legs Hempty Q)
                (wpull_empty_comm f Hempty (wpull_empty_legs Hempty Q)))
    as U.
  unshelve eapply Build_Unique.
  - exact (unique_obj U).
  - exact Logic.I.
  - intros v _.
    apply (uniqueness U).
    intro i; destruct (Hempty i).
Defined.

(* Conversely a terminal object is a wide pullback of the empty family over
   ANY codomain, with its (empty) family of projections.  Emptiness is used
   twice, once for each field. *)
Definition terminal_wide_pullback_empty {C : Category} {I : Type}
  {A : I → C} {z : C} (f : ∀ i : I, A i ~> z) {P : C}
  (p : ∀ i : I, P ~> A i) (Hempty : I → False) (H : IsTerminalObj P) :
  IsWidePullback f P p.
Proof.
  unshelve refine {| wpull_commutes := _ |}.
  - intros i j; destruct (Hempty i).
  - intros Q q Hq.
    unshelve eapply Build_Unique.
    + exact (is_terminal_one H).
    + intro i; destruct (Hempty i).
    + intros v _; apply (is_terminal_unique H).
Defined.

(** ** Riehl's lemma: products are wide pullbacks over a terminal object *)

(*
   本节说明拉回/推出、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem wide_pullback_product {C : Category} `{T : @Terminal C}
  {I : Type} (A : I → C) (P : C) (p : ∀ i : I, P ~> A i)
  (H : IsIndexedProduct A P p) :
  IsWidePullback (fun i : I => @one C T (A i)) P p.
Proof.
  unshelve refine {| wpull_commutes := _ |}.
  - (* both composites are maps into 1, hence equal *)
    intros i j.
    apply (@one_unique C T).
  - (* the hypothesis [Hq] is discarded: it says nothing over 1 *)
    intros Q q _.
    exact (iprod_desc H q).
Defined.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem product_wide_pullback {C : Category} `{T : @Terminal C}
  {I : Type} (A : I → C) (P : C) (p : ∀ i : I, P ~> A i)
  (W : IsWidePullback (fun i : I => @one C T (A i)) P p) :
  IsIndexedProduct A P p.
Proof.
  unshelve refine {| iprod_desc := _ |}.
  intros c pi.
  refine (wpull_ump W pi _).
  (* the condition Riehl observes to be no condition at all *)
  intros i j.
  apply (@one_unique C T).
Defined.

(** ** The binary specialization *)

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition two_fam {C : Category} (x y : C) : bool → C :=
  fun b => if b then x else y.

Definition two_maps {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z) :
  ∀ b : bool, two_fam x y b ~> z :=
  fun b => if b as b' return (two_fam x y b' ~> z) then f else g.

Definition two_legs {C : Category} {x y P : C} (p1 : P ~> x) (p2 : P ~> y) :
  ∀ b : bool, P ~> two_fam x y b :=
  fun b => if b as b' return (P ~> two_fam x y b') then p1 else p2.

Theorem wide_pullback_binary {C : Category} {x y z : C}
  {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
  (W : IsWidePullback (two_maps f g) P (two_legs p1 p2)) :
  IsPullback f g P p1 p2.
Proof.
  unshelve refine {| is_pullback_commutes := _ |}.
  - (* the square is the [∀ i j] condition at [true], [false] *)
    exact (wpull_commutes W true false).
  - intros Q q1 q2 Hq.
    assert (Hc : ∀ i j : bool,
              two_maps f g i ∘ two_legs q1 q2 i
                ≈ two_maps f g j ∘ two_legs q1 q2 j).
    { intros i j; destruct i, j; simpl;
        [ reflexivity | exact Hq | now symmetry | reflexivity ]. }
    pose proof (wpull_ump W (two_legs q1 q2) Hc) as U.
    unshelve eapply Build_Unique.
    + exact (unique_obj U).
    + split.
      * exact (unique_property U true).
      * exact (unique_property U false).
    + intros v [Hv1 Hv2].
      apply (uniqueness U).
      intro b; destruct b; assumption.
Defined.

Theorem binary_wide_pullback {C : Category} {x y z : C}
  {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
  (H : IsPullback f g P p1 p2) :
  IsWidePullback (two_maps f g) P (two_legs p1 p2).
Proof.
  unshelve refine {| wpull_commutes := _ |}.
  - intros i j; destruct i, j; simpl;
      [ reflexivity
      | exact (is_pullback_commutes H)
      | now symmetry; exact (is_pullback_commutes H)
      | reflexivity ].
  - intros Q q Hq.
    pose proof (is_pullback_ump H Q (q true) (q false) (Hq true false)) as U.
    unshelve eapply Build_Unique.
    + exact (unique_obj U).
    + intro b; destruct b; simpl.
      * exact (fst (unique_property U)).
      * exact (snd (unique_property U)).
    + intros v Hv.
      apply (uniqueness U).
      split; [ exact (Hv true) | exact (Hv false) ].
Defined.

(*
   本节说明 Wide 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example wide_pullback_binary_commutes {C : Category} {x y z : C}
  {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
  (H : IsPullback f g P p1 p2) :
  is_pullback_commutes (wide_pullback_binary (binary_wide_pullback H))
  = is_pullback_commutes H := eq_refl.

(** ** Non-vacuity: the identification at [Sets] *)

(*
   本节说明拉回/推出、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_wide_pullback_over_one {A : Type} (F : A → obj[Sets]) :
  IsWidePullback (fun i : A => @one Sets Sets_Terminal (F i))
    (Sets_iprod_obj F) (Sets_iprod_proj F) :=
  wide_pullback_product F (Sets_iprod_obj F) (Sets_iprod_proj F)
    (Sets_IsIndexedProduct F).

(* ... and the converse direction is available at the same witness, so the
   two readings of that object genuinely coincide in a concrete category
   rather than only in the abstract statement. *)
Definition Sets_iprod_of_wide_pullback {A : Type} (F : A → obj[Sets]) :
  IsIndexedProduct F (Sets_iprod_obj F) (Sets_iprod_proj F) :=
  product_wide_pullback F (Sets_iprod_obj F) (Sets_iprod_proj F)
    (Sets_wide_pullback_over_one F).
