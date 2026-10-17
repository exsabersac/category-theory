Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Theory.Bicategory.

Generalizable All Variables.

(*
   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Infix "∘∘" := vcompose : category_scope.
Notation "f ∘∘∘ g" := (hcompose (f, g)) : category_scope.

(** Adjunctions inside a bicategory *)

(*
   nLab: https://ncatlab.org/nlab/show/adjunction+in+a+bicategory

   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section BicatAdjunction.

Context {B : Bicategory}.

(* ------------------------------------------------------------------ *)
(* The Godement / interchange calculus of `hcomp2`.                    *)
(*                                                                     *)
(* `hcomp2 θ η` is by definition `fmap[hcompose] (θ, η)`, so its whole *)
(* algebra functoriality horizontal-复合 函子 （已译） *)
(* 相关说明。 （已译） *)
(* category `bicat y z ∏ bicat x y`. These lemmas package that algebra *)
(* 相关说明。 （已译） *)
(* ------------------------------------------------------------------ *)

(* `hcomp2` respects `≈` in each argument (it is the action of a functor). *)
#[local] Instance hcomp2_respects
  {x y z : bi0cell} {g g' : bicat y z} {f f' : bicat x y} :
  Proper (equiv ==> equiv ==> equiv) (@hcomp2 B x y z g g' f f').
Proof.
  proper.
  exact (@fmap_respects _ _ (@hcompose B x y z)
           (g, f) (g', f') (x0, x1) (y0, y1) (X, X0)).
Qed.

(* The horizontal 复合 恒等 2-cells 恒等 2-cell the
 horizontal 复合 1-cell (`hcompose` preserves identities). （已译） *)
Lemma hcomp2_id {x y z : bi0cell} (g : bicat y z) (f : bicat x y) :
  hcomp2 (bi2id (a:=g)) (bi2id (a:=f)) ≈ bi2id (a:=g ∘∘∘ f).
Proof. exact (@fmap_id _ _ (@hcompose B x y z) (g, f)). Qed.

(* Interchange: horizontal 复合 vertical composites vertical
 复合 horizontal composites (`hcompose` preserves 复合). （已译） *)
Lemma hcomp2_comp {x y z : bi0cell}
  {g g' g'' : bicat y z} {f f' f'' : bicat x y}
  (θ' : g' ~> g'') (θ : g ~> g') (η' : f' ~> f'') (η : f ~> f') :
  hcomp2 (θ' ∘∘ θ) (η' ∘∘ η) ≈ hcomp2 θ' η' ∘∘ hcomp2 θ η.
Proof.
  exact (@fmap_comp _ _ (@hcompose B x y z)
           (g, f) (g', f') (g'', f'') (θ', η') (θ, η)).
Qed.

(* 相关说明。 （已译） *)
Definition lwhisker {x y z : bi0cell} (g : bicat y z) {f f' : bicat x y}
  (η : f ~> f') : (g ∘∘∘ f) ~> (g ∘∘∘ f') := hcomp2 (bi2id (a:=g)) η.

Definition rwhisker {x y z : bi0cell} {g g' : bicat y z} (θ : g ~> g')
  (f : bicat x y) : (g ∘∘∘ f) ~> (g' ∘∘∘ f) := hcomp2 θ (bi2id (a:=f)).

Lemma lwhisker_id {x y z : bi0cell} (g : bicat y z) (f : bicat x y) :
  lwhisker g (bi2id (a:=f)) ≈ bi2id.
Proof. exact (hcomp2_id g f). Qed.

Lemma rwhisker_id {x y z : bi0cell} (g : bicat y z) (f : bicat x y) :
  rwhisker (bi2id (a:=g)) f ≈ bi2id.
Proof. exact (hcomp2_id g f). Qed.

Lemma lwhisker_comp {x y z : bi0cell} (g : bicat y z)
  {f f' f'' : bicat x y} (η' : f' ~> f'') (η : f ~> f') :
  lwhisker g (η' ∘∘ η) ≈ lwhisker g η' ∘∘ lwhisker g η.
Proof.
  unfold lwhisker.
  rewrite <- (bi2id_left (bi2id (a:=g))) at 1.
  now rewrite hcomp2_comp.
Qed.

Lemma rwhisker_comp {x y z : bi0cell}
  {g g' g'' : bicat y z} (θ' : g' ~> g'') (θ : g ~> g') (f : bicat x y) :
  rwhisker (θ' ∘∘ θ) f ≈ rwhisker θ' f ∘∘ rwhisker θ f.
Proof.
  unfold rwhisker.
  rewrite <- (bi2id_left (bi2id (a:=f))) at 1.
  now rewrite hcomp2_comp.
Qed.

(* Whiskering respects `≈` in its 2-cell argument. Stated as congruence lemmas
   (rather than `Proper` instances) because a whisker's result type depends on
   the 1-cell argument, which blocks the pointwise `Proper` search; these support
   whole-term rewrites of a whisker in a composite. *)
Lemma lwhisker_cong {x y z : bi0cell} (g : bicat y z) {f f' : bicat x y}
  (η η' : f ~> f') : η ≈ η' → lwhisker g η ≈ lwhisker g η'.
Proof. intro E; unfold lwhisker; now rewrite E. Qed.

Lemma rwhisker_cong {x y z : bi0cell} {g g' : bicat y z} (θ θ' : g ~> g')
  (f : bicat x y) : θ ≈ θ' → rwhisker θ f ≈ rwhisker θ' f.
Proof. intro E; unfold rwhisker; now rewrite E. Qed.

(* A general horizontal 复合 factors right whisker followed left
 whisker, either order (the two orders agreeing interchange law). （已译） *)
Lemma hcomp2_lwhisker_rwhisker {x y z : bi0cell}
  {g g' : bicat y z} {f f' : bicat x y} (θ : g ~> g') (η : f ~> f') :
  hcomp2 θ η ≈ lwhisker g' η ∘∘ rwhisker θ f.
Proof.
  unfold lwhisker, rwhisker.
  rewrite <- hcomp2_comp.
  now rewrite bi2id_left, bi2id_right.
Qed.

Lemma hcomp2_rwhisker_lwhisker {x y z : bi0cell}
  {g g' : bicat y z} {f f' : bicat x y} (θ : g ~> g') (η : f ~> f') :
  hcomp2 θ η ≈ rwhisker θ f' ∘∘ lwhisker g η.
Proof.
  unfold lwhisker, rwhisker.
  rewrite <- hcomp2_comp.
  now rewrite bi2id_left, bi2id_right.
Qed.

(* The middle-four interchange whisker form: two whiskers 2-cell by
 two legs horizontal 复合 commute past one another. （已译） *)
Lemma whisker_exchange {x y z : bi0cell}
  {g g' : bicat y z} {f f' : bicat x y} (θ : g ~> g') (η : f ~> f') :
  lwhisker g' η ∘∘ rwhisker θ f ≈ rwhisker θ f' ∘∘ lwhisker g η.
Proof.
  rewrite <- hcomp2_lwhisker_rwhisker.
  now rewrite hcomp2_rwhisker_lwhisker.
Qed.

(*
   本节说明 Adjunction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)
Lemma assoc_nat_top {w x' y' z' : bi0cell} {h h' : bicat y' z'}
  (θ : h ~> h') (g : bicat x' y') (k : bicat w x') :
  rwhisker θ (g ∘∘∘ k) ∘∘ to (hassoc h g k)
    ≈ to (hassoc h' g k) ∘∘ rwhisker (rwhisker θ g) k.
Proof.
  pose proof (hassoc_natural θ (bi2id (a:=g)) (bi2id (a:=k))) as HN.
  now rewrite hcomp2_id in HN.
Qed.

(* 相关说明。 （已译） *)
Lemma assoc_nat_mid {w x' y' z' : bi0cell} (h : bicat y' z')
  {g g' : bicat x' y'} (γ : g ~> g') (k : bicat w x') :
  lwhisker h (rwhisker γ k) ∘∘ to (hassoc h g k)
    ≈ to (hassoc h g' k) ∘∘ rwhisker (lwhisker h γ) k.
Proof.
  pose proof (hassoc_natural (bi2id (a:=h)) γ (bi2id (a:=k))) as HN.
  now unfold lwhisker, rwhisker.
Qed.

(* 相关说明。 （已译） *)
Lemma assoc_nat_bot {w x' y' z' : bi0cell} (h : bicat y' z')
  (g : bicat x' y') {k k' : bicat w x'} (η : k ~> k') :
  lwhisker h (lwhisker g η) ∘∘ to (hassoc h g k)
    ≈ to (hassoc h g k') ∘∘ lwhisker (h ∘∘∘ g) η.
Proof.
  pose proof (hassoc_natural (bi2id (a:=h)) (bi2id (a:=g)) η) as HN.
  now rewrite hcomp2_id in HN.
Qed.

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma vto_vfrom {x y : bi0cell} {A A' : bicat x y} (i : A ≅[bicat x y] A') :
  to i ∘∘ from i ≈ bi2id.
Proof. exact (iso_to_from i). Qed.

Lemma vfrom_vto {x y : bi0cell} {A A' : bicat x y} (i : A ≅[bicat x y] A') :
  from i ∘∘ to i ≈ bi2id.
Proof. exact (iso_from_to i). Qed.

(*
   本节说明 Adjunction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma iso_conj_from {x y : bi0cell} {A A' Bb Bb' : bicat x y}
  (i : A ≅[bicat x y] Bb) (i' : A' ≅[bicat x y] Bb')
  (η : Bb ~> Bb') (θ : A ~> A') :
  η ∘∘ to i ≈ to i' ∘∘ θ → from i' ∘∘ η ≈ θ ∘∘ from i.
Proof.
  intro HN.
  transitivity ((from i' ∘∘ η) ∘∘ (to i ∘∘ from i)).
  { rewrite vto_vfrom. now rewrite bi2id_right. }
  transitivity (from i' ∘∘ ((η ∘∘ to i) ∘∘ from i)).
  { now rewrite !vcompose_assoc. }
  rewrite HN.
  transitivity ((from i' ∘∘ to i') ∘∘ (θ ∘∘ from i)).
  { now rewrite !vcompose_assoc. }
  rewrite vfrom_vto.
  now rewrite bi2id_left.
Qed.

(* Inverse-direction unitor naturalities, as instances of `iso_conj_from`. *)
Lemma hunit_left_from_natural {x y : bi0cell} {f f' : bicat x y}
  (η : f ~> f') :
  from (hunit_left f') ∘∘ η ≈ lwhisker bi1id η ∘∘ from (hunit_left f).
Proof. exact (iso_conj_from _ _ _ _ (hunit_left_natural η)). Qed.

Lemma hunit_right_from_natural {x y : bi0cell} {f f' : bicat x y}
  (η : f ~> f') :
  from (hunit_right f') ∘∘ η ≈ rwhisker η bi1id ∘∘ from (hunit_right f).
Proof. exact (iso_conj_from _ _ _ _ (hunit_right_natural η)). Qed.

(*
   本节说明 Adjunction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma hunit_left_nat {x y : bi0cell} {f f' : bicat x y} (η : f ~> f') :
  η ∘∘ to (hunit_left f) ≈ to (hunit_left f') ∘∘ lwhisker bi1id η.
Proof. exact (hunit_left_natural η). Qed.

Lemma hunit_right_nat {x y : bi0cell} {f f' : bicat x y} (η : f ~> f') :
  η ∘∘ to (hunit_right f) ≈ to (hunit_right f') ∘∘ rwhisker η bi1id.
Proof. exact (hunit_right_natural η). Qed.

(* ------------------------------------------------------------------ *)
(* The adjunction class.                                               *)
(* ------------------------------------------------------------------ *)

(*
   本节说明 Adjunction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class BicatAdjunction {x y : bi0cell} (f : bicat x y) (u : bicat y x) := {
  adj_unit   : bi1id ~{bicat x x}~> (u ∘∘∘ f);   (* η : Id_x ⟹ u ∘ f *)
  adj_counit : (f ∘∘∘ u) ~{bicat y y}~> bi1id;   (* ε : f ∘ u ⟹ Id_y *)

  (* Left triangle: (ε ⊳ f) ∘ α⁻¹ ∘ (f ⊲ η) conjugated by ρ⁻¹ and λ is id[f]. *)
  adj_triangle_left :
    to (hunit_left f)
      ∘∘ hcomp2 adj_counit (bi2id (a:=f))
      ∘∘ from (hassoc f u f)
      ∘∘ hcomp2 (bi2id (a:=f)) adj_unit
      ∘∘ from (hunit_right f)
    ≈ bi2id (a:=f);

  (* Right triangle: (u ⊲ ε) ∘ α ∘ (η ⊳ u) conjugated by λ⁻¹ and ρ is id[u]. *)
  adj_triangle_right :
    to (hunit_right u)
      ∘∘ hcomp2 (bi2id (a:=u)) adj_counit
      ∘∘ to (hassoc u f u)
      ∘∘ hcomp2 adj_unit (bi2id (a:=u))
      ∘∘ from (hunit_left u)
    ≈ bi2id (a:=u)
}.

End BicatAdjunction.

Arguments BicatAdjunction {B x y} f u.
Arguments adj_unit {B x y} f u {_}.
Arguments adj_counit {B x y} f u {_}.
Arguments adj_triangle_left {B x y} f u {_}.
Arguments adj_triangle_right {B x y} f u {_}.

(** Uniqueness of adjoints up to invertible 2-cell *)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section AdjointUniqueness.

Context {B : Bicategory}.
Context {x y : bi0cell}.
Context {f : bicat x y}.

(* Readable accessors unit, counit right triangle 伴随
 supplied explicit 假设. （已译） *)
Definition uη {a : bicat y x} (A : BicatAdjunction f a)
  : bi1id ~{bicat x x}~> (a ∘∘∘ f) := @adj_unit B x y f a A.
Definition uε {a : bicat y x} (A : BicatAdjunction f a)
  : (f ∘∘∘ a) ~{bicat y y}~> bi1id := @adj_counit B x y f a A.

(* The comparison 2-cell (mate 恒等) `a` `b`. （已译） *)
Definition matecell {a b : bicat y x}
  (Aa : BicatAdjunction f a) (Ab : BicatAdjunction f b) : a ~{bicat y x}~> b :=
  to (hunit_right b)
    ∘∘ lwhisker b (uε Aa)
    ∘∘ to (hassoc b f a)
    ∘∘ rwhisker (uη Ab) a
    ∘∘ from (hunit_left a).

(* `matecell Aa Aa` is the right-triangle composite of `Aa`, hence `id`. *)
Lemma matecell_id {a : bicat y x} (Aa : BicatAdjunction f a) :
  matecell Aa Aa ≈ bi2id.
Proof.
  unfold matecell, lwhisker, rwhisker, uε, uη.
  exact (@adj_triangle_right B x y f a Aa).
Qed.

(* Characterisation: any unit-compatible 2-cell equals the mate. *)
Lemma mate_charac {a b : bicat y x}
  (Aa : BicatAdjunction f a) (Ab : BicatAdjunction f b) (γ : a ~> b) :
  rwhisker γ f ∘∘ uη Aa ≈ uη Ab → γ ≈ matecell Aa Ab.
Proof.
  intro H.
  (* Split whiskered unit `b` using unit-compatibility 假设. （已译） *)
  assert (Hb : rwhisker (uη Ab) a
                 ≈ rwhisker (rwhisker γ f) a ∘∘ rwhisker (uη Aa) a).
  { rewrite <- rwhisker_comp. apply rwhisker_cong. now symmetry. }
  symmetry.
  unfold matecell.
  rewrite Hb.
  (* Slide γ leftwards across the associator (assoc_nat_top). *)
  transitivity
    (to (hunit_right b) ∘∘ (lwhisker b (uε Aa)
       ∘∘ ((to (hassoc b f a) ∘∘ rwhisker (rwhisker γ f) a)
             ∘∘ (rwhisker (uη Aa) a ∘∘ from (hunit_left a))))).
  { now rewrite !vcompose_assoc. }
  transitivity
    (to (hunit_right b) ∘∘ (lwhisker b (uε Aa)
       ∘∘ ((rwhisker γ (f ∘∘∘ a) ∘∘ to (hassoc a f a))
             ∘∘ (rwhisker (uη Aa) a ∘∘ from (hunit_left a))))).
  { now rewrite <- (assoc_nat_top γ f a). }
  (* Exchange the counit whisker of `b` past γ (whisker_exchange). *)
  transitivity
    (to (hunit_right b) ∘∘ ((lwhisker b (uε Aa) ∘∘ rwhisker γ (f ∘∘∘ a))
       ∘∘ (to (hassoc a f a)
             ∘∘ (rwhisker (uη Aa) a ∘∘ from (hunit_left a))))).
  { now rewrite !vcompose_assoc. }
  transitivity
    (to (hunit_right b) ∘∘ ((rwhisker γ bi1id ∘∘ lwhisker a (uε Aa))
       ∘∘ (to (hassoc a f a)
             ∘∘ (rwhisker (uη Aa) a ∘∘ from (hunit_left a))))).
  { now rewrite (whisker_exchange γ (uε Aa)). }
  (* Slide γ out through the right unitor (hunit_right_nat). *)
  transitivity
    ((to (hunit_right b) ∘∘ rwhisker γ bi1id) ∘∘ (lwhisker a (uε Aa)
       ∘∘ (to (hassoc a f a)
             ∘∘ (rwhisker (uη Aa) a ∘∘ from (hunit_left a))))).
  { now rewrite !vcompose_assoc. }
  transitivity
    ((γ ∘∘ to (hunit_right a)) ∘∘ (lwhisker a (uε Aa)
       ∘∘ (to (hassoc a f a)
             ∘∘ (rwhisker (uη Aa) a ∘∘ from (hunit_left a))))).
  { now rewrite <- (hunit_right_nat γ). }
  (* The remaining factor right triangle `Aa`, hence 恒等. （已译） *)
  transitivity (γ ∘∘ matecell Aa Aa).
  { unfold matecell. now rewrite !vcompose_assoc. }
  rewrite matecell_id.
  now rewrite bi2id_right.
Qed.

(* ------------------------------------------------------------------ *)
(* Derived unit-coherence lemmas of the ambient bicategory.            *)
(*                                                                     *)
(* 相关说明。 （已译） *)
(* pentagon coherences; they do not mention the adjunction data. They  *)
(* 相关说明。 （已译） *)
(* 相关说明。 （已译） *)
(* 相关说明。 （已译） *)
(* ------------------------------------------------------------------ *)

(* Right cancellation of a 2-cell that carries a chosen right inverse. *)
Lemma vcancel_r {x' y' : bi0cell} {A0 A1 A2 : bicat x' y'}
  (p q : A1 ~> A2) (m : A0 ~> A1) (n : A1 ~> A0) :
  m ∘∘ n ≈ bi2id → p ∘∘ m ≈ q ∘∘ m → p ≈ q.
Proof.
  intros Hmn H.
  transitivity (p ∘∘ (m ∘∘ n)).
  { rewrite Hmn. now rewrite bi2id_right. }
  transitivity ((p ∘∘ m) ∘∘ n).
  { now rewrite vcompose_assoc. }
  rewrite H.
  transitivity (q ∘∘ (m ∘∘ n)).
  { now rewrite <- vcompose_assoc. }
  rewrite Hmn. now rewrite bi2id_right.
Qed.

(* Left cancellation of a 2-cell that carries a chosen left inverse. *)
Lemma vcancel_l {x' y' : bi0cell} {A0 A1 A2 : bicat x' y'}
  (p q : A0 ~> A1) (m : A1 ~> A2) (n : A2 ~> A1) :
  n ∘∘ m ≈ bi2id → m ∘∘ p ≈ m ∘∘ q → p ≈ q.
Proof.
  intros Hnm H.
  transitivity ((n ∘∘ m) ∘∘ p).
  { rewrite Hnm. now rewrite bi2id_left. }
  transitivity (n ∘∘ (m ∘∘ p)).
  { now rewrite <- vcompose_assoc. }
  rewrite H.
  transitivity ((n ∘∘ m) ∘∘ q).
  { now rewrite vcompose_assoc. }
  rewrite Hnm. now rewrite bi2id_left.
Qed.

(* Left-whiskering by the unit 1-cell is faithful: it reflects `≈`. *)
Lemma lwhisker_unit_faithful {x' y' : bi0cell} {A A' : bicat x' y'}
  (u v : A ~> A') :
  lwhisker bi1id u ≈ lwhisker bi1id v → u ≈ v.
Proof.
  intro H.
  apply (vcancel_r u v (to (hunit_left A)) (from (hunit_left A))).
  - exact (vto_vfrom (hunit_left A)).
  - rewrite (hunit_left_nat u), H. now rewrite <- (hunit_left_nat v).
Qed.

(* Right-whiskering by the unit 1-cell is faithful: it reflects `≈`. *)
Lemma rwhisker_unit_faithful {x' y' : bi0cell} {A A' : bicat x' y'}
  (u v : A ~> A') :
  rwhisker u bi1id ≈ rwhisker v bi1id → u ≈ v.
Proof.
  intro H.
  apply (vcancel_r u v (to (hunit_right A)) (from (hunit_right A))).
  - exact (vto_vfrom (hunit_right A)).
  - rewrite (hunit_right_nat u), H. now rewrite <- (hunit_right_nat v).
Qed.

(*
   本节说明 Adjunction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma tri_lr {x' y' z' : bi0cell} (g : bicat y' z') (k : bicat x' y') :
  rwhisker (to (hunit_right g)) k
    ≈ lwhisker g (to (hunit_left k)) ∘∘ to (hassoc g bi1id k).
Proof. exact (hcoherence_triangle g k). Qed.

Lemma pent_lr {v' w' x' y' z' : bi0cell}
  (k : bicat y' z') (h : bicat x' y') (g : bicat w' x') (l : bicat v' w') :
  lwhisker k (to (hassoc h g l))
    ∘∘ to (hassoc k (h ∘∘∘ g) l)
    ∘∘ rwhisker (to (hassoc k h g)) l
    ≈ to (hassoc k h (g ∘∘∘ l)) ∘∘ to (hassoc (k ∘∘∘ h) g l).
Proof. exact (hcoherence_pentagon k h g l). Qed.

(* Left-unit coherence (Kelly): left unitor whiskered right `k`
 agrees left unitor 复合, across associator. （已译） *)
Lemma left_unit_coherence {x' y' z' : bi0cell}
  (g : bicat y' z') (k : bicat x' y') :
  rwhisker (to (hunit_left g)) k
    ≈ to (hunit_left (g ∘∘∘ k)) ∘∘ to (hassoc bi1id g k).
Proof.
  apply lwhisker_unit_faithful.
  apply (vcancel_r _ _ (to (hassoc bi1id (bi1id ∘∘∘ g) k))
                       (from (hassoc bi1id (bi1id ∘∘∘ g) k))).
  { exact (vto_vfrom _). }
  apply (vcancel_r _ _ (rwhisker (to (hassoc bi1id bi1id g)) k)
                       (rwhisker (from (hassoc bi1id bi1id g)) k)).
  { rewrite <- rwhisker_comp.
    rewrite (rwhisker_cong _ _ k (vto_vfrom (hassoc bi1id bi1id g))).
    now rewrite rwhisker_id. }
  rewrite (assoc_nat_mid bi1id (to (hunit_left g)) k).
  rewrite <- vcompose_assoc.
  rewrite <- rwhisker_comp.
  rewrite <- (rwhisker_cong _ _ k (tri_lr bi1id g)).
  rewrite <- (assoc_nat_top (to (hunit_right bi1id)) g k).
  rewrite (tri_lr bi1id (g ∘∘∘ k)).
  rewrite <- vcompose_assoc.
  rewrite <- (pent_lr bi1id bi1id g k).
  rewrite !vcompose_assoc.
  now rewrite <- lwhisker_comp.
Qed.

(* Right-unit coherence (Kelly), 镜像 statement right unitor. （已译） *)
Lemma right_unit_coherence {x' y' z' : bi0cell}
  (g : bicat y' z') (k : bicat x' y') :
  lwhisker g (to (hunit_right k)) ∘∘ to (hassoc g k bi1id)
    ≈ to (hunit_right (g ∘∘∘ k)).
Proof.
  apply rwhisker_unit_faithful.
  apply (vcancel_l _ _ (to (hassoc g k bi1id)) (from (hassoc g k bi1id))).
  { exact (vfrom_vto (hassoc g k bi1id)). }
  rewrite rwhisker_comp.
  rewrite vcompose_assoc.
  rewrite <- (assoc_nat_mid g (to (hunit_right k)) bi1id).
  rewrite (lwhisker_cong g _ _ (tri_lr k bi1id)).
  rewrite lwhisker_comp.
  transitivity (lwhisker g (lwhisker k (to (hunit_left bi1id)))
    ∘∘ ((lwhisker g (to (hassoc k bi1id bi1id))
          ∘∘ to (hassoc g (k ∘∘∘ bi1id) bi1id))
          ∘∘ rwhisker (to (hassoc g k bi1id)) bi1id)).
  { now rewrite <- !vcompose_assoc. }
  rewrite (pent_lr g k bi1id bi1id).
  rewrite vcompose_assoc.
  rewrite (assoc_nat_bot g k (to (hunit_left bi1id))).
  rewrite <- vcompose_assoc.
  now rewrite <- (tri_lr (g ∘∘∘ k) bi1id).
Qed.

(* Unit-对象 coherence (Kelly): two unitors unit 1-cell agree. （已译） *)
Lemma unit_left_right_id {x' : bi0cell} :
  to (hunit_left (bi1id (x:=x'))) ≈ to (hunit_right (bi1id (x:=x'))).
Proof.
  apply rwhisker_unit_faithful.
  assert (Hδ : to (hunit_left (bi1id ∘∘∘ bi1id))
                 ≈ lwhisker bi1id (to (hunit_left (bi1id (x:=x'))))).
  { apply (vcancel_l _ _ (to (hunit_left bi1id)) (from (hunit_left bi1id))).
    - exact (vfrom_vto (hunit_left bi1id)).
    - exact (hunit_left_nat (to (hunit_left bi1id))). }
  rewrite (left_unit_coherence bi1id bi1id).
  rewrite Hδ.
  symmetry.
  apply tri_lr.
Qed.

(*
   本节说明 Adjunction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma left_unit_coherence_from {x' y' z' : bi0cell}
  (g : bicat y' z') (k : bicat x' y') :
  rwhisker (from (hunit_left g)) k
    ≈ from (hassoc bi1id g k) ∘∘ from (hunit_left (g ∘∘∘ k)).
Proof.
  apply (vcancel_r _ _ (rwhisker (to (hunit_left g)) k)
                       (rwhisker (from (hunit_left g)) k)).
  { rewrite <- rwhisker_comp.
    rewrite (rwhisker_cong _ _ k (vto_vfrom (hunit_left g))).
    now rewrite rwhisker_id. }
  rewrite <- rwhisker_comp.
  rewrite (rwhisker_cong _ _ k (vfrom_vto (hunit_left g))).
  rewrite rwhisker_id.
  rewrite (left_unit_coherence g k).
  rewrite <- !vcompose_assoc.
  rewrite (vcompose_assoc (from (hunit_left (g ∘∘∘ k)))
                          (to (hunit_left (g ∘∘∘ k)))
                          (to (hassoc bi1id g k))).
  rewrite vfrom_vto, bi2id_left.
  now rewrite vfrom_vto.
Qed.

(* Cancel `to`/`from` pair sitting at head right-nested 复合. （已译） *)
Lemma vcancel_tf {x' y' : bi0cell} {A0 A1 C : bicat x' y'}
  (i : A0 ≅[bicat x' y'] A1) (r : C ~> A1) :
  to i ∘∘ (from i ∘∘ r) ≈ r.
Proof. rewrite vcompose_assoc, vto_vfrom. now rewrite bi2id_left. Qed.

(*
   本节说明 Adjunction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma assoc_top_solve {w x' y' z' : bi0cell} {h h' : bicat y' z'}
  (θ : h ~> h') (g : bicat x' y') (l : bicat w x') :
  rwhisker (rwhisker θ g) l
    ≈ from (hassoc h' g l) ∘∘ (rwhisker θ (g ∘∘∘ l) ∘∘ to (hassoc h g l)).
Proof.
  apply (vcancel_l _ _ (to (hassoc h' g l)) (from (hassoc h' g l))).
  - exact (vfrom_vto _).
  - rewrite (vcancel_tf (hassoc h' g l)).
    symmetry. exact (assoc_nat_top θ g l).
Qed.

Lemma assoc_mid_solve {w x' y' z' : bi0cell} (h : bicat y' z')
  {g g' : bicat x' y'} (γ : g ~> g') (l : bicat w x') :
  rwhisker (lwhisker h γ) l
    ≈ from (hassoc h g' l) ∘∘ (lwhisker h (rwhisker γ l) ∘∘ to (hassoc h g l)).
Proof.
  apply (vcancel_l _ _ (to (hassoc h g' l)) (from (hassoc h g' l))).
  - exact (vfrom_vto _).
  - rewrite (vcancel_tf (hassoc h g' l)).
    symmetry. exact (assoc_nat_mid h γ l).
Qed.

(* 相关说明。 （已译） *)
Lemma pent_solve {v' w' x' y' z' : bi0cell}
  (k : bicat y' z') (h : bicat x' y') (g : bicat w' x') (l : bicat v' w') :
  rwhisker (to (hassoc k h g)) l
    ≈ from (hassoc k (h ∘∘∘ g) l)
        ∘∘ (lwhisker k (from (hassoc h g l))
             ∘∘ (to (hassoc k h (g ∘∘∘ l)) ∘∘ to (hassoc (k ∘∘∘ h) g l))).
Proof.
  apply (vcancel_l _ _ (lwhisker k (to (hassoc h g l)) ∘∘ to (hassoc k (h ∘∘∘ g) l))
                       (from (hassoc k (h ∘∘∘ g) l) ∘∘ lwhisker k (from (hassoc h g l)))).
  - rewrite <- !vcompose_assoc.
    rewrite (vcompose_assoc (lwhisker k (from (hassoc h g l)))
                            (lwhisker k (to (hassoc h g l)))
                            (to (hassoc k (h ∘∘∘ g) l))).
    rewrite <- lwhisker_comp.
    rewrite (lwhisker_cong k _ _ (vfrom_vto (hassoc h g l))).
    rewrite lwhisker_id, bi2id_left.
    now rewrite vfrom_vto.
  - rewrite (pent_lr k h g l).
    rewrite <- !vcompose_assoc.
    rewrite (vcancel_tf (hassoc k (h ∘∘∘ g) l)).
    rewrite (vcompose_assoc (lwhisker k (to (hassoc h g l)))
                            (lwhisker k (from (hassoc h g l))) _).
    rewrite <- lwhisker_comp.
    rewrite (lwhisker_cong k _ _ (vto_vfrom (hassoc h g l))).
    rewrite lwhisker_id, bi2id_left.
    reflexivity.
Qed.

(* 相关说明。 （已译） *)
Lemma mate_unit_compat {a b : bicat y x}
  (Aa : BicatAdjunction f a) (Ab : BicatAdjunction f b) :
  rwhisker (matecell Aa Ab) f ∘∘ uη Aa ≈ uη Ab.
Proof.
  (* Straighten `η_b ⊳ I` against inverse left unitor unit: the
 right unitor 自然性 `η_b` together `λ_I = ρ_I` turns it into
 `ρ_{b·f}⁻¹ ∘ η_b`. （已译） *)
  assert (Eη : rwhisker (uη Ab) bi1id ∘∘ from (hunit_left bi1id)
               ≈ from (hunit_right (b ∘∘∘ f)) ∘∘ uη Ab).
  { apply (vcancel_l _ _ (to (hunit_right (b ∘∘∘ f))) (from (hunit_right (b ∘∘∘ f)))).
    - exact (vfrom_vto _).
    - rewrite (vcancel_tf (hunit_right (b ∘∘∘ f))).
      rewrite vcompose_assoc.
      rewrite <- (hunit_right_nat (uη Ab)).
      rewrite <- vcompose_assoc.
      rewrite <- (unit_left_right_id (x':=x)).
      rewrite vto_vfrom.
      now rewrite bi2id_right. }
  (* 相关说明。 （已译） *)
  assert (Htri : ((to (hunit_left f) ∘∘ rwhisker (uε Aa) f) ∘∘ from (hassoc f a f))
                   ∘∘ lwhisker f (uη Aa)
                 ≈ to (hunit_right f)).
  { apply (vcancel_r _ _ (from (hunit_right f)) (to (hunit_right f))).
    - exact (vfrom_vto (hunit_right f)).
    - rewrite vto_vfrom. exact (@adj_triangle_left B x y f a Aa). }
  (* 相关说明。 （已译） *)
  assert (Etail :
    to (hassoc b f (a ∘∘∘ f))
      ∘∘ (rwhisker (uη Ab) (a ∘∘∘ f) ∘∘ (from (hunit_left (a ∘∘∘ f)) ∘∘ uη Aa))
    ≈ lwhisker b (lwhisker f (uη Aa))
      ∘∘ (to (hassoc b f bi1id) ∘∘ (from (hunit_right (b ∘∘∘ f)) ∘∘ uη Ab))).
  { rewrite (hunit_left_from_natural (uη Aa)).
    rewrite (vcompose_assoc (rwhisker (uη Ab) (a ∘∘∘ f))
                            (lwhisker bi1id (uη Aa)) (from (hunit_left bi1id))).
    rewrite <- (whisker_exchange (uη Ab) (uη Aa)).
    rewrite <- (vcompose_assoc (lwhisker (b ∘∘∘ f) (uη Aa))
                               (rwhisker (uη Ab) bi1id) (from (hunit_left bi1id))).
    rewrite Eη.
    rewrite (vcompose_assoc (to (hassoc b f (a ∘∘∘ f)))
                            (lwhisker (b ∘∘∘ f) (uη Aa))
                            (from (hunit_right (b ∘∘∘ f)) ∘∘ uη Ab)).
    rewrite <- (assoc_nat_bot b f (uη Aa)).
    now rewrite <- vcompose_assoc. }
  (*
   本节说明 Adjunction 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  unfold matecell.
  rewrite !rwhisker_comp.
  rewrite (tri_lr b f).
  rewrite (assoc_mid_solve b (uε Aa) f).
  rewrite (pent_solve b f a f).
  rewrite (assoc_top_solve (uη Ab) a f).
  rewrite (left_unit_coherence_from a f).
  rewrite <- !vcompose_assoc.
  rewrite (vcancel_tf (hassoc b bi1id f)).
  rewrite (vcancel_tf (hassoc b (f ∘∘∘ a) f)).
  rewrite (vcancel_tf (hassoc (b ∘∘∘ f) a f)).
  rewrite (vcancel_tf (hassoc bi1id a f)).
  rewrite Etail.
  rewrite !vcompose_assoc.
  rewrite <- !lwhisker_comp.
  rewrite (lwhisker_cong b _ _ Htri).
  rewrite (right_unit_coherence b f).
  rewrite vto_vfrom.
  now rewrite bi2id_left.
Qed.

(* Uniqueness adjoints: two right adjoints `f` related an
 invertible 2-cell, mate 恒等. （已译） *)
Theorem adjoint_unique {a b : bicat y x}
  (Aa : BicatAdjunction f a) (Ab : BicatAdjunction f b) :
  a ≅[bicat y x] b.
Proof.
  refine (@Build_Isomorphism (bicat y x) a b
            (matecell Aa Ab) (matecell Ab Aa) _ _).
  - (* matecell Aa Ab ∘∘ matecell Ab Aa ≈ id[b] *)
    transitivity (matecell Ab Ab).
    + refine (mate_charac Ab Ab (matecell Aa Ab ∘∘ matecell Ab Aa) _).
      rewrite rwhisker_comp.
      rewrite <- vcompose_assoc.
      rewrite (mate_unit_compat Ab Aa).
      now rewrite (mate_unit_compat Aa Ab).
    + exact (matecell_id Ab).
  - (* matecell Ab Aa ∘∘ matecell Aa Ab ≈ id[a] *)
    transitivity (matecell Aa Aa).
    + refine (mate_charac Aa Aa (matecell Ab Aa ∘∘ matecell Aa Ab) _).
      rewrite rwhisker_comp.
      rewrite <- vcompose_assoc.
      rewrite (mate_unit_compat Aa Ab).
      now rewrite (mate_unit_compat Ab Aa).
    + exact (matecell_id Aa).
Qed.

End AdjointUniqueness.

Arguments matecell {B x y f a b} Aa Ab.
Arguments adjoint_unique {B x y f a b} Aa Ab.
