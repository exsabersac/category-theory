Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Theory.Bicategory.
Require Import Category.Theory.Bicategory.Adjunction.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Infix "∘∘" := vcompose : category_scope.
Notation "f ∘∘∘ g" := (hcompose (f, g)) : category_scope.

(** The mates correspondence in a bicategory *)

(*
 nLab: https://ncatlab.org/nlab/show/mate

   本文件给出 mate 对应。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Helpers.
Context {B : Bicategory}.

Lemma vcancel_ft {aa bb : bi0cell} {A0 A1 C : bicat aa bb}
  (i : A0 ≅[bicat aa bb] A1) (r : C ~> A0) :
  from i ∘∘ (to i ∘∘ r) ≈ r.
Proof. rewrite vcompose_assoc, vfrom_vto. now rewrite bi2id_left. Qed.

Lemma tri_lr_from {aa bb cc : bi0cell} (g : bicat bb cc) (k : bicat aa bb) :
  rwhisker (from (hunit_right g)) k
    ≈ from (hassoc g bi1id k) ∘∘ lwhisker g (from (hunit_left k)).
Proof.
  apply (vcancel_r _ _ (rwhisker (to (hunit_right g)) k)
                       (rwhisker (from (hunit_right g)) k)).
  - rewrite <- rwhisker_comp.
    rewrite (rwhisker_cong _ _ k (vto_vfrom (hunit_right g))).
    apply rwhisker_id.
  - rewrite <- rwhisker_comp.
    rewrite (rwhisker_cong _ _ k (vfrom_vto (hunit_right g))).
    rewrite rwhisker_id.
    rewrite (tri_lr g k).
    rewrite <- !vcompose_assoc.
    rewrite (vcompose_assoc (lwhisker g (from (hunit_left k)))
                            (lwhisker g (to (hunit_left k)))
                            (to (hassoc g bi1id k))).
    rewrite <- lwhisker_comp.
    rewrite (lwhisker_cong g _ _ (vfrom_vto (hunit_left k))).
    rewrite lwhisker_id, bi2id_left.
    now rewrite vfrom_vto.
Qed.

Lemma pent_solve_from {v w xx yy zz : bi0cell}
  (k : bicat yy zz) (h : bicat xx yy) (g : bicat w xx) (l : bicat v w) :
  rwhisker (from (hassoc k h g)) l
    ≈ from (hassoc (k ∘∘∘ h) g l)
        ∘∘ (from (hassoc k h (g ∘∘∘ l))
             ∘∘ (lwhisker k (to (hassoc h g l)) ∘∘ to (hassoc k (h ∘∘∘ g) l))).
Proof.
  apply (vcancel_r _ _ (rwhisker (to (hassoc k h g)) l)
                       (rwhisker (from (hassoc k h g)) l)).
  - rewrite <- rwhisker_comp.
    rewrite (rwhisker_cong _ _ l (vto_vfrom (hassoc k h g))).
    apply rwhisker_id.
  - rewrite <- rwhisker_comp.
    rewrite (rwhisker_cong _ _ l (vfrom_vto (hassoc k h g))).
    rewrite rwhisker_id.
    rewrite (pent_solve k h g l).
    rewrite <- !vcompose_assoc.
    rewrite (vcancel_tf (hassoc k (h ∘∘∘ g) l)).
    rewrite (vcompose_assoc (lwhisker k (to (hassoc h g l)))
                            (lwhisker k (from (hassoc h g l))) _).
    rewrite <- lwhisker_comp.
    rewrite (lwhisker_cong k _ _ (vto_vfrom (hassoc h g l))).
    rewrite lwhisker_id, bi2id_left.
    rewrite (vcancel_ft (hassoc k h (g ∘∘∘ l))).
    now rewrite vfrom_vto.
Qed.

Lemma right_unit_coherence_from {aa bb cc : bi0cell}
  (g : bicat bb cc) (k : bicat aa bb) :
  from (hunit_right (g ∘∘∘ k))
    ≈ from (hassoc g k bi1id) ∘∘ lwhisker g (from (hunit_right k)).
Proof.
  apply (vcancel_r _ _ (to (hunit_right (g ∘∘∘ k)))
                       (from (hunit_right (g ∘∘∘ k)))).
  - exact (vto_vfrom (hunit_right (g ∘∘∘ k))).
  - rewrite (vfrom_vto (hunit_right (g ∘∘∘ k))).
    rewrite <- (right_unit_coherence g k).
    rewrite <- !vcompose_assoc.
    rewrite (vcompose_assoc (lwhisker g (from (hunit_right k)))
                            (lwhisker g (to (hunit_right k)))
                            (to (hassoc g k bi1id))).
    rewrite <- lwhisker_comp.
    rewrite (lwhisker_cong g _ _ (vfrom_vto (hunit_right k))).
    rewrite lwhisker_id, bi2id_left.
    now rewrite vfrom_vto.
Qed.

Lemma lwhisker_hcompose {aa bb cc dd : bi0cell}
  (h : bicat cc dd) (g : bicat bb cc) {k k' : bicat aa bb} (η : k ~> k') :
  lwhisker (h ∘∘∘ g) η
    ≈ from (hassoc h g k') ∘∘ (lwhisker h (lwhisker g η) ∘∘ to (hassoc h g k)).
Proof.
  apply (vcancel_l _ _ (to (hassoc h g k')) (from (hassoc h g k'))).
  - exact (vfrom_vto (hassoc h g k')).
  - rewrite (vcancel_tf (hassoc h g k')).
    symmetry. exact (assoc_nat_bot h g η).
Qed.

End Helpers.

Section HomAdjunction.
Context {B : Bicategory}.
Context {x y : bi0cell}.
Context {f : bicat x y} {u : bicat y x}.
Context (A : BicatAdjunction f u).

#[local] Instance hcomp2_respects
  {x0 y0 z0 : bi0cell} {g g' : bicat y0 z0} {ff ff' : bicat x0 y0} :
  Proper (equiv ==> equiv ==> equiv) (@hcomp2 B x0 y0 z0 g g' ff ff').
Proof.
  proper.
  exact (@fmap_respects _ _ (@hcompose B x0 y0 z0)
           (g, ff) (g', ff') (x1, x2) (y1, y2) (X, X0)).
Qed.

Notation η := (adj_unit f u).
Notation ε := (adj_counit f u).

(* ---------- precomposition hom-adjunction bicat(f∘c,d) ≅ bicat(c,u∘d) ------ *)

(* Unit-side cell: c ⟹ u∘(f∘c). *)
Definition preΘ {w : bi0cell} (c : bicat w x) : c ~> (u ∘∘∘ (f ∘∘∘ c)) :=
  to (hassoc u f c) ∘∘ rwhisker η c ∘∘ from (hunit_left c).

(* Counit-side cell: f∘(u∘d) ⟹ d. *)
Definition preΞ {w : bi0cell} (d : bicat w y) : (f ∘∘∘ (u ∘∘∘ d)) ~> d :=
  to (hunit_left d) ∘∘ rwhisker ε d ∘∘ from (hassoc f u d).

Definition precomp_to {w : bi0cell} {c : bicat w x} {d : bicat w y}
  (σ : (f ∘∘∘ c) ~> d) : c ~> (u ∘∘∘ d) := lwhisker u σ ∘∘ preΘ c.

Definition precomp_from {w : bi0cell} {c : bicat w x} {d : bicat w y}
  (τ : c ~> (u ∘∘∘ d)) : (f ∘∘∘ c) ~> d := preΞ d ∘∘ lwhisker f τ.

#[export] Instance precomp_to_Proper {w c d} :
  Proper (equiv ==> equiv) (@precomp_to w c d).
Proof. intros p q H. unfold precomp_to. now rewrite (lwhisker_cong u _ _ H). Qed.

#[export] Instance precomp_from_Proper {w c d} :
  Proper (equiv ==> equiv) (@precomp_from w c d).
Proof. intros p q H. unfold precomp_from. now rewrite (lwhisker_cong f _ _ H). Qed.

(* The zig cell preΞ(f∘c) ∘∘ (f ⊲ preΘ c) 恒等 — whiskered left
 triangle 恒等, reduced adj_triangle_left via coherence engine. （已译） *)
Lemma precomp_zig_id {w : bi0cell} (c : bicat w x) :
  preΞ (f ∘∘∘ c) ∘∘ lwhisker f (preΘ c) ≈ bi2id.
Proof.
  unfold preΞ, preΘ.
  transitivity (rwhisker
    (to (hunit_left f) ∘∘ rwhisker ε f ∘∘ from (hassoc f u f)
       ∘∘ lwhisker f η ∘∘ from (hunit_right f)) c).
  - rewrite !lwhisker_comp.
    rewrite !rwhisker_comp.
    rewrite (left_unit_coherence f c).
    rewrite (assoc_top_solve ε f c).
    rewrite (pent_solve_from f u f c).
    rewrite (assoc_mid_solve f η c).
    rewrite (tri_lr_from f c).
    rewrite <- !vcompose_assoc.
    rewrite (vcancel_tf (hassoc bi1id f c)).
    rewrite (vcancel_tf (hassoc (f ∘∘∘ u) f c)).
    rewrite (vcancel_tf (hassoc f (u ∘∘∘ f) c)).
    rewrite (vcancel_tf (hassoc f bi1id c)).
    reflexivity.
  - transitivity (rwhisker (bi2id (a:=f)) c).
    + apply rwhisker_cong. exact (adj_triangle_left f u).
    + apply rwhisker_id.
Qed.

(* Naturality slide: preΞ d after left-whiskering σ recovers σ before preΞ. *)
Lemma precomp_slide {w : bi0cell} {c : bicat w x} {d : bicat w y}
  (σ : (f ∘∘∘ c) ~> d) :
  preΞ d ∘∘ lwhisker f (lwhisker u σ) ≈ σ ∘∘ preΞ (f ∘∘∘ c).
Proof.
  unfold preΞ.
  transitivity (to (hunit_left d) ∘∘ (rwhisker ε d
    ∘∘ (from (hassoc f u d) ∘∘ lwhisker f (lwhisker u σ)))).
  { now rewrite <- !vcompose_assoc. }
  rewrite (iso_conj_from _ _ _ _ (assoc_nat_bot f u σ)).
  transitivity (to (hunit_left d) ∘∘ ((rwhisker ε d ∘∘ lwhisker (f ∘∘∘ u) σ)
    ∘∘ from (hassoc f u (f ∘∘∘ c)))).
  { now rewrite <- !vcompose_assoc. }
  rewrite <- (whisker_exchange ε σ).
  transitivity ((to (hunit_left d) ∘∘ lwhisker bi1id σ)
    ∘∘ (rwhisker ε (f ∘∘∘ c) ∘∘ from (hassoc f u (f ∘∘∘ c)))).
  { now rewrite <- !vcompose_assoc. }
  rewrite <- (hunit_left_nat σ).
  now rewrite <- !vcompose_assoc.
Qed.

Lemma precomp_left {w : bi0cell} {c : bicat w x} {d : bicat w y}
  (σ : (f ∘∘∘ c) ~> d) :
  precomp_from (precomp_to σ) ≈ σ.
Proof.
  unfold precomp_from, precomp_to.
  rewrite lwhisker_comp.
  rewrite (vcompose_assoc (preΞ d) (lwhisker f (lwhisker u σ)) (lwhisker f (preΘ c))).
  rewrite precomp_slide.
  rewrite <- vcompose_assoc.
  rewrite precomp_zig_id.
  now rewrite bi2id_right.
Qed.

(* The zag cell (u ⊲ preΞ D) ∘∘ preΘ (u∘D) 恒等 — whiskered right
 triangle 恒等, reduced adj_triangle_right via coherence engine. （已译） *)
Lemma precomp_zag_id {w : bi0cell} (D : bicat w y) :
  lwhisker u (preΞ D) ∘∘ preΘ (u ∘∘∘ D) ≈ bi2id.
Proof.
  unfold preΞ, preΘ.
  transitivity (rwhisker
    (to (hunit_right u) ∘∘ lwhisker u ε ∘∘ to (hassoc u f u)
       ∘∘ rwhisker η u ∘∘ from (hunit_left u)) D).
  - rewrite !lwhisker_comp.
    rewrite !rwhisker_comp.
    rewrite (tri_lr u D).
    rewrite (assoc_mid_solve u ε D).
    rewrite (pent_solve u f u D).
    rewrite (assoc_top_solve η u D).
    rewrite (left_unit_coherence_from u D).
    rewrite <- !vcompose_assoc.
    rewrite (vcancel_tf (hassoc u bi1id D)).
    rewrite (vcancel_tf (hassoc u (f ∘∘∘ u) D)).
    rewrite (vcancel_tf (hassoc (u ∘∘∘ f) u D)).
    rewrite (vcancel_tf (hassoc bi1id u D)).
    reflexivity.
  - transitivity (rwhisker (bi2id (a:=u)) D).
    + apply rwhisker_cong. exact (adj_triangle_right f u).
    + apply rwhisker_id.
Qed.

(* Mirror 自然性 slide, unit-side cell preΘ. （已译） *)
Lemma precomp_slide' {w : bi0cell} {c : bicat w x} {d : bicat w y}
  (τ : c ~> (u ∘∘∘ d)) :
  lwhisker u (lwhisker f τ) ∘∘ preΘ c ≈ preΘ (u ∘∘∘ d) ∘∘ τ.
Proof.
  unfold preΘ.
  transitivity ((lwhisker u (lwhisker f τ) ∘∘ to (hassoc u f c))
    ∘∘ (rwhisker η c ∘∘ from (hunit_left c))).
  { now rewrite <- !vcompose_assoc. }
  rewrite (assoc_nat_bot u f τ).
  transitivity (to (hassoc u f (u ∘∘∘ d))
    ∘∘ ((lwhisker (u ∘∘∘ f) τ ∘∘ rwhisker η c) ∘∘ from (hunit_left c))).
  { now rewrite <- !vcompose_assoc. }
  rewrite (whisker_exchange η τ).
  transitivity (to (hassoc u f (u ∘∘∘ d))
    ∘∘ (rwhisker η (u ∘∘∘ d) ∘∘ (lwhisker bi1id τ ∘∘ from (hunit_left c)))).
  { now rewrite <- !vcompose_assoc. }
  rewrite <- (hunit_left_from_natural τ).
  now rewrite <- !vcompose_assoc.
Qed.

Lemma precomp_right {w : bi0cell} {c : bicat w x} {d : bicat w y}
  (τ : c ~> (u ∘∘∘ d)) :
  precomp_to (precomp_from τ) ≈ τ.
Proof.
  unfold precomp_to, precomp_from.
  rewrite lwhisker_comp.
  rewrite <- (vcompose_assoc (lwhisker u (preΞ d))
                             (lwhisker u (lwhisker f τ)) (preΘ c)).
  rewrite precomp_slide'.
  rewrite (vcompose_assoc (lwhisker u (preΞ d)) (preΘ (u ∘∘∘ d)) τ).
  rewrite precomp_zag_id.
  now rewrite bi2id_left.
Qed.

(* ---------- postcomposition hom-adjunction bicat(c,e∘f) ≅ bicat(c∘u,e) ----- *)

(* Counit-side cell: (e∘f)∘u ⟹ e. *)
Definition postΛ {w : bi0cell} (e : bicat y w) : ((e ∘∘∘ f) ∘∘∘ u) ~> e :=
  to (hunit_right e) ∘∘ lwhisker e ε ∘∘ to (hassoc e f u).

(* Unit-side cell: c ⟹ (c∘u)∘f. *)
Definition postΠ {w : bi0cell} (c : bicat x w) : c ~> ((c ∘∘∘ u) ∘∘∘ f) :=
  from (hassoc c u f) ∘∘ lwhisker c η ∘∘ from (hunit_right c).

Definition postcomp_to {w : bi0cell} {c : bicat x w} {e : bicat y w}
  (β : c ~> (e ∘∘∘ f)) : (c ∘∘∘ u) ~> e := postΛ e ∘∘ rwhisker β u.

Definition postcomp_from {w : bi0cell} {c : bicat x w} {e : bicat y w}
  (γ : (c ∘∘∘ u) ~> e) : c ~> (e ∘∘∘ f) := rwhisker γ f ∘∘ postΠ c.

#[export] Instance postcomp_to_Proper {w c e} :
  Proper (equiv ==> equiv) (@postcomp_to w c e).
Proof. intros p q H. unfold postcomp_to. now rewrite (rwhisker_cong _ _ u H). Qed.

#[export] Instance postcomp_from_Proper {w c e} :
  Proper (equiv ==> equiv) (@postcomp_from w c e).
Proof. intros p q H. unfold postcomp_from. now rewrite (rwhisker_cong _ _ f H). Qed.

Lemma postcomp_zig_id {w : bi0cell} (e : bicat y w) :
  rwhisker (postΛ e) f ∘∘ postΠ (e ∘∘∘ f) ≈ bi2id.
Proof.
  unfold postΛ, postΠ.
  transitivity (lwhisker e
    (to (hunit_left f) ∘∘ rwhisker ε f ∘∘ from (hassoc f u f)
       ∘∘ lwhisker f η ∘∘ from (hunit_right f))).
  - rewrite !rwhisker_comp.
    rewrite !lwhisker_comp.
    rewrite (tri_lr e f).
    rewrite (assoc_mid_solve e ε f).
    rewrite (pent_solve e f u f).
    rewrite (lwhisker_hcompose e f η).
    rewrite (right_unit_coherence_from e f).
    rewrite <- !vcompose_assoc.
    rewrite (vcancel_tf (hassoc e bi1id f)).
    rewrite (vcancel_tf (hassoc e (f ∘∘∘ u) f)).
    rewrite (vcancel_tf (hassoc (e ∘∘∘ f) u f)).
    rewrite (vcancel_tf (hassoc e f (u ∘∘∘ f))).
    rewrite (vcancel_tf (hassoc e f bi1id)).
    reflexivity.
  - transitivity (lwhisker e (bi2id (a:=f))).
    + apply lwhisker_cong. exact (adj_triangle_left f u).
    + apply lwhisker_id.
Qed.

Lemma postcomp_slide {w : bi0cell} {c : bicat x w} {e : bicat y w}
  (β : c ~> (e ∘∘∘ f)) :
  rwhisker (rwhisker β u) f ∘∘ postΠ c ≈ postΠ (e ∘∘∘ f) ∘∘ β.
Proof.
  unfold postΠ.
  transitivity ((rwhisker (rwhisker β u) f ∘∘ from (hassoc c u f))
    ∘∘ (lwhisker c η ∘∘ from (hunit_right c))).
  { now rewrite <- !vcompose_assoc. }
  rewrite <- (iso_conj_from _ _ _ _ (assoc_nat_top β u f)).
  transitivity (from (hassoc (e ∘∘∘ f) u f)
    ∘∘ ((rwhisker β (u ∘∘∘ f) ∘∘ lwhisker c η) ∘∘ from (hunit_right c))).
  { now rewrite <- !vcompose_assoc. }
  rewrite <- (whisker_exchange β η).
  transitivity (from (hassoc (e ∘∘∘ f) u f)
    ∘∘ (lwhisker (e ∘∘∘ f) η ∘∘ (rwhisker β bi1id ∘∘ from (hunit_right c)))).
  { now rewrite <- !vcompose_assoc. }
  rewrite <- (hunit_right_from_natural β).
  now rewrite <- !vcompose_assoc.
Qed.

Lemma postcomp_left {w : bi0cell} {c : bicat x w} {e : bicat y w}
  (β : c ~> (e ∘∘∘ f)) :
  postcomp_from (postcomp_to β) ≈ β.
Proof.
  unfold postcomp_from, postcomp_to.
  rewrite rwhisker_comp.
  rewrite <- (vcompose_assoc (rwhisker (postΛ e) f)
                             (rwhisker (rwhisker β u) f) (postΠ c)).
  rewrite postcomp_slide.
  rewrite (vcompose_assoc (rwhisker (postΛ e) f) (postΠ (e ∘∘∘ f)) β).
  rewrite postcomp_zig_id.
  now rewrite bi2id_left.
Qed.

Lemma postcomp_zag_id {w : bi0cell} (c : bicat x w) :
  postΛ (c ∘∘∘ u) ∘∘ rwhisker (postΠ c) u ≈ bi2id.
Proof.
  unfold postΛ, postΠ.
  transitivity (lwhisker c
    (to (hunit_right u) ∘∘ lwhisker u ε ∘∘ to (hassoc u f u)
       ∘∘ rwhisker η u ∘∘ from (hunit_left u))).
  - rewrite !rwhisker_comp.
    rewrite !lwhisker_comp.
    rewrite <- (right_unit_coherence c u).
    rewrite (lwhisker_hcompose c u ε).
    rewrite (pent_solve_from c u f u).
    rewrite (assoc_mid_solve c η u).
    rewrite (tri_lr_from c u).
    rewrite <- !vcompose_assoc.
    rewrite (vcancel_tf (hassoc c u bi1id)).
    rewrite (vcancel_tf (hassoc (c ∘∘∘ u) f u)).
    rewrite (vcancel_tf (hassoc c u (f ∘∘∘ u))).
    rewrite (vcancel_tf (hassoc c (u ∘∘∘ f) u)).
    rewrite (vcancel_tf (hassoc c bi1id u)).
    reflexivity.
  - transitivity (lwhisker c (bi2id (a:=u))).
    + apply lwhisker_cong. exact (adj_triangle_right f u).
    + apply lwhisker_id.
Qed.

Lemma postcomp_slide' {w : bi0cell} {c : bicat x w} {e : bicat y w}
  (γ : (c ∘∘∘ u) ~> e) :
  postΛ e ∘∘ rwhisker (rwhisker γ f) u ≈ γ ∘∘ postΛ (c ∘∘∘ u).
Proof.
  unfold postΛ.
  transitivity (to (hunit_right e) ∘∘ (lwhisker e ε
    ∘∘ (to (hassoc e f u) ∘∘ rwhisker (rwhisker γ f) u))).
  { now rewrite <- !vcompose_assoc. }
  rewrite <- (assoc_nat_top γ f u).
  transitivity (to (hunit_right e) ∘∘ ((lwhisker e ε ∘∘ rwhisker γ (f ∘∘∘ u))
    ∘∘ to (hassoc (c ∘∘∘ u) f u))).
  { now rewrite <- !vcompose_assoc. }
  rewrite (whisker_exchange γ ε).
  transitivity ((to (hunit_right e) ∘∘ rwhisker γ bi1id)
    ∘∘ (lwhisker (c ∘∘∘ u) ε ∘∘ to (hassoc (c ∘∘∘ u) f u))).
  { now rewrite <- !vcompose_assoc. }
  rewrite <- (hunit_right_nat γ).
  now rewrite <- !vcompose_assoc.
Qed.

Lemma postcomp_right {w : bi0cell} {c : bicat x w} {e : bicat y w}
  (γ : (c ∘∘∘ u) ~> e) :
  postcomp_to (postcomp_from γ) ≈ γ.
Proof.
  unfold postcomp_to, postcomp_from.
  rewrite rwhisker_comp.
  rewrite (vcompose_assoc (postΛ e) (rwhisker (rwhisker γ f) u)
                          (rwhisker (postΠ c) u)).
  rewrite postcomp_slide'.
  rewrite <- (vcompose_assoc γ (postΛ (c ∘∘∘ u)) (rwhisker (postΠ c) u)).
  rewrite postcomp_zag_id.
  now rewrite bi2id_right.
Qed.

End HomAdjunction.

(** The mates correspondence *)

Section Mates.
Context {B : Bicategory}.
Context {x y x' y' : bi0cell}.
Context {f : bicat x y} {u : bicat y x} (Af : BicatAdjunction f u).
Context {f' : bicat x' y'} {u' : bicat y' x'} (Af' : BicatAdjunction f' u').
Context {a : bicat x x'} {b : bicat y y'}.

(* 相关说明。 （已译） *)
Definition mate (σ : (f' ∘∘∘ a) ~> (b ∘∘∘ f)) : (a ∘∘∘ u) ~> (u' ∘∘∘ b) :=
  postcomp_to Af (from (hassoc u' b f) ∘∘ precomp_to Af' σ).

(* 相关说明。 （已译） *)
Definition mate_inv (τ : (a ∘∘∘ u) ~> (u' ∘∘∘ b)) : (f' ∘∘∘ a) ~> (b ∘∘∘ f) :=
  precomp_from Af' (to (hassoc u' b f) ∘∘ postcomp_from Af τ).

#[local] Instance mate_Proper : Proper (equiv ==> equiv) mate.
Proof. intros p q H. unfold mate. now rewrite H. Qed.

#[local] Instance mate_inv_Proper : Proper (equiv ==> equiv) mate_inv.
Proof. intros p q H. unfold mate_inv. now rewrite H. Qed.

Lemma mate_roundtrip_left (σ : (f' ∘∘∘ a) ~> (b ∘∘∘ f)) :
  mate_inv (mate σ) ≈ σ.
Proof.
  unfold mate_inv, mate.
  rewrite (postcomp_left Af).
  rewrite (vcancel_tf (hassoc u' b f)).
  now rewrite (precomp_left Af').
Qed.

Lemma mate_roundtrip_right (τ : (a ∘∘∘ u) ~> (u' ∘∘∘ b)) :
  mate (mate_inv τ) ≈ τ.
Proof.
  unfold mate, mate_inv.
  rewrite (precomp_right Af').
  rewrite (vcancel_ft (hassoc u' b f)).
  now rewrite (postcomp_right Af).
Qed.

(* The two 2-cell hom-setoids, presented as objects of Sets. *)
Definition mate_dom : SetoidObject :=
  {| carrier := (f' ∘∘∘ a) ~{bicat x y'}~> (b ∘∘∘ f) |}.
Definition mate_cod : SetoidObject :=
  {| carrier := (a ∘∘∘ u) ~{bicat y x'}~> (u' ∘∘∘ b) |}.

(* The mates correspondence as a bijection in Sets. *)
#[local] Obligation Tactic := idtac.
Program Definition mate_iso : @Isomorphism Sets mate_dom mate_cod := {|
  to   := {| morphism := mate |};
  from := {| morphism := mate_inv |}
|}.
Next Obligation. exact mate_roundtrip_right. Qed.
Next Obligation. exact mate_roundtrip_left. Qed.

End Mates.
