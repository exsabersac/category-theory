Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Slice.
Require Import Category.Structure.Pullback.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** Functors between slice categories induced by a base morphism. *)

(*
   nLab: https://ncatlab.org/nlab/show/dependent+sum
   nLab: https://ncatlab.org/nlab/show/over+category
   Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)
   Book:      Mac Lane, "Categories for the Working Mathematician",

   本文件给出拉回相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SliceFunctors.

Context `{C : Category}.

#[local] Set Transparent Obligations.

(* Dependent sum Σ_f (= f_!): post-compose the structure morphism with f. *)
Program Definition Bang_Functor `(f : a ~> b) : @Slice C a ⟶ @Slice C b := {|
  fobj := λ '(o; h), (o; f ∘ h);
  fmap := λ x y f, (_; _)
|}.
Next Obligation.
  rewrite <- comp_assoc.
  now rewrite X.
Qed.

(* Postfix notation for Σ_f, mirroring the standard f_! ("lower shriek"). *)
Notation "f !" := (Bang_Functor f) (at level 90) : category_scope.

(* C has all binary pullbacks; this is what makes base change f* below total. *)
Hypothesis pullbacks : ∀ {X Y Z : C} (f : Y ~> Z) (g : X ~> Z), Pullback f g.

(* Base change f*: pull the structure morphism back along f, taking the
   resulting projection onto c as the new structure morphism over c. *)
Program Definition Star_Functor `(f : c ~> a) :
  @Slice C a ⟶ @Slice C c := {|
  fobj := λ '(_; h),
            let pull : Pullback h f := pullbacks h f in
            (Pull h f pull; pullback_snd h f pull);
  fmap := λ '(a; x) '(b; y) '(g; H),
            let ypb : Pullback y f := pullbacks y f in
            let xpb : Pullback x f := pullbacks x f in
            let uniq :=
                  ump_pullbacks
                    _ _ ypb _
                    (g ∘ pullback_fst x f xpb)
                    (pullback_snd x f xpb)
                    ltac:(rewrite comp_assoc, H;
                          exact (pullback_commutes x f xpb)) in
            (unique_obj uniq; snd (unique_property uniq))
|}.
Next Obligation.
  proper; simpl in *.
  repeat (destruct (pullbacks _ _); simpl).
  repeat (destruct (ump_pullbacks0 _ _ _ _); simpl).
  intuition eauto.
  apply uniqueness.
  intuition eauto.
  now rewrites.
Qed.
Next Obligation.
  repeat (destruct (pullbacks _ _); simpl).
  repeat (destruct (ump_pullbacks _ _ _ _); simpl).
  intuition eauto.
  apply uniqueness.
  now cat.
Qed.
Next Obligation.
  repeat (destruct (pullbacks _ _); simpl).
  repeat (destruct (ump_pullbacks0 _ _ _ _); simpl).
  repeat (destruct (ump_pullbacks1 _ _ _ _); simpl).
  intuition eauto.
  apply uniqueness.
  split.
  - rewrite comp_assoc.
    rewrite a1.
    now comp_left.
  - rewrite comp_assoc.
    now rewrite b0.
Qed.

(** ** The base change adjunction Σ_f ⊣ f* *)

Section BaseChange.

Context `(f : a ~> b).

(* The universal property of the chosen pullback of k along f, read at
   the competing cone that a slice morphism Σ_f (o; h) ~> (p; k)
   supplies: its two legs are the morphism itself and h, and the square
   condition IS that morphism's slice condition. *)
Definition base_ump {o p : C} (h : o ~> a) (k : p ~> b)
      (g : o ~> p) (Hg : k ∘ g ≈ f ∘ h) :
  ∃! u : o ~> Pull k f (pullbacks k f),
      pullback_fst k f (pullbacks k f) ∘ u ≈ g ∧
      pullback_snd k f (pullbacks k f) ∘ u ≈ h :=
  ump_pullbacks k f (pullbacks k f) o g h Hg.

(* The arrow action of f* is itself a pullback mediator; its underlying
   C-morphism is named here so that its two leg equations can be stated
   with the pullback objects already in reduced form. *)
Definition star_fmap_mor {p1 p2 : C} {k1 : p1 ~> b} {k2 : p2 ~> b}
      (g : (p1; k1) ~{@Slice C b}~> (p2; k2)) :
  Pull k1 f (pullbacks k1 f) ~> Pull k2 f (pullbacks k2 f) :=
  `1 (fmap[Star_Functor f] g).

Lemma star_fmap_fst {p1 p2 : C} {k1 : p1 ~> b} {k2 : p2 ~> b}
      (g : (p1; k1) ~{@Slice C b}~> (p2; k2)) :
  pullback_fst k2 f (pullbacks k2 f) ∘ star_fmap_mor g
    ≈ `1 g ∘ pullback_fst k1 f (pullbacks k1 f).
Proof.
  unfold star_fmap_mor.
  destruct g as [gm Hg]; simpl.
  match goal with
  | |- context [ unique_obj ?U ] => exact (fst (unique_property U))
  end.
Qed.

Lemma star_fmap_snd {p1 p2 : C} {k1 : p1 ~> b} {k2 : p2 ~> b}
      (g : (p1; k1) ~{@Slice C b}~> (p2; k2)) :
  pullback_snd k2 f (pullbacks k2 f) ∘ star_fmap_mor g
    ≈ pullback_snd k1 f (pullbacks k1 f).
Proof.
  unfold star_fmap_mor.
  destruct g as [gm Hg]; simpl.
  match goal with
  | |- context [ unique_obj ?U ] => exact (snd (unique_property U))
  end.
Qed.

(* The forward transpose, on underlying C-morphisms. *)
Definition base_to_mor {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  o ~> Pull k f (pullbacks k f) :=
  unique_obj (base_ump h k (`1 g) (`2 g)).

Lemma base_to_fst {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  pullback_fst k f (pullbacks k f) ∘ base_to_mor g ≈ `1 g.
Proof. exact (fst (unique_property (base_ump h k (`1 g) (`2 g)))). Qed.

Lemma base_to_snd {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  pullback_snd k f (pullbacks k f) ∘ base_to_mor g ≈ h.
Proof. exact (snd (unique_property (base_ump h k (`1 g) (`2 g)))). Defined.

(* Every competitor satisfying the two leg equations IS the transpose.
   This single lemma discharges respectfulness, one round trip and both
   naturality clauses. *)
Lemma base_to_mor_unique {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k))
      (u : o ~> Pull k f (pullbacks k f)) :
  pullback_fst k f (pullbacks k f) ∘ u ≈ `1 g →
  pullback_snd k f (pullbacks k f) ∘ u ≈ h →
  base_to_mor g ≈ u.
Proof.
  intros H1 H2.
  exact (uniqueness (base_ump h k (`1 g) (`2 g)) u (H1, H2)).
Qed.

Definition base_to {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  (o; h) ~{@Slice C a}~> Star_Functor f (p; k) :=
  (base_to_mor g; base_to_snd g).

(* The backward transpose: post-compose with the pullback projection.
   Its slice condition over b is [pullback_commutes] followed by the
   argument's own slice condition over a. *)
Lemma base_from_ok {o p : C} {h : o ~> a} {k : p ~> b}
      (u : (o; h) ~{@Slice C a}~> Star_Functor f (p; k)) :
  k ∘ (pullback_fst k f (pullbacks k f) ∘ `1 u) ≈ f ∘ h.
Proof.
  pose proof (`2 u) as Hu; simpl in Hu.
  rewrite comp_assoc.
  rewrite (pullback_commutes k f (pullbacks k f)).
  rewrite <- comp_assoc.
  now rewrite Hu.
Defined.

Definition base_from {o p : C} {h : o ~> a} {k : p ~> b}
      (u : (o; h) ~{@Slice C a}~> Star_Functor f (p; k)) :
  (o; f ∘ h) ~{@Slice C b}~> (p; k) :=
  (pullback_fst k f (pullbacks k f) ∘ `1 u; base_from_ok u).

Lemma base_to_respects {o p : C} {h : o ~> a} {k : p ~> b}
      (g1 g2 : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  `1 g1 ≈ `1 g2 → base_to_mor g1 ≈ base_to_mor g2.
Proof.
  intro Hg.
  apply base_to_mor_unique.
  - rewrite base_to_fst.
    now symmetry.
  - apply base_to_snd.
Qed.

(* Round trip: the transpose of a morphism into the pullback recovers
   it, by uniqueness of the mediator. *)
Lemma base_to_from {o p : C} {h : o ~> a} {k : p ~> b}
      (u : (o; h) ~{@Slice C a}~> Star_Functor f (p; k)) :
  base_to_mor (base_from u) ≈ `1 u.
Proof.
  apply base_to_mor_unique.
  - reflexivity.
  - exact (`2 u).
Qed.

(* The other round trip is the FIRST leg equation of the mediator, with
   no further argument. *)
Lemma base_from_to {o p : C} {h : o ~> a} {k : p ~> b}
      (g : (o; f ∘ h) ~{@Slice C b}~> (p; k)) :
  `1 (base_from (base_to g)) ≈ `1 g.
Proof. exact (base_to_fst g). Qed.

Program Definition base_adj_to (o p : C) (h : o ~> a) (k : p ~> b) :
  {| carrier   := Bang_Functor f (o; h) ~{@Slice C b}~> (p; k)
   ; is_setoid := @homset (@Slice C b) (Bang_Functor f (o; h)) (p; k) |}
    ~{Sets}~>
  {| carrier   := (o; h) ~{@Slice C a}~> Star_Functor f (p; k)
   ; is_setoid := @homset (@Slice C a) (o; h) (Star_Functor f (p; k)) |} := {|
  morphism := @base_to o p h k
|}.
Next Obligation. proper; now apply base_to_respects. Qed.

Program Definition base_adj_from (o p : C) (h : o ~> a) (k : p ~> b) :
  {| carrier   := (o; h) ~{@Slice C a}~> Star_Functor f (p; k)
   ; is_setoid := @homset (@Slice C a) (o; h) (Star_Functor f (p; k)) |}
    ~{Sets}~>
  {| carrier   := Bang_Functor f (o; h) ~{@Slice C b}~> (p; k)
   ; is_setoid := @homset (@Slice C b) (Bang_Functor f (o; h)) (p; k) |} := {|
  morphism := @base_from o p h k
|}.

Program Definition base_adj_at (o p : C) (h : o ~> a) (k : p ~> b) :
  @Isomorphism Sets
    {| carrier   := Bang_Functor f (o; h) ~{@Slice C b}~> (p; k)
     ; is_setoid := @homset (@Slice C b) (Bang_Functor f (o; h)) (p; k) |}
    {| carrier   := (o; h) ~{@Slice C a}~> Star_Functor f (p; k)
     ; is_setoid := @homset (@Slice C a) (o; h) (Star_Functor f (p; k)) |} := {|
  to   := base_adj_to o p h k;
  from := base_adj_from o p h k
|}.
Next Obligation. apply base_to_from. Qed.
Next Obligation. apply base_from_to. Qed.

Definition base_adj (x : @Slice C a) (y : @Slice C b) :
  @Isomorphism Sets
    {| carrier   := Bang_Functor f x ~{@Slice C b}~> y
     ; is_setoid := @homset (@Slice C b) (Bang_Functor f x) y |}
    {| carrier   := x ~{@Slice C a}~> Star_Functor f y
     ; is_setoid := @homset (@Slice C a) x (Star_Functor f y) |}.
Proof.
  destruct x as [o h], y as [p k].
  exact (base_adj_at o p h k).
Defined.

(* The two leg equations the [to_adj_nat_r] clause needs, stated at
   arguments whose slice types are already in pullback form, so that the
   rewriting below has the shape it expects. *)
Lemma base_nat_r_fst {o p1 p2 : C} {h : o ~> a}
      {k1 : p1 ~> b} {k2 : p2 ~> b}
      (g : (p1; k1) ~{@Slice C b}~> (p2; k2))
      (u : (o; f ∘ h) ~{@Slice C b}~> (p1; k1)) :
  pullback_fst k2 f (pullbacks k2 f)
      ∘ (star_fmap_mor g ∘ base_to_mor u)
    ≈ `1 g ∘ `1 u.
Proof.
  rewrite comp_assoc, star_fmap_fst, <- comp_assoc, base_to_fst.
  reflexivity.
Qed.

Lemma base_nat_r_snd {o p1 p2 : C} {h : o ~> a}
      {k1 : p1 ~> b} {k2 : p2 ~> b}
      (g : (p1; k1) ~{@Slice C b}~> (p2; k2))
      (u : (o; f ∘ h) ~{@Slice C b}~> (p1; k1)) :
  pullback_snd k2 f (pullbacks k2 f)
      ∘ (star_fmap_mor g ∘ base_to_mor u) ≈ h.
Proof.
  rewrite comp_assoc, star_fmap_snd.
  apply base_to_snd.
Qed.

(** The base change adjunction: dependent sum is left adjoint to
    pullback along the same morphism. *)
Definition Base_Functor_Adjunction : Bang_Functor f ⊣ Star_Functor f.
Proof.
  unshelve eapply (@Build_Adjunction' (@Slice C b) (@Slice C a)
                     (Bang_Functor f) (Star_Functor f) base_adj).
  - intros [ox hx] [oy hy] [p k] g u; simpl.
    apply base_to_mor_unique.
    + rewrite comp_assoc, base_to_fst.
      reflexivity.
    + rewrite comp_assoc, base_to_snd.
      exact (`2 u).
  - intros [o h] [p1 k1] [p2 k2] g u.
    change (@base_to_mor o p2 h k2 (g ∘ u)
              ≈ star_fmap_mor g ∘ @base_to_mor o p1 h k1 u).
    apply base_to_mor_unique.
    + apply (base_nat_r_fst g u).
    + apply (base_nat_r_snd g u).
Defined.

(** ** Unit and counit *)

(* The unit at (o; h) is the comparison of o into the pullback of f ∘ h
   along f: the mediator of the cone ⟨id, h⟩, whose square condition is
   (f ∘ h) ∘ id ≈ f ∘ h. *)
Definition bang_star_unit_mor (o : C) (h : o ~> a) :
  o ~> Pull (f ∘ h) f (pullbacks (f ∘ h) f) :=
  unique_obj (base_ump h (f ∘ h) id (id_right (f ∘ h))).

Definition bang_star_unit (o : C) (h : o ~> a) :
  (o; h) ~{@Slice C a}~> Star_Functor f (Bang_Functor f (o; h)) :=
  (bang_star_unit_mor o h;
   snd (unique_property (base_ump h (f ∘ h) id (id_right (f ∘ h))))).

(* The counit at (p; k) is the pullback projection itself; its slice
   condition k ∘ fst ≈ f ∘ snd IS [pullback_commutes]. *)
Definition bang_star_counit_mor (p : C) (k : p ~> b) :
  Pull k f (pullbacks k f) ~> p := pullback_fst k f (pullbacks k f).

Definition bang_star_counit (p : C) (k : p ~> b) :
  Bang_Functor f (Star_Functor f (p; k)) ~{@Slice C b}~> (p; k) :=
  (bang_star_counit_mor p k; pullback_commutes k f (pullbacks k f)).

(** *** How the named unit and counit relate to the class *)

(* The class's unit at (o; h) IS the forward transpose of the identity,
   on the nose. *)
Example bang_star_unit_strict (o : C) (h : o ~> a) :
  `1 (@unit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor f) Base_Functor_Adjunction (o; h))
  = base_to_mor (id[Bang_Functor f (o; h)]) := eq_refl.

(* The residue is exhibited rather than described: both sides are the
   mediator of the cone whose legs are [id] and [h], and they differ in
   nothing but the proof of that cone's square condition. *)
Example bang_star_unit_residue (o : C) (h : o ~> a) :
  `1 (@unit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor f) Base_Functor_Adjunction (o; h))
  = unique_obj (base_ump h (f ∘ h) id
                  (`2 (id[Bang_Functor f (o; h)]))) := eq_refl.

Example bang_star_unit_mor_residue (o : C) (h : o ~> a) :
  bang_star_unit_mor o h
  = unique_obj (base_ump h (f ∘ h) id (id_right (f ∘ h))) := eq_refl.

(* Against [bang_star_unit_mor] the identification holds up to ≈ and not
   on the nose: both are mediators of the SAME cone ⟨id, h⟩, but the
   mediator is produced from a proof of the square condition and the two
   sides feed it different proofs -- the slice identity's own commuting
   witness on the class side, [id_right (f ∘ h)] on the named side. *)
Lemma bang_star_unit_is_mediator (o : C) (h : o ~> a) :
  `1 (@unit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor f) Base_Functor_Adjunction (o; h))
    ≈ bang_star_unit_mor o h.
Proof.
  symmetry.
  apply (uniqueness (base_ump h (f ∘ h) id (id_right (f ∘ h)))).
  split.
  - apply (base_to_fst (id[Bang_Functor f (o; h)])).
  - apply (base_to_snd (id[Bang_Functor f (o; h)])).
Qed.

Lemma bang_star_unit_is_unit (o : C) (h : o ~> a) :
  @unit (@Slice C b) (@Slice C a) (Bang_Functor f)
    (Star_Functor f) Base_Functor_Adjunction (o; h)
    ≈ bang_star_unit o h.
Proof. exact (bang_star_unit_is_mediator o h). Qed.

(* The class's counit at (p; k) is the pullback projection with one
   residual identity, which is exactly what ε := ⌈id⌉ produces. *)
Example bang_star_counit_strict (p : C) (k : p ~> b) :
  `1 (@counit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor f) Base_Functor_Adjunction (p; k))
  = bang_star_counit_mor p k ∘ id := eq_refl.

Lemma bang_star_counit_is_fst (p : C) (k : p ~> b) :
  `1 (@counit (@Slice C b) (@Slice C a) (Bang_Functor f)
        (Star_Functor f) Base_Functor_Adjunction (p; k))
    ≈ bang_star_counit_mor p k.
Proof. apply id_right. Qed.

Lemma bang_star_counit_is_counit (p : C) (k : p ~> b) :
  @counit (@Slice C b) (@Slice C a) (Bang_Functor f)
    (Star_Functor f) Base_Functor_Adjunction (p; k)
    ≈ bang_star_counit p k.
Proof. exact (bang_star_counit_is_fst p k). Qed.

End BaseChange.

End SliceFunctors.
