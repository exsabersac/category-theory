Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/equivalence+of+categories
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_of_categories

   本文件给出范畴等价的经典刻画：函子是等价当且仅当它全、忠实且本质满射（本库中为带选择的分裂版本，两个方向均可构造）。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition ff_eso_inverse `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F} :
  D ⟶ C := {|
  fobj := eso_obj;
  fmap := fun d d' g => prefmap (from (eso_iso d') ∘ g ∘ to (eso_iso d))
|}.
Next Obligation.
  (* respectfulness 态射 action, recovered faithfulness （已译） *)
  proper.
  apply fmap_inj.
  rewrite !fmap_sur.
  now rewrites.
Qed.
Next Obligation.
  (* preservation of identities *)
  apply fmap_inj.
  rewrite fmap_sur, fmap_id, id_right.
  apply iso_from_to.
Qed.
Next Obligation.
  (* preservation 复合: middle [to ∘ from] pair cancels （已译） *)
  apply fmap_inj.
  rewrite fmap_comp, !fmap_sur.
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (to (eso_iso _)) (from (eso_iso _))).
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition ff_eso_unit_iso `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F}
  (x : C) : x ≅ eso_obj (F x) := {|
  to   := prefmap (from (eso_iso (F x)));
  from := prefmap (to (eso_iso (F x)))
|}.
Next Obligation.
  apply fmap_inj.
  rewrite fmap_comp, !fmap_sur, fmap_id.
  apply iso_from_to.
Qed.
Next Obligation.
  apply fmap_inj.
  rewrite fmap_comp, !fmap_sur, fmap_id.
  apply iso_to_from.
Qed.

(* The counit cell F ◯ ff_eso_inverse F ≈ Id[D]. Its 同构 family
 literally [eso_iso]; conjugation coherence exactly the
 section law [fmap_sur]. （已译） *)
Definition ff_eso_counit `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F} :
  F ◯ ff_eso_inverse F ≈ Id[D].
Proof.
  exists (fun d => eso_iso d).
  intros d d' g.
  exact (fmap_sur (from (eso_iso d') ∘ g ∘ to (eso_iso d))).
Defined.

(* Conjugation coherence unit cell, standalone (opaque) 引理:
 two [eso_iso (F −)] pairs cancel after pushing [fmap[F]]
 through [fmap_sur]. （已译） *)
Lemma ff_eso_unit_coherence `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F}
  {x y : C} (f : x ~> y) :
  f ≈ from (ff_eso_unit_iso F y)
        ∘ fmap[ff_eso_inverse F ◯ F] f
        ∘ to (ff_eso_unit_iso F x).
Proof.
  apply fmap_inj.
  simpl.
  rewrite !fmap_comp, !fmap_sur.
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  rewrite <- comp_assoc.
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

(* The unit cell Id[C] ≈ ff_eso_inverse F ◯ F. *)
Definition ff_eso_unit `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F} :
  Id[C] ≈ ff_eso_inverse F ◯ F.
Proof.
  exists (fun x => ff_eso_unit_iso F x).
  intros x y f.
  exact (ff_eso_unit_coherence F f).
Defined.

(* The forward direction characterization: full + faithful +
 本质满射 函子 equivalences 范畴. （已译） *)
Theorem FF_ESO_Equivalence `(F : C ⟶ D)
  `{@Full C D F} `{@Faithful C D F} `{@EssentiallySurjective C D F} :
  EquivalenceOfCategories F.
Proof.
  exact (@Build_EquivalenceOfCategories C D F (ff_eso_inverse F)
           (ff_eso_counit F) (ff_eso_unit F)).
Defined.

(* The converse direction: every 等价 范畴 faithful,
 full, 本质满射. （已译） *)

Theorem Equivalence_Faithful `(E : @EquivalenceOfCategories C D F) :
  Faithful F.
Proof.
  constructor.
  intros x y f g Hfg.
  pose proof (`2 equivalence_unit x y f) as Hf; simpl in Hf.
  pose proof (`2 equivalence_unit x y g) as Hg; simpl in Hg.
  rewrite Hf, Hg.
  now rewrite Hfg.
Qed.

(* The quasi-inverse likewise faithful: apply same 论元 the
 symmetric 等价, i.e. read it off counit cell. （已译） *)
Corollary Equivalence_Inverse_Faithful
  `(E : @EquivalenceOfCategories C D F) :
  Faithful (@quasi_inverse C D F E).
Proof.
  exact (Equivalence_Faithful (@EquivalenceOfCategories_sym C D F E)).
Qed.

(* 相关说明。 （已译） *)
Definition equivalence_prefmap `(E : @EquivalenceOfCategories C D F)
  {x y : C} (g : F x ~> F y) : x ~> y :=
  from (equivalence_unit_at y)
    ∘ fmap[@quasi_inverse C D F E] g
    ∘ to (equivalence_unit_at x).

(*
   本节说明等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma equivalence_prefmap_sur `(E : @EquivalenceOfCategories C D F)
  {x y : C} (g : F x ~> F y) :
  fmap[F] (equivalence_prefmap E g) ≈ g.
Proof.
  apply (fmap_inj (Faithful := Equivalence_Inverse_Faithful E)).
  symmetry.
  apply (monic (Monic := iso_from_monic (equivalence_unit_at y))).
  apply (epic (Epic := iso_to_epic (equivalence_unit_at x))).
  exact (`2 equivalence_unit x y (equivalence_prefmap E g)).
Qed.

Theorem Equivalence_Full `(E : @EquivalenceOfCategories C D F) : Full F.
Proof.
  exact (@Build_Full C D F
           (fun x y g => equivalence_prefmap E g)
           (fun x y g => equivalence_prefmap_sur E g)).
Defined.

Theorem Equivalence_EssSurj `(E : @EquivalenceOfCategories C D F) :
  EssentiallySurjective F.
Proof.
  exact (@Build_EssentiallySurjective C D F
           (fun d => quasi_inverse d)
           (fun d => equivalence_counit_at d)).
Defined.
