Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.

Generalizable All Variables.

(*
   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Set Default Proof Using "All".

(*
   nLab: https://ncatlab.org/nlab/show/idempotent+monad

   本节说明伴随、单子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fmap_IsIsomorphism {C D : Category} (F : C ⟶ D) {x y : C}
  (f : x ~> y) (Hf : IsIsomorphism f) : IsIsomorphism (fmap[F] f).
Proof.
  destruct Hf as [g Hr Hl].
  refine {| two_sided_inverse := fmap[F] g |}.
  - rewrite <- fmap_comp, Hr; apply fmap_id.
  - rewrite <- fmap_comp, Hl; apply fmap_id.
Defined.

(* nLab: https://ncatlab.org/nlab/show/idempotent+monad

   The defining datum: join (μ) is an isomorphism at every object. *)
Class IdempotentMonad {C : Category} (M : C ⟶ C) `{@Monad C M} := {
  idem_join_iso {x} : IsIsomorphism (@join C M _ x)
}.

Arguments idem_join_iso {C} M {_ _} x.

(* 相关说明。 （已译） *)

(* These describe multiplication [join] invertible at one 对象;
 none them presupposes [IdempotentMonad], so each stated over bare
 单子 consumed pointwise below. （已译） *)

Section Characterizations.

Context {C : Category}.
Context {M : C ⟶ C}.
Context `{@Monad C M}.

(*
   本节说明单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition join_iso_ret_iso (x : C)
  (Hj : IsIsomorphism (@join C M _ x)) :
  IsIsomorphism (@ret C M _ (M x)).
Proof.
  refine {| two_sided_inverse := @join C M _ x |}.
  - destruct Hj as [k Hk_r Hk_l].
    assert (Hre : @ret C M _ (M x) ≈ k).
    { apply (comp_inverse_unique (@join C M _ x));
        [ apply (@join_ret C M _ x) | exact Hk_l ]. }
    rewrite Hre; exact Hk_l.
  - apply (@join_ret C M _ x).
Defined.

(* Conversely, if ret (M x) invertible then so join x, ret (M x)
 inverse (the symmetric inverse-uniqueness 论元). （已译） *)
Definition ret_iso_join_iso (x : C)
  (Hr : IsIsomorphism (@ret C M _ (M x))) :
  IsIsomorphism (@join C M _ x).
Proof.
  refine {| two_sided_inverse := @ret C M _ (M x) |}.
  - apply (@join_ret C M _ x).
  - destruct Hr as [k Hk_r Hk_l].
    assert (Hkj : k ≈ @join C M _ x).
    { apply (comp_inverse_unique (@ret C M _ (M x)));
        [ exact Hk_r | apply (@join_ret C M _ x) ]. }
    rewrite <- Hkj; exact Hk_r.
Defined.

(* Packaged as the two-way characterization (↔ is [iffT], Lib/Foundation.v). *)
Definition join_iso_iff_ret_M_iso (x : C) :
  IsIsomorphism (@join C M _ x) ↔ IsIsomorphism (@ret C M _ (M x)) :=
  (join_iso_ret_iso x, ret_iso_join_iso x).

(* 相关说明。 （已译） *)
Definition join_iso_fmap_ret (x : C)
  (Hj : IsIsomorphism (@join C M _ x)) :
  fmap[M] (@ret C M _ x) ≈ @ret C M _ (M x).
Proof.
  destruct Hj as [k Hk_r Hk_l].
  transitivity k.
  - rewrite <- id_left.
    rewrite <- Hk_l.
    rewrite <- comp_assoc.
    rewrite (@join_fmap_ret C M _ x).
    now rewrite id_right.
  - symmetry.
    rewrite <- id_left.
    rewrite <- Hk_l.
    rewrite <- comp_assoc.
    rewrite (@join_ret C M _ x).
    now rewrite id_right.
Qed.

End Characterizations.

(* * * A reflective subcategory induces idempotent 单子 （已译） *)

Section ReflectiveInducesIdempotent.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma reflective_counit_IsIso (x : Sub C S) :
  IsIsomorphism
    (@Category.Theory.Adjunction.counit
       (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) x).
Proof.
  unshelve econstructor.
  - exists (@Category.Theory.Adjunction.unit
              (Sub C S) C (reflector R) (Incl C S) (reflective_adj R)
              (Incl C S x)).
    apply (reflective_full R).
  - apply (@Category.Theory.Adjunction.fmap_counit_unit
             (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) x).
  - rewrite <- (counit_naturality (reflective_adj R)).
    apply (@Category.Theory.Adjunction.counit_fmap_unit
             (Sub C S) C (reflector R) (Incl C S) (reflective_adj R)
             (Incl C S x)).
Qed.

(* The 单子 C induced reflector ⊣ Incl, join = U ε F. （已译） *)
Definition Reflective_Monad : @Monad C (Incl C S ◯ reflector R) :=
  Adjunction_Induced_Monad (reflective_adj R).

(* Its join, being fmap[Incl] of the (invertible) counit, is invertible. *)
Definition Reflective_IdempotentMonad :
  @IdempotentMonad C (Incl C S ◯ reflector R) Reflective_Monad.
Proof.
  refine {| idem_join_iso := _ |}.
  intro x.
  apply (fmap_IsIsomorphism (Incl C S)
           (@Category.Theory.Adjunction.counit
              (Sub C S) C (reflector R) (Incl C S) (reflective_adj R)
              (reflector R x))).
  apply reflective_counit_IsIso.
Defined.

End ReflectiveInducesIdempotent.

(* * * An idempotent 单子 yields reflective subcategory (and EM 等价) （已译） *)

Section IdempotentInducesReflective.

Context {C : Category}.
Context {M : C ⟶ C}.
Context `{MM : @Monad C M}.
Context `{IM : @IdempotentMonad C M MM}.

(* The M-local 对象: those x whose unit ret x invertible. The
 subcategory full — every C-态射 between local 对象 retained —
 so [shom] terminal predicate. （已译） *)
Definition MLocal_Subcategory : Subcategory C :=
  {| sobj  := fun x => IsIsomorphism (@ret C M MM x)
   ; shom  := fun _ _ _ _ _ => True
   ; scomp := fun _ _ _ _ _ _ _ _ _ _ => I
   ; sid   := fun _ _ => I |}.

(*
   本节说明函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma local_inv_natural {a b : C}
  (oa : IsIsomorphism (@ret C M MM a)) (ob : IsIsomorphism (@ret C M MM b))
  (h : a ~> b) :
  h ∘ @two_sided_inverse C a (M a) (@ret C M MM a) oa
    ≈ @two_sided_inverse C b (M b) (@ret C M MM b) ob ∘ fmap[M] h.
Proof.
  destruct oa as [ta Ha_r Ha_l], ob as [tb Hb_r Hb_l]; simpl.
  assert (Hfm : fmap[M] h ≈ @ret C M MM b ∘ h ∘ ta).
  { rewrite <- (id_right (fmap[M] h)).
    rewrite <- Ha_r.
    rewrite comp_assoc.
    rewrite <- fmap_ret.
    reflexivity. }
  rewrite Hfm, !comp_assoc, Hb_l.
  now rewrite id_left.
Qed.

(* 相关说明。 （已译） *)

Definition idem_reflector_fobj (x : C) : Sub C MLocal_Subcategory :=
  (M x; join_iso_ret_iso x (idem_join_iso M x)).

Definition idem_reflector_fmap {x y : C} (f : x ~> y) :
  idem_reflector_fobj x ~{Sub C MLocal_Subcategory}~> idem_reflector_fobj y :=
  (fmap[M] f; I).

Lemma idem_reflector_fmap_respects {x y : C} (f g : x ~> y) (E : f ≈ g) :
  idem_reflector_fmap f ≈ idem_reflector_fmap g.
Proof. simpl; now rewrite E. Qed.

Lemma idem_reflector_fmap_id {x : C} :
  idem_reflector_fmap (@id C x) ≈ id.
Proof. simpl; apply fmap_id. Qed.

Lemma idem_reflector_fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
  idem_reflector_fmap (f ∘ g) ≈ idem_reflector_fmap f ∘ idem_reflector_fmap g.
Proof. simpl; apply fmap_comp. Qed.

Definition idem_reflector : C ⟶ Sub C MLocal_Subcategory :=
  Build_Functor C (Sub C MLocal_Subcategory)
    idem_reflector_fobj
    (fun x y f => idem_reflector_fmap f)
    (fun x y f g E => idem_reflector_fmap_respects f g E)
    (fun x => idem_reflector_fmap_id)
    (fun x y z f g => idem_reflector_fmap_comp f g).

(* * ** Unit counit reflector ⊣ Incl, 伴随 （已译） *)

Lemma idem_unit_natural (x y : C) (f : x ~> y) :
  fmap[Incl C MLocal_Subcategory ◯ idem_reflector] f ∘ @ret C M MM x
    ≈ @ret C M MM y ∘ fmap[Id[C]] f.
Proof. simpl; symmetry; apply fmap_ret. Qed.

Definition idem_unit_transform :
  Id[C] ⟹ (Incl C MLocal_Subcategory ◯ idem_reflector) :=
  Build_Transform'
    (F := Id[C]) (G := Incl C MLocal_Subcategory ◯ idem_reflector)
    (fun x => @ret C M MM x) idem_unit_natural.

Definition idem_counit_transform_fun (y : Sub C MLocal_Subcategory) :
  (idem_reflector ◯ Incl C MLocal_Subcategory) y ~> Id y :=
  (@two_sided_inverse C (`1 y) (M (`1 y)) (@ret C M MM (`1 y)) (`2 y); I).

Lemma idem_counit_natural (x y : Sub C MLocal_Subcategory) (f : x ~> y) :
  fmap[Id[Sub C MLocal_Subcategory]] f ∘ idem_counit_transform_fun x
    ≈ idem_counit_transform_fun y
        ∘ fmap[idem_reflector ◯ Incl C MLocal_Subcategory] f.
Proof. simpl; apply local_inv_natural. Qed.

Definition idem_counit_transform :
  (idem_reflector ◯ Incl C MLocal_Subcategory)
    ⟹ Id[Sub C MLocal_Subcategory] :=
  Build_Transform'
    (F := idem_reflector ◯ Incl C MLocal_Subcategory)
    (G := Id[Sub C MLocal_Subcategory])
    idem_counit_transform_fun idem_counit_natural.

(* First triangle 恒等: at reflector X counit underlies join X, and
 join X ∘ M ret unit law [join_fmap_ret]. （已译） *)
Lemma idem_triangle_counit (X : C) :
  transform[idem_counit_transform] (idem_reflector X)
    ∘ fmap[idem_reflector] (transform[idem_unit_transform] X) ≈ id.
Proof. cbn; apply (@join_fmap_ret C M MM X). Qed.

(* Second triangle 恒等: at local 对象 counit underlies unit
 inverse, inverse ∘ ret [is_left_inverse]. （已译） *)
Lemma idem_triangle_unit (X : Sub C MLocal_Subcategory) :
  fmap[Incl C MLocal_Subcategory] (transform[idem_counit_transform] X)
    ∘ transform[idem_unit_transform] (Incl C MLocal_Subcategory X) ≈ id.
Proof.
  cbn.
  apply (@is_left_inverse C (`1 X) (M (`1 X)) (@ret C M MM (`1 X)) (`2 X)).
Qed.

Definition idem_reflection_transform :
  idem_reflector ∹ Incl C MLocal_Subcategory :=
  {| Transformation.unit             := idem_unit_transform
   ; Transformation.counit           := idem_counit_transform
   ; Transformation.counit_fmap_unit := @idem_triangle_counit
   ; Transformation.fmap_counit_unit := @idem_triangle_unit |}.

Definition idem_reflective_adj :
  idem_reflector ⊣ Incl C MLocal_Subcategory :=
  Adjunction_from_Transform idem_reflection_transform.

(* The M-local subcategory is full: every C-morphism between local objects is
   retained. *)
Definition MLocal_Full : Construction.Subcategory.Full C MLocal_Subcategory :=
  fun _ _ _ _ _ => I.

(* The M-local subcategory is a full reflective subcategory of C. *)
Definition Idempotent_Reflective : Reflective MLocal_Subcategory :=
  @Build_Reflective C MLocal_Subcategory
    MLocal_Full idem_reflector idem_reflective_adj.

(* * ** Eilenberg–Moore algebras coincide M-local 对象 （已译） *)

(* Every local 对象 carries canonical M-algebra whose structure map the
 inverse unit; action law reduces fmap (ret⁻¹) = join, both
 being inverse fmap ret = ret M. （已译） *)
Definition local_algebra {b : C} (ob : IsIsomorphism (@ret C M MM b)) :
  @TAlgebra C M MM b.
Proof.
  refine {| t_alg := @two_sided_inverse C b (M b) (@ret C M MM b) ob |}.
  - exact (@is_left_inverse C b (M b) (@ret C M MM b) ob).
  - assert (Hfj : fmap[M] (@two_sided_inverse C b (M b) (@ret C M MM b) ob)
                    ≈ @join C M MM b).
    { apply (comp_inverse_unique (fmap[M] (@ret C M MM b))).
      - rewrite <- fmap_comp.
        rewrite (@is_right_inverse C b (M b) (@ret C M MM b) ob).
        apply fmap_id.
      - rewrite (join_iso_fmap_ret b (idem_join_iso M b)).
        apply (@join_ret C M MM b). }
    now rewrite Hfj.
Defined.

(*
   本节说明 Idempotent 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition algebra_ret_iso {a : C} (alg : @TAlgebra C M MM a) :
  IsIsomorphism (@ret C M MM a).
Proof.
  refine {| two_sided_inverse := @t_alg C M MM a alg |}.
  - rewrite fmap_ret.
    rewrite <- (join_iso_fmap_ret a (idem_join_iso M a)).
    rewrite <- fmap_comp.
    rewrite (@t_id C M MM a alg).
    apply fmap_id.
  - exact (@t_id C M MM a alg).
Defined.

(* * ** The comparison 函子 Sub ⟶ EM inverse （已译） *)

Definition idem_G_fobj (s : Sub C MLocal_Subcategory) : EilenbergMoore M :=
  (`1 s; local_algebra (`2 s)).

Definition idem_G_fmap {s t : Sub C MLocal_Subcategory} (f : s ~> t) :
  idem_G_fobj s ~{EilenbergMoore M}~> idem_G_fobj t.
Proof.
  refine {| t_alg_hom := `1 f |}.
  simpl.
  apply local_inv_natural.
Defined.

Lemma idem_G_fmap_respects {s t : Sub C MLocal_Subcategory}
  (f g : s ~> t) (E : f ≈ g) : idem_G_fmap f ≈ idem_G_fmap g.
Proof. simpl; exact E. Qed.

Lemma idem_G_fmap_id {s : Sub C MLocal_Subcategory} :
  idem_G_fmap (@id (Sub C MLocal_Subcategory) s) ≈ id.
Proof. simpl; reflexivity. Qed.

Lemma idem_G_fmap_comp {s t u : Sub C MLocal_Subcategory}
  (f : t ~> u) (g : s ~> t) :
  idem_G_fmap (f ∘ g) ≈ idem_G_fmap f ∘ idem_G_fmap g.
Proof. simpl; reflexivity. Qed.

Definition idem_G : Sub C MLocal_Subcategory ⟶ EilenbergMoore M :=
  Build_Functor (Sub C MLocal_Subcategory) (EilenbergMoore M)
    idem_G_fobj
    (fun s t f => idem_G_fmap f)
    (fun s t f g E => idem_G_fmap_respects f g E)
    (fun s => idem_G_fmap_id)
    (fun s t u f g => idem_G_fmap_comp f g).

(* [idem_G] faithful: EM-态射 compared underlying arrows,
 exactly underlying arrows Sub-态射. （已译） *)
#[local] Instance idem_G_Faithful : Faithful idem_G.
Proof.
  refine {| fmap_inj := _ |}.
  intros x y f g Hfg; exact Hfg.
Defined.

(* [idem_G] is full: any algebra homomorphism is (its underlying arrow lifted
   into the full subcategory). *)
Definition idem_G_prefmap {s t : Sub C MLocal_Subcategory}
  (h : idem_G s ~> idem_G t) : s ~> t := (t_alg_hom[h]; I).

Lemma idem_G_fmap_sur {s t : Sub C MLocal_Subcategory}
  (h : idem_G s ~> idem_G t) : fmap[idem_G] (idem_G_prefmap h) ≈ h.
Proof. simpl; reflexivity. Qed.

#[local] Instance idem_G_Full : Functor.Full idem_G :=
  {| prefmap := @idem_G_prefmap; fmap_sur := @idem_G_fmap_sur |}.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition idem_eso_obj (z : EilenbergMoore M) : Sub C MLocal_Subcategory :=
  (`1 z; algebra_ret_iso (`2 z)).

Definition idem_eso_iso (z : EilenbergMoore M) :
  idem_G (idem_eso_obj z) ≅ z.
Proof.
  unshelve refine (@Build_Isomorphism (EilenbergMoore M)
    (idem_G (idem_eso_obj z)) z
    {| t_alg_hom := id |} {| t_alg_hom := id |} _ _).
  - cbn; rewrite fmap_id; cat.
  - cbn; rewrite fmap_id; cat.
  - cbn; cat.
  - cbn; cat.
Defined.

#[local] Instance idem_G_ESO : EssentiallySurjective idem_G.
Proof.
  refine {| eso_obj := idem_eso_obj; eso_iso := idem_eso_iso |}.
Defined.

(* The Eilenberg–Moore 范畴 idempotent 单子 equivalent its
 subcategory M-local 对象. （已译） *)
Definition Idempotent_EM_Equivalence : EquivalenceOfCategories idem_G :=
  FF_ESO_Equivalence idem_G.

End IdempotentInducesReflective.
