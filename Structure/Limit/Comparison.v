Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Span.
Require Import Category.Adjunction.Continuity.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Roof.

Generalizable All Variables.

(** * The canonical comparison arrow for limits of composites *)

(*
   nLab: https://ncatlab.org/nlab/show/preserved+limit

   本文件给出比较函子相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Reindexing a cone along a functor between shapes *)

Section Reindex.

Context {J' J C : Category} (W : J' ⟶ J) {F : J ⟶ C}.

(* Restricting a cone over [F] along [W]: the same apex, the legs at the
   objects [W j'], the coherence read off [N]'s at the arrows [fmap[W] f]. *)
Definition cone_reindex (N : Cone F) : Cone (F ◯ W) :=
  @Build_Cone J' C (F ◯ W) (vertex_obj[N])
    (@Build_ACone J' C (vertex_obj[N]) (F ◯ W)
       (fun j' => cone_leg N (W j'))
       (fun x y f =>
          @cone_coherence J C (vertex_obj[N]) F (@coneFrom _ _ _ N)
            (W x) (W y) (fmap[W] f))).

Example cone_reindex_apex (N : Cone F) :
  vertex_obj[cone_reindex N] = vertex_obj[N] := eq_refl.

Example cone_reindex_leg (N : Cone F) (j' : J') :
  cone_leg (cone_reindex N) j' = cone_leg N (W j') := eq_refl.

End Reindex.

(*
   本节说明函子、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example cone_reindex_id_apex {J C : Category} {F : J ⟶ C} (N : Cone F) :
  vertex_obj[cone_reindex Id[J] N] = vertex_obj[N] := eq_refl.

Example cone_reindex_id_leg {J C : Category} {F : J ⟶ C} (N : Cone F) (j : J) :
  cone_leg (cone_reindex Id[J] N) j = cone_leg N j := eq_refl.

Example cone_reindex_comp_apex {J'' J' J C : Category} (W : J' ⟶ J) (V : J'' ⟶ J')
  {F : J ⟶ C} (N : Cone F) :
  vertex_obj[cone_reindex V (cone_reindex W N)] = vertex_obj[cone_reindex (W ◯ V) N]
  := eq_refl.

Example cone_reindex_comp_leg {J'' J' J C : Category} (W : J' ⟶ J) (V : J'' ⟶ J')
  {F : J ⟶ C} (N : Cone F) (j : J'') :
  cone_leg (cone_reindex V (cone_reindex W N)) j = cone_leg (cone_reindex (W ◯ V) N) j
  := eq_refl.

(** ** The comparison with a change of shape: H (Lim F) ~> Lim ((H ◯ F) ◯ W) *)

Section ReindexComparison.

Context {J' J C D : Category} (W : J' ⟶ J) {F : J ⟶ C} (H : C ⟶ D).

(*
   本节说明（余）极限、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition reindex_comparison (N : Cone F)
  {M : Cone ((H ◯ F) ◯ W)} (HM : IsLimitCone M) :
  H (vertex_obj[N]) ~{D}~> vertex_obj[M] :=
  cone_comparison H (cone_reindex W N) (islimitcone_assoc HM).

Lemma reindex_comparison_commutes (N : Cone F)
  {M : Cone ((H ◯ F) ◯ W)} (HM : IsLimitCone M) (j' : J') :
  cone_leg M j' ∘ reindex_comparison N HM ≈ fmap[H] (cone_leg N (W j')).
Proof.
  exact (cone_comparison_commutes H (cone_reindex W N) (islimitcone_assoc HM) j').
Qed.

Lemma reindex_comparison_unique (N : Cone F)
  {M : Cone ((H ◯ F) ◯ W)} (HM : IsLimitCone M)
  (v : H (vertex_obj[N]) ~{D}~> vertex_obj[M]) :
  (∀ j' : J', cone_leg M j' ∘ v ≈ fmap[H] (cone_leg N (W j'))) →
  reindex_comparison N HM ≈ v.
Proof.
  intro Hv.
  exact (cone_comparison_unique H (cone_reindex W N) (islimitcone_assoc HM) v Hv).
Qed.

(* Invertibility is exactly limit-ness of the image of the reindexed cone,
   both ways. *)
Definition reindex_comparison_iso (N : Cone F)
  {M : Cone ((H ◯ F) ◯ W)} (HM : IsLimitCone M)
  (HN : IsLimitCone (FCone H (cone_reindex W N))) :
  IsIsomorphism (reindex_comparison N HM) :=
  LimitCone_comparison_iso H (cone_reindex W N) (islimitcone_assoc HM) HN.

Definition reindex_comparison_iso_LimitCone (N : Cone F)
  {M : Cone ((H ◯ F) ◯ W)} (HM : IsLimitCone M)
  (Hi : IsIsomorphism (reindex_comparison N HM)) :
  IsLimitCone (FCone H (cone_reindex W N)) :=
  comparison_iso_LimitCone H (cone_reindex W N) (islimitcone_assoc HM) Hi.

End ReindexComparison.

(** ** The biconditional, bundled; one limit cone suffices *)

Section LimitBundle.

Context {J C D : Category} {K : J ⟶ C} (F : C ⟶ D).

(* Riehl's Lemma 3.4.3 and Mac Lane's V.4 Exercise 5 as one statement: the
   two directions are Preservation.v's [comparison_iso_of_PreservesLimitCone]
   and [PreservesLimitCone_of_comparison]. *)
Definition preserves_iff_comparison_iso {M : Cone (F ◯ K)} (HM : IsLimitCone M) :
  PreservesLimitCone K F ↔
  (∀ N : Cone K, IsLimitCone N → IsIsomorphism (cone_comparison F N HM)) :=
  (fun P => comparison_iso_of_PreservesLimitCone F P HM,
   PreservesLimitCone_of_comparison F HM).

(* Preserving ONE limit cone of [K] is preserving them all: any other is
   isomorphic to it by [limitcone_iso], the image of that isomorphism is a
   cone isomorphism by [FCone_iso], and limit-ness transports along it. *)
Definition PreservesLimitCone_of_cone (N0 : Cone K) (HN0 : IsLimitCone N0)
  (H0 : IsLimitCone (FCone F N0)) : PreservesLimitCone K F :=
  fun N HN => limitcone_transport (FCone_iso F (limitcone_iso HN0 HN)) H0.

Definition PreservesLimitCone_of_comparison_iso (N0 : Cone K) (HN0 : IsLimitCone N0)
  {M : Cone (F ◯ K)} (HM : IsLimitCone M)
  (Hi : IsIsomorphism (cone_comparison F N0 HM)) : PreservesLimitCone K F :=
  PreservesLimitCone_of_cone N0 HN0 (comparison_iso_LimitCone F N0 HM Hi).

End LimitBundle.

(** ** The colimit comparison and its biconditional *)

Section CoComparison.

Context {J C D : Category} {K : J ⟶ C} (F : C ⟶ D).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition colimitcocone_iso {N M : Cocone K}
  (HN : IsColimitCocone N) (HM : IsColimitCocone M) : ConeIso N M :=
  limitcone_iso HN HM.

Lemma cocone_comparison_commutes (N : Cocone K) {M : Cocone (F ◯ K)}
  (HM : IsColimitCocone M) (x : J) :
  cocone_comparison F N HM ∘ cocone_inj M x ≈ fmap[F] (cocone_inj N x).
Proof.
  exact (unique_property (HM (FCocone F N)) x).
Qed.

Lemma cocone_comparison_unique (N : Cocone K) {M : Cocone (F ◯ K)}
  (HM : IsColimitCocone M) (v : vertex_obj[M] ~{D}~> F (vertex_obj[N])) :
  (∀ x : J, v ∘ cocone_inj M x ≈ fmap[F] (cocone_inj N x)) →
  cocone_comparison F N HM ≈ v.
Proof.
  intro Hv. exact (uniqueness (HM (FCocone F N)) v Hv).
Qed.

Definition ColimitCocone_comparison_iso (N : Cocone K) {M : Cocone (F ◯ K)}
  (HM : IsColimitCocone M) (HN : IsColimitCocone (FCocone F N)) :
  IsIsomorphism (cocone_comparison F N HM) :=
  @Build_IsIsomorphism D (vertex_obj[M]) (F (vertex_obj[N]))
    (cocone_comparison F N HM)
    (from `1 (limitcone_iso HN HM))
    (iso_from_to `1 (limitcone_iso HN HM))
    (iso_to_from `1 (limitcone_iso HN HM)).

Definition comparison_iso_ColimitCocone (N : Cocone K) {M : Cocone (F ◯ K)}
  (HM : IsColimitCocone M) (Hi : IsIsomorphism (cocone_comparison F N HM)) :
  IsColimitCocone (FCocone F N).
Proof.
  assert (ci : ConeIso (FCocone F N) M).
  { unshelve eexists.
    - (* the comparison, read as an isomorphism of [D^op]: its two inverse
         laws swap roles under [^op] *)
      exact (@Build_Isomorphism (D^op) (F (vertex_obj[N])) (vertex_obj[M])
               (cocone_comparison F N HM)
               (@two_sided_inverse D _ _ _ Hi)
               (@is_left_inverse D _ _ _ Hi)
               (@is_right_inverse D _ _ _ Hi)).
    - intro x; exact (cocone_comparison_commutes N HM x). }
  exact (limitcone_transport (ConeIso_sym ci) HM).
Defined.

Definition PreservesColimitCocone_of_comparison {M : Cocone (F ◯ K)}
  (HM : IsColimitCocone M)
  (H : ∀ N : Cocone K, IsColimitCocone N → IsIsomorphism (cocone_comparison F N HM)) :
  PreservesColimitCocone K F :=
  fun N HN => comparison_iso_ColimitCocone N HM (H N HN).

Definition comparison_iso_of_PreservesColimitCocone
  (P : PreservesColimitCocone K F) {M : Cocone (F ◯ K)} (HM : IsColimitCocone M)
  (N : Cocone K) (HN : IsColimitCocone N) :
  IsIsomorphism (cocone_comparison F N HM) :=
  ColimitCocone_comparison_iso N HM (P N HN).

(* Riehl's Exercise 3.4.i: the dual of Lemma 3.4.3. *)
Definition preserves_colimit_iff_comparison_iso {M : Cocone (F ◯ K)}
  (HM : IsColimitCocone M) :
  PreservesColimitCocone K F ↔
  (∀ N : Cocone K, IsColimitCocone N → IsIsomorphism (cocone_comparison F N HM)) :=
  (fun P => comparison_iso_of_PreservesColimitCocone P HM,
   PreservesColimitCocone_of_comparison HM).

End CoComparison.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition PreservesColimitCocone_of_cocone@{jo co ch do +}
  {J : Category@{jo ch ch}} {C : Category@{co ch ch}}
  {D : Category@{do ch ch}} {K : J ⟶ C} (F : C ⟶ D)
  (N0 : Cocone K) (HN0 : IsColimitCocone N0)
  (H0 : IsColimitCocone (FCocone F N0)) : PreservesColimitCocone K F :=
  fun N HN =>
    limitcone_transport (FCocone_iso F (colimitcocone_iso HN0 HN)) H0.

(** ** Riehl's whiskering identity F ∘ Δc = Δ(Fc), at functor level *)

Section Whisker.

Context {J C D : Category} (F : C ⟶ D) (c : C).

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition const_image_iso :
  @equiv _ (@Functor_Setoid J D) (F ◯ Δ[J](c)) (Δ[J](F c)).
Proof.
  exists (fun x => iso_id).
  intros x y f; simpl.
  rewrite fmap_id. cat.
Defined.

Example const_image_iso_component (x : J) :
  to (`1 const_image_iso x) = id[F c] := eq_refl.

End Whisker.

(** ** Riehl's warm-up: the pullback comparison F (X ×_Z Y) ~> F X ×_{F Z} F Y *)

Section PullbackWarmup.

Context {C D : Category} (H : C ⟶ D) (F : Cospan C).

Definition pullback_comparison (N : Cone F) {M : Cone (H ◯ F)}
  (HM : IsLimitCone M) : H (vertex_obj[N]) ~{D}~> vertex_obj[M] :=
  cone_comparison H N HM.

Example pullback_comparison_is (N : Cone F) {M : Cone (H ◯ F)}
  (HM : IsLimitCone M) :
  pullback_comparison N HM = cone_comparison H N HM := eq_refl.

End PullbackWarmup.

(** ** RAPL restated: the comparison of a right adjoint is invertible *)

Section RAPLRestated.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U)
        {J : Category} (G : J ⟶ C).

Definition rapl_comparison_iso {M : Cone (U ◯ G)} (HM : IsLimitCone M)
  (N : Cone G) (HN : IsLimitCone N) :
  IsIsomorphism (cone_comparison U N HM) :=
  comparison_iso_of_PreservesLimitCone U
    (right_adjoint_PreservesLimitCone A G) HM N HN.

End RAPLRestated.

(** ** Discrete shapes: a cone is limiting iff its legs are an indexed product *)

(*
   本节说明函子、（余）极限、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition DiscreteCat_Functor'@{o h p uo uh up +}
  {A : Type@{o}} {C : Category@{uo uh up}} (f : A → C) :
  DiscreteCat@{o h p} A ⟶ C := @DiscreteCat_Functor A C f.

Section DiscreteBridge.

Universe o h p uo uh up.

Context {A : Type@{o}} {C : Category@{uo uh up}} (G : DiscreteCat@{o h p} A ⟶ C).

(* Any family of legs is a cone over a discrete diagram: coherence has only
   the identity arrows to check. *)
Definition discrete_cone (c : C) (pi : ∀ a : A, c ~> G a) : Cone G.
Proof.
  unshelve refine (@Build_Cone (DiscreteCat A) C G c
                     (@Build_ACone (DiscreteCat A) C c G pi _)).
  intros x y e; destruct e.
  change (@eq_refl A x) with (@id (DiscreteCat A) x).
  rewrite fmap_id.
  apply id_left.
Defined.

Example discrete_cone_leg (c : C) (pi : ∀ a : A, c ~> G a) (a : A) :
  cone_leg (discrete_cone c pi) a = pi a := eq_refl.

(* The two readings of "product" coincide, for ANY functor out of a discrete
   shape — in particular for image diagrams [F ◯ G]. *)
Definition discrete_IsLimitCone_of_IsIndexedProduct (N : Cone G)
  (HP : IsIndexedProduct (fobj[G]) (vertex_obj[N]) (cone_leg N)) :
  IsLimitCone N.
Proof.
  intro M.
  destruct (iprod_desc HP (cone_leg M)) as [u Hu Huniq].
  exists u.
  - exact Hu.
  - exact Huniq.
Defined.

(* The converse Structure/Limit/Product.v's [limit_is_indexed_product] never
   had (Functor/Hom/Limit.v records the absence). *)
Definition discrete_IsIndexedProduct_of_IsLimitCone (N : Cone G)
  (HN : IsLimitCone N) :
  IsIndexedProduct (fobj[G]) (vertex_obj[N]) (cone_leg N) :=
  {| iprod_desc := fun c pi => HN (discrete_cone c pi) |}.

End DiscreteBridge.

(** ** Binary products: [CartesianFunctor] is invertibility of the comparison *)

Section BinaryProducts.

Context {C : Category} `{@Cartesian C}.

(* A two-element family and its product's projections, as an indexed
   product over [bool]. *)
Definition binary_proj (f : bool → C) (b : bool) : f true × f false ~> f b :=
  match b return (f true × f false ~> f b) with
  | true => exl
  | false => exr
  end.

Definition IsIndexedProduct_binary (f : bool → C) :
  IsIndexedProduct f (f true × f false) (binary_proj f).
Proof.
  constructor; intros c pi.
  exists (pi true △ pi false).
  - intros [|]; simpl.
    + apply exl_fork.
    + apply exr_fork.
  - intros v Hv.
    symmetry.
    apply (snd (ump_products _ _ _)).
    split.
    + exact (Hv true).
    + exact (Hv false).
Defined.

Definition binary_fam (x y : C) : bool → C := fun b => if b then x else y.

End BinaryProducts.

Section CartesianBridge.

Context {C D : Category} (F : C ⟶ D) `{@Cartesian C} `{@Cartesian D}.

(* the product cone of [C] over the discrete two-object diagram of [f] *)
Definition binary_cone (f : bool → C) : Cone (DiscreteCat_Functor' f) :=
  discrete_cone (DiscreteCat_Functor' f) (f true × f false) (binary_proj f).

Definition binary_cone_IsLimitCone (f : bool → C) : IsLimitCone (binary_cone f) :=
  discrete_IsLimitCone_of_IsIndexedProduct _ (binary_cone f)
    (IsIndexedProduct_binary f).

(* the product cone of [D] over the IMAGE diagram [F ◯ DiscreteCat_Functor' f] *)
Definition binary_image_cone (f : bool → C) : Cone (F ◯ DiscreteCat_Functor' f) :=
  discrete_cone (F ◯ DiscreteCat_Functor' f) (F (f true) × F (f false))
    (binary_proj (fun b => F (f b))).

Definition binary_image_cone_IsLimitCone (f : bool → C) :
  IsLimitCone (binary_image_cone f) :=
  discrete_IsLimitCone_of_IsIndexedProduct _ (binary_image_cone f)
    (IsIndexedProduct_binary (fun b => F (f b))).

(* The comparison F (x × y) ~> F x × F y, as the general [cone_comparison]
   at the two product cones. *)
Definition binary_comparison (f : bool → C) :
  F (f true × f false) ~{D}~> F (f true) × F (f false) :=
  cone_comparison F (binary_cone f) (binary_image_cone_IsLimitCone f).

Lemma binary_comparison_exl (f : bool → C) :
  exl ∘ binary_comparison f ≈ fmap[F] exl.
Proof.
  exact (cone_comparison_commutes F (binary_cone f)
           (binary_image_cone_IsLimitCone f) true).
Qed.

Lemma binary_comparison_exr (f : bool → C) :
  exr ∘ binary_comparison f ≈ fmap[F] exr.
Proof.
  exact (cone_comparison_commutes F (binary_cone f)
           (binary_image_cone_IsLimitCone f) false).
Qed.

(* It is the pairing of the images of the projections — the forward map
   [prod_out] of Functor/Structure/Cartesian.v's class, computed rather
   than postulated. *)
Lemma binary_comparison_fork (f : bool → C) :
  binary_comparison f ≈ fmap[F] exl △ fmap[F] exr.
Proof.
  apply (snd (ump_products _ _ _)).
  split.
  - apply binary_comparison_exl.
  - apply binary_comparison_exr.
Qed.

Theorem cartesian_functor_iff_comparison_iso :
  @CartesianFunctor C D F _ _ ↔
  (∀ x y : C, IsIsomorphism (binary_comparison (binary_fam x y))).
Proof.
  split.
  - intros HF x y.
    unshelve refine {| two_sided_inverse := from (@fobj_prod_iso _ _ F _ _ HF x y) |}.
    + rewrite binary_comparison_fork.
      rewrite fmap_exl, fmap_exr; simpl.
      rewrite fork_comp.
      rewrite fork_exl_exr.
      rewrite id_left.
      apply iso_to_from.
    + rewrite binary_comparison_fork.
      rewrite fmap_exl, fmap_exr; simpl.
      rewrite fork_comp.
      rewrite fork_exl_exr.
      rewrite id_left.
      apply iso_from_to.
  - intros Hi.
    unshelve refine {| fobj_prod_iso := fun x y => IsIsoToIso _ (Hi x y) |}.
    + intros x y; simpl. symmetry. apply (binary_comparison_exl (binary_fam x y)).
    + intros x y; simpl. symmetry. apply (binary_comparison_exr (binary_fam x y)).
    + intros x y z f g; simpl.
      rewrite <- (id_left (fmap[F] (f △ g))).
      rewrite <- (is_left_inverse (IsIsomorphism := Hi y z)).
      rewrite <- comp_assoc.
      apply compose_respects; [reflexivity |].
      apply (snd (ump_products _ _ _)).
      split.
      * rewrite comp_assoc.
        rewrite (binary_comparison_exl (binary_fam y z)).
        rewrite <- fmap_comp.
        now rewrite exl_fork.
      * rewrite comp_assoc.
        rewrite (binary_comparison_exr (binary_fam y z)).
        rewrite <- fmap_comp.
        now rewrite exr_fork.
Qed.

(* The issue's headline: a cartesian functor is exactly a functor preserving
   the limit cones of the two-object discrete diagrams. *)
Theorem cartesian_functor_iff_preserves_binary_products :
  @CartesianFunctor C D F _ _ ↔
  (∀ x y : C, PreservesLimitCone (DiscreteCat_Functor' (binary_fam x y)) F).
Proof.
  split.
  - intros HF x y.
    exact (PreservesLimitCone_of_comparison_iso F (binary_cone _)
             (binary_cone_IsLimitCone _) (binary_image_cone_IsLimitCone _)
             (fst cartesian_functor_iff_comparison_iso HF x y)).
  - intros P.
    apply (snd cartesian_functor_iff_comparison_iso).
    intros x y.
    exact (comparison_iso_of_PreservesLimitCone F (P x y)
             (binary_image_cone_IsLimitCone _) (binary_cone _)
             (binary_cone_IsLimitCone _)).
Qed.

End CartesianBridge.

(** ** The terminal object: [TerminalFunctor] is invertibility of the comparison *)

Section NullaryProducts.

Context {C : Category} `{@Terminal C}.

Definition nullary_proj (f : False → C) (a : False) : terminal_obj ~> f a :=
  match a with end.

Definition IsIndexedProduct_nullary (f : False → C) :
  IsIndexedProduct f terminal_obj (nullary_proj f).
Proof.
  constructor; intros c pi.
  exists one.
  - intros [].
  - intros v _; apply one_unique.
Defined.

Definition nullary_fam : False → C := fun a => match a with end.

End NullaryProducts.

Section TerminalBridge.

Context {C D : Category} (F : C ⟶ D) `{@Terminal C} `{@Terminal D}.

Definition nullary_cone (f : False → C) : Cone (DiscreteCat_Functor' f) :=
  discrete_cone (DiscreteCat_Functor' f) terminal_obj (nullary_proj f).

Definition nullary_cone_IsLimitCone (f : False → C) : IsLimitCone (nullary_cone f) :=
  discrete_IsLimitCone_of_IsIndexedProduct _ (nullary_cone f)
    (IsIndexedProduct_nullary f).

Definition nullary_image_cone (f : False → C) :
  Cone (F ◯ DiscreteCat_Functor' f) :=
  discrete_cone (F ◯ DiscreteCat_Functor' f) terminal_obj
    (nullary_proj (fun a => F (f a))).

Definition nullary_image_cone_IsLimitCone (f : False → C) :
  IsLimitCone (nullary_image_cone f) :=
  discrete_IsLimitCone_of_IsIndexedProduct _ (nullary_image_cone f)
    (IsIndexedProduct_nullary (fun a => F (f a))).

(* The comparison F 1 ~> 1: the unique map into the terminal object. *)
Definition terminal_comparison (f : False → C) :
  F terminal_obj ~{D}~> terminal_obj :=
  cone_comparison F (nullary_cone f) (nullary_image_cone_IsLimitCone f).

Lemma terminal_comparison_one (f : False → C) : terminal_comparison f ≈ one.
Proof. apply one_unique. Qed.

(* Functor/Structure/Terminal.v records [fobj_one_iso : 1 ≅ F 1] with
   [to : 1 ~> F 1]; the comparison is therefore its [from]. *)
Theorem terminal_functor_iff_comparison_iso :
  @TerminalFunctor C D F _ _ ↔ IsIsomorphism (terminal_comparison nullary_fam).
Proof.
  split.
  - intros HF.
    unshelve refine {| two_sided_inverse := to (@fobj_one_iso _ _ F _ _ HF) |}.
    + apply one_unique.
    + rewrite terminal_comparison_one.
      rewrite <- (one_unique (from (@fobj_one_iso _ _ F _ _ HF)) one).
      apply iso_to_from.
  - intros Hi.
    unshelve refine {| fobj_one_iso := iso_sym (IsIsoToIso _ Hi) |}.
    intros X; simpl.
    rewrite <- (id_left (fmap[F] one)).
    rewrite <- (is_left_inverse (IsIsomorphism := Hi)).
    rewrite <- comp_assoc.
    apply compose_respects; [reflexivity |].
    apply one_unique.
Qed.

Theorem terminal_functor_iff_preserves_terminal :
  @TerminalFunctor C D F _ _ ↔
  PreservesLimitCone (DiscreteCat_Functor' nullary_fam) F.
Proof.
  split.
  - intros HF.
    exact (PreservesLimitCone_of_comparison_iso F (nullary_cone _)
             (nullary_cone_IsLimitCone _) (nullary_image_cone_IsLimitCone _)
             (fst terminal_functor_iff_comparison_iso HF)).
  - intros P.
    apply (snd terminal_functor_iff_comparison_iso).
    exact (comparison_iso_of_PreservesLimitCone F P
             (nullary_image_cone_IsLimitCone _) (nullary_cone _)
             (nullary_cone_IsLimitCone _)).
Qed.

End TerminalBridge.
