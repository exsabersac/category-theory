Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(* * * Limits product 范畴 computed componentwise （已译） *)

(*
   Book:  Riehl, "Category Theory in Context", 2nd ed., §3.4 Exercise
   nLab:  https://ncatlab.org/nlab/show/product+category
   nLab:  https://ncatlab.org/nlab/show/complete+category

   本文件给出极限相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

Section ProductCones.

Context {J C D : Category}.
Context (K : J ⟶ C ∏ D).

(* 相关说明。 （已译） *)

Definition prod_cone (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) : Cone K.
Proof.
  unshelve refine
    (@Build_Cone J (C ∏ D) K (vertex_obj[N1], vertex_obj[N2])
       (@Build_ACone J (C ∏ D) (vertex_obj[N1], vertex_obj[N2]) K
          (fun x => (cone_leg N1 x, cone_leg N2 x)) _)).
  intros x y f; split.
  - exact (cone_leg_coh N1 f).
  - exact (cone_leg_coh N2 f).
Defined.

Example prod_cone_apex (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  vertex_obj[prod_cone N1 N2] = (vertex_obj[N1], vertex_obj[N2]) := eq_refl.

Example prod_cone_leg (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) (x : J) :
  cone_leg (prod_cone N1 N2) x = (cone_leg N1 x, cone_leg N2 x) := eq_refl.

(* 相关说明。 （已译） *)

Example prod_cone_fst_leg (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) (x : J) :
  cone_leg (FCone Fst (prod_cone N1 N2)) x = cone_leg N1 x := eq_refl.

Example prod_cone_snd_leg (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) (x : J) :
  cone_leg (FCone Snd (prod_cone N1 N2)) x = cone_leg N2 x := eq_refl.

Definition prod_cone_fst_iso (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  ConeIso (FCone Fst (prod_cone N1 N2)) N1.
Proof.
  exists iso_id.
  intro x; simpl; now rewrite id_right.
Defined.

Definition prod_cone_snd_iso (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  ConeIso (FCone Snd (prod_cone N1 N2)) N2.
Proof.
  exists iso_id.
  intro x; simpl; now rewrite id_right.
Defined.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)

Definition prod_IsLimitCone {N1 : Cone (Fst ◯ K)} {N2 : Cone (Snd ◯ K)}
  (H1 : IsLimitCone N1) (H2 : IsLimitCone N2) :
  IsLimitCone (prod_cone N1 N2).
Proof.
  intro M.
  unshelve refine
    {| unique_obj := (unique_obj (H1 (FCone Fst M)),
                      unique_obj (H2 (FCone Snd M))) |}.
  - intro x; split.
    + exact (unique_property (H1 (FCone Fst M)) x).
    + exact (unique_property (H2 (FCone Snd M)) x).
  - intros [v1 v2] Hv; split.
    + apply (uniqueness (H1 (FCone Fst M))).
      intro x; exact (fst (Hv x)).
    + apply (uniqueness (H2 (FCone Snd M))).
      intro x; exact (snd (Hv x)).
Defined.

Example prod_IsLimitCone_med {N1 : Cone (Fst ◯ K)} {N2 : Cone (Snd ◯ K)}
  (H1 : IsLimitCone N1) (H2 : IsLimitCone N2) (M : Cone K) :
  unique_obj (prod_IsLimitCone H1 H2 M)
    = (unique_obj (H1 (FCone Fst M)), unique_obj (H2 (FCone Snd M)))
  := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition Fst_PreservesLimitCone : PreservesLimitCone K Fst.
Proof.
  intros N HN M.
  pose (P := prod_cone M (FCone Snd N)).
  unshelve refine {| unique_obj := fst (unique_obj (HN P)) |}.
  - intro x; exact (fst (unique_property (HN P) x)).
  - intros v Hv.
    refine (fst (uniqueness (HN P) (v, id) _)).
    intro x; split.
    + exact (Hv x).
    + simpl; now rewrite id_right.
Defined.

Definition Snd_PreservesLimitCone : PreservesLimitCone K Snd.
Proof.
  intros N HN M.
  pose (P := prod_cone (FCone Fst N) M).
  unshelve refine {| unique_obj := snd (unique_obj (HN P)) |}.
  - intro x; exact (snd (unique_property (HN P) x)).
  - intros v Hv.
    refine (snd (uniqueness (HN P) (id, v) _)).
    intro x; split.
    + simpl; now rewrite id_right.
    + exact (Hv x).
Defined.

(* 相关说明。 （已译） *)

(* A cone over [K] isomorphic pairing projections; the
 apex 同构 [(id, id) : (fst n, snd n) ≅ n], the
 identity only because [prod] has no definitional eta. （已译） *)

Definition prod_cone_iso (N : Cone K) :
  ConeIso (prod_cone (FCone Fst N) (FCone Snd N)) N.
Proof.
  unshelve refine ((_; _)).
  - unshelve refine (@Build_Isomorphism (C ∏ D)
        (vertex_obj[prod_cone (FCone Fst N) (FCone Snd N)]) (vertex_obj[N])
        (id, id) (id, id) _ _).
    + split; simpl; apply id_left.
    + split; simpl; apply id_left.
  - intro x; split; simpl; apply id_right.
Defined.

Definition prod_reflect (N : Cone K)
  (H1 : IsLimitCone (FCone Fst N)) (H2 : IsLimitCone (FCone Snd N)) :
  IsLimitCone N :=
  limitcone_transport (prod_cone_iso N) (prod_IsLimitCone H1 H2).

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)

Definition ProdFactor (b : bool) : Category := if b then C else D.

Definition ProdProj (b : bool) : C ∏ D ⟶ ProdFactor b :=
  match b as b0 return C ∏ D ⟶ ProdFactor b0 with
  | true  => Fst
  | false => Snd
  end.

Definition Product_JointlyCreateLimit : JointlyCreateLimit K ProdProj.
Proof.
  unshelve refine
    {| jcreates_lift := fun N HN => prod_cone (N true) (N false) |}.
  - intros N HN b.
    destruct b.
    + exact (prod_cone_fst_iso (N true) (N false)).
    + exact (prod_cone_snd_iso (N true) (N false)).
  - intros M H.
    exact (prod_reflect M (H true) (H false)).
Defined.

(* 相关说明。 （已译） *)

Definition Product_Limit (L1 : Limit (Fst ◯ K)) (L2 : Limit (Snd ◯ K)) :
  Limit K :=
  limitcone_limit _ (prod_IsLimitCone (limit_limitcone L1) (limit_limitcone L2)).

Example Product_Limit_apex (L1 : Limit (Fst ◯ K)) (L2 : Limit (Snd ◯ K)) :
  vertex_obj[Product_Limit L1 L2] = (vertex_obj[L1], vertex_obj[L2])
  := eq_refl.

End ProductCones.

(* * ** Mac Lane §V.2 Exercise 2: product complete 范畴 is
 complete, dually （已译） *)

Definition Product_Complete {C D : Category}
  (HC : @Complete C) (HD : @Complete D) : @Complete (C ∏ D) :=
  fun J K => Product_Limit K (HC J (Fst ◯ K)) (HD J (Snd ◯ K)).

(* 相关说明。 （已译） *)

Definition Complete_op_of_Cocomplete {E : Category} (H : @Cocomplete E) :
  @Complete (E^op) :=
  fun J G => H (Opposite J) (Opposite_Functor G).

(* 相关说明。 （已译） *)

Definition Product_Cocomplete {C D : Category}
  (HC : @Cocomplete C) (HD : @Cocomplete D) : @Cocomplete (C ∏ D) :=
  fun J K =>
    @Product_Complete (Opposite C) (Opposite D)
      (Complete_op_of_Cocomplete HC) (Complete_op_of_Cocomplete HD)
      (Opposite J) (Opposite_Functor K).

(* 相关说明。 （已译） *)

Section ProductOnlyIf.

Context {C D : Category}.

(* The diagram [C ∏ D] whose [C]-component [G] whose
 [D]-component 常值 at [d]. （已译） *)

Definition pair_const (d : D) {J : Category} (G : J ⟶ C) : J ⟶ C ∏ D.
Proof.
  unshelve refine
    (@Build_Functor J (C ∏ D) (fun x => (G x, d))
       (fun _ _ f => (fmap[G] f, id)) _ _ _).
  - repeat intro; split; simpl; [ now apply fmap_respects | reflexivity ].
  - intro x; split; simpl; [ apply fmap_id | reflexivity ].
  - intros x y z f g; split; simpl;
      [ apply fmap_comp | symmetry; apply id_left ].
Defined.

Definition const_pair (c : C) {J : Category} (G : J ⟶ D) : J ⟶ C ∏ D.
Proof.
  unshelve refine
    (@Build_Functor J (C ∏ D) (fun x => (c, G x))
       (fun _ _ f => (id, fmap[G] f)) _ _ _).
  - repeat intro; split; simpl; [ reflexivity | now apply fmap_respects ].
  - intro x; split; simpl; [ reflexivity | apply fmap_id ].
  - intros x y z f g; split; simpl;
      [ symmetry; apply id_left | apply fmap_comp ].
Defined.

Example pair_const_obj (d : D) {J : Category} (G : J ⟶ C) (x : J) :
  fobj[pair_const d G] x = (G x, d) := eq_refl.

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition repack_fst {d : D} {J : Category} {G : J ⟶ C}
  (N : Cone (Fst ◯ pair_const d G)) : Cone G :=
  @Build_Cone J C G (vertex_obj[N])
    (@Build_ACone J C (vertex_obj[N]) G (fun x => cone_leg N x)
       (fun x y f => cone_leg_coh N f)).

Definition repack_fst_inv {d : D} {J : Category} {G : J ⟶ C}
  (M : Cone G) : Cone (Fst ◯ pair_const d G) :=
  @Build_Cone J C (Fst ◯ pair_const d G) (vertex_obj[M])
    (@Build_ACone J C (vertex_obj[M]) (Fst ◯ pair_const d G)
       (fun x => cone_leg M x) (fun x y f => cone_leg_coh M f)).

Definition Product_Limit_Fst (d : D) {J : Category} (G : J ⟶ C)
  (L : Limit (pair_const d G)) : Limit G :=
  limitcone_limit (repack_fst (FCone Fst (@limit_cone _ _ _ L)))
    (fun M => Fst_PreservesLimitCone (pair_const d G)
                (@limit_cone _ _ _ L) (limit_limitcone L) (repack_fst_inv M)).

Definition repack_snd {c : C} {J : Category} {G : J ⟶ D}
  (N : Cone (Snd ◯ const_pair c G)) : Cone G :=
  @Build_Cone J D G (vertex_obj[N])
    (@Build_ACone J D (vertex_obj[N]) G (fun x => cone_leg N x)
       (fun x y f => cone_leg_coh N f)).

Definition repack_snd_inv {c : C} {J : Category} {G : J ⟶ D}
  (M : Cone G) : Cone (Snd ◯ const_pair c G) :=
  @Build_Cone J D (Snd ◯ const_pair c G) (vertex_obj[M])
    (@Build_ACone J D (vertex_obj[M]) (Snd ◯ const_pair c G)
       (fun x => cone_leg M x) (fun x y f => cone_leg_coh M f)).

Definition Product_Limit_Snd (c : C) {J : Category} (G : J ⟶ D)
  (L : Limit (const_pair c G)) : Limit G :=
  limitcone_limit (repack_snd (FCone Snd (@limit_cone _ _ _ L)))
    (fun M => Snd_PreservesLimitCone (const_pair c G)
                (@limit_cone _ _ _ L) (limit_limitcone L) (repack_snd_inv M)).

Definition Product_Complete_Fst (H : @Complete (C ∏ D)) (d : D) :
  @Complete C :=
  fun J G => Product_Limit_Fst d G (H J (pair_const d G)).

Definition Product_Complete_Snd (H : @Complete (C ∏ D)) (c : C) :
  @Complete D :=
  fun J G => Product_Limit_Snd c G (H J (const_pair c G)).

(* 相关说明。 （已译） *)

Example Product_Limit_Fst_apex (d : D) {J : Category} (G : J ⟶ C)
  (L : Limit (pair_const d G)) :
  vertex_obj[Product_Limit_Fst d G L] = fst (vertex_obj[L]) := eq_refl.

End ProductOnlyIf.

(* * ** Componentwise terminal initial 对象, coproducts （已译） *)

Section ProductTerminal.

Context {C D : Category}.

#[export]
Program Instance Product_Terminal `{@Terminal C} `{@Terminal D} :
  @Terminal (C ∏ D) := {
  terminal_obj := (1, 1);
  one := fun _ => (one, one)
}.
Next Obligation. split; apply one_unique. Qed.

Example Product_Terminal_obj `{@Terminal C} `{@Terminal D} :
  @terminal_obj (C ∏ D) Product_Terminal = (@terminal_obj C _, @terminal_obj D _)
  := eq_refl.

End ProductTerminal.

(* The duals primal instances at opposite 范畴, through
 conversion [Product_Opposite]; not registered resolution. （已译） *)

Definition Product_Initial {C D : Category}
  (HC : @Initial C) (HD : @Initial D) : @Initial (C ∏ D) :=
  @Product_Terminal (C^op) (D^op) HC HD.

Definition Product_Cocartesian {C D : Category}
  (HC : @Cocartesian C) (HD : @Cocartesian D) : @Cocartesian (C ∏ D) :=
  @Product_Cartesian (C^op) (D^op) HC HD.

Example Product_Initial_obj {C D : Category}
  (HC : @Initial C) (HD : @Initial D) :
  @initial_obj (C ∏ D) (Product_Initial HC HD)
    = (@initial_obj C HC, @initial_obj D HD)
  := eq_refl.

Example Product_Cocartesian_obj {C D : Category}
  (HC : @Cocartesian C) (HD : @Cocartesian D) (x y : C ∏ D) :
  @Coprod (C ∏ D) (Product_Cocartesian HC HD) x y
    = (@Coprod C HC (fst x) (fst y), @Coprod D HD (snd x) (snd y))
  := eq_refl.

(* 相关说明。 （已译） *)

Section PiCatCones.

Context {I : Type} {D : I → Category} {J : Category}.
Context (K : J ⟶ PiCat D).

Definition pi_cone (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K)) : Cone K.
Proof.
  unshelve refine
    (@Build_Cone J (PiCat D) K (fun i => vertex_obj[N i])
       (@Build_ACone J (PiCat D) (fun i => vertex_obj[N i]) K
          (fun x i => cone_leg (N i) x) _)).
  intros x y f i.
  exact (cone_leg_coh (N i) f).
Defined.

Example pi_cone_apex (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K)) :
  vertex_obj[pi_cone N] = fun i => vertex_obj[N i] := eq_refl.

Example pi_cone_proj_leg (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K))
  (i : I) (x : J) :
  cone_leg (FCone (PiCat_Proj D i) (pi_cone N)) x = cone_leg (N i) x
  := eq_refl.

Definition pi_cone_proj_iso (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K)) (i : I) :
  ConeIso (FCone (PiCat_Proj D i) (pi_cone N)) (N i).
Proof.
  exists iso_id.
  intro x; simpl; now rewrite id_right.
Defined.

Definition pi_IsLimitCone (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K))
  (HN : ∀ i : I, IsLimitCone (N i)) : IsLimitCone (pi_cone N).
Proof.
  intro M.
  unshelve refine
    {| unique_obj := fun i => unique_obj (HN i (FCone (PiCat_Proj D i) M)) |}.
  - intros x i.
    exact (unique_property (HN i (FCone (PiCat_Proj D i) M)) x).
  - intros v Hv i.
    apply (uniqueness (HN i (FCone (PiCat_Proj D i) M))).
    intro x; exact (Hv x i).
Defined.

Example pi_IsLimitCone_med (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K))
  (HN : ∀ i : I, IsLimitCone (N i)) (M : Cone K) :
  unique_obj (pi_IsLimitCone N HN M)
    = fun i => unique_obj (HN i (FCone (PiCat_Proj D i) M))
  := eq_refl.

(* Here apex 同构 IS [iso_id]: function has definitional eta
 where pair does not, so two apexes same 对象. （已译） *)

Definition pi_cone_iso (N : Cone K) :
  ConeIso (pi_cone (fun i => FCone (PiCat_Proj D i) N)) N.
Proof.
  exists iso_id.
  intros x i; simpl; apply id_right.
Defined.

Definition pi_reflect (N : Cone K)
  (H : ∀ i : I, IsLimitCone (FCone (PiCat_Proj D i) N)) : IsLimitCone N :=
  limitcone_transport (pi_cone_iso N)
    (pi_IsLimitCone (fun i => FCone (PiCat_Proj D i) N) H).

Definition PiCat_JointlyCreateLimit : JointlyCreateLimit K (PiCat_Proj D).
Proof.
  unshelve refine {| jcreates_lift := fun N HN => pi_cone N |}.
  - intros N HN i; exact (pi_cone_proj_iso N i).
  - exact pi_reflect.
Defined.

Definition PiCat_Limit (L : ∀ i : I, Limit (PiCat_Proj D i ◯ K)) : Limit K :=
  limitcone_limit _
    (pi_IsLimitCone (fun i => @limit_cone _ _ _ (L i))
       (fun i => limit_limitcone (L i))).

Example PiCat_Limit_apex (L : ∀ i : I, Limit (PiCat_Proj D i ◯ K)) :
  vertex_obj[PiCat_Limit L] = fun i => vertex_obj[L i] := eq_refl.

End PiCatCones.

Definition PiCat_Complete {I : Type} {D : I → Category}
  (HD : ∀ i : I, @Complete (D i)) : @Complete (PiCat D) :=
  fun J K => PiCat_Limit K (fun i => HD i J (PiCat_Proj D i ◯ K)).
