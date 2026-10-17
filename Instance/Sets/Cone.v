Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Diagram.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.Karoubi.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.Diagonal.Limit.

Generalizable All Variables.
#[local] Obligation Tactic := idtac.

(** * Mac Lane's cone-set limit: the comparison, the remark, the cases *)

(*
   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The comparison with the compatible-family limit *)

Section Compare.

Context {D : Category}.
Context (F : D ⟶ Sets).

(* Both apexes are limits of [F], so [limit_unique_iso] supplies the
   comparison and both leg families with no new proof content. *)
Definition cone_apex_iso : Sets_limit_obj F ≅[Sets] cone_apex F :=
  limit_unique_iso (limit_is_alimit (Sets_Limit F)) (cone_set_IsALimit F).

Definition cone_apex_iso_legs :
  (∀ x : D, limit_leg (cone_set_IsALimit F) x ∘ to cone_apex_iso
              ≈ limit_leg (limit_is_alimit (Sets_Limit F)) x) *
  (∀ x : D, limit_leg (limit_is_alimit (Sets_Limit F)) x
              ∘ from cone_apex_iso ≈ limit_leg (cone_set_IsALimit F) x) :=
  limit_unique_iso_legs (limit_is_alimit (Sets_Limit F))
                        (cone_set_IsALimit F).

(* The two leg families are the named ones, on the nose. *)
Example cone_apex_iso_leg_cone :
  limit_leg (cone_set_IsALimit F) = cone_leg_at F := eq_refl.

Example cone_apex_iso_leg_family :
  limit_leg (limit_is_alimit (Sets_Limit F)) = Sets_limit_leg F := eq_refl.

(*
   本节说明（余）极限、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example cone_apex_iso_to_is_med :
  to cone_apex_iso
  = cone_set_med F (alimit_cone (limit_is_alimit (Sets_Limit F)))
  := eq_refl.

End Compare.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition cone_apex_discrete_iprod_iso {A : Set} (f : A -> obj[Sets]) :
  cone_apex (DiscreteCat_Functor f) ≅[Sets] Sets_iprod_obj f :=
  iso_compose (discrete_iprod_iso f)
              (iso_sym (cone_apex_iso (DiscreteCat_Functor f))).

(** ** The remark: display (3), natural in the apex *)

Section Remark.

Context {D : Category}.
Context (F : D ⟶ Sets).

(* Mac Lane's [tau |--> h]: a cone with apex X becomes a map into the cone
   set, sending [e] to the cone [tau e]. *)
Program Definition cone_transpose (X : obj[Sets]) :
  fobj[ConePresheaf F] X
    ~{Sets}~> fobj[Curried_CoHom Sets (cone_apex F)] X := {|
  morphism := fun p =>
    {| morphism := fun e =>
         {| vertex_map := fun d => {| morphism := fun _ =>
              @vertex_map _ _ _ _ p d e |} |} |}
|}.
Next Obligation. intros X p e d u v Huv; reflexivity. Qed.
Next Obligation.
  intros X p e x y f u; exact (@cone_coherence _ _ _ _ p x y f e).
Qed.
Next Obligation.
  intros X p e e' Hee' d u.
  exact (proper_morphism (@vertex_map _ _ _ _ p d) e e' Hee').
Qed.
Next Obligation. intros X p q Hpq e d u; exact (Hpq d e). Qed.

(* The inverse: reindex the tautological cone along h, i.e. compose each
   leg of display (2) with h. *)
Program Definition cone_untranspose (X : obj[Sets]) :
  fobj[Curried_CoHom Sets (cone_apex F)] X
    ~{Sets}~> fobj[ConePresheaf F] X := {|
  morphism := fun h => {| vertex_map := fun d => cone_leg_at F d ∘ h |}
|}.
Next Obligation.
  intros X h x y f e; simpl.
  exact (@cone_coherence _ _ _ _ (h e) x y f ttt).
Qed.
Next Obligation. intros X h h' Hhh' d e; simpl; exact (Hhh' e d ttt). Qed.

(* One round trip is definitional pointwise; the other spends the
   singleton, exactly once, in the same [destruct] the mediator spends. *)
Lemma cone_transpose_round (X : obj[Sets]) (p : fobj[ConePresheaf F] X) :
  cone_untranspose X (cone_transpose X p) ≈ p.
Proof. intros d e; reflexivity. Qed.

Lemma cone_untranspose_round (X : obj[Sets])
  (h : fobj[Curried_CoHom Sets (cone_apex F)] X) :
  cone_transpose X (cone_untranspose X h) ≈ h.
Proof. intros e d u; destruct u; reflexivity. Qed.

(* Display (3) at a fixed apex. *)
Program Definition cone_hom_iso (X : obj[Sets]) :
  @Isomorphism Sets (fobj[ConePresheaf F] X)
                    (fobj[Curried_CoHom Sets (cone_apex F)] X) := {|
  to := cone_transpose X; from := cone_untranspose X
|}.
Next Obligation. intros X; exact (cone_untranspose_round X). Qed.
Next Obligation. intros X; exact (cone_transpose_round X). Qed.

(* The book's parenthetical "(natural)", proved.  Both directions. *)
Lemma cone_transpose_natural (X Y : obj[Sets]) (g : X ~{Sets^op}~> Y) :
  fmap[Curried_CoHom Sets (cone_apex F)] g ∘ cone_transpose X
    ≈ cone_transpose Y ∘ fmap[ConePresheaf F] g.
Proof. intros p e d u; reflexivity. Qed.

Lemma cone_untranspose_natural (X Y : obj[Sets]) (g : X ~{Sets^op}~> Y) :
  fmap[ConePresheaf F] g ∘ cone_untranspose X
    ≈ cone_untranspose Y ∘ fmap[Curried_CoHom Sets (cone_apex F)] g.
Proof. intros h d e; simpl; reflexivity. Qed.

(* Display (3) as an isomorphism of functors of the apex. *)
Program Definition ConeSet_Natural_Iso :
  @Isomorphism ([Sets^op, Sets])
               (ConePresheaf F) (Curried_CoHom Sets (cone_apex F)) := {|
  to   := {| transform := cone_transpose |};
  from := {| transform := cone_untranspose |}
|}.
Next Obligation. intros X Y g; exact (cone_transpose_natural X Y g). Qed.
Next Obligation. intros X Y g p e d u; reflexivity. Qed.
Next Obligation. intros X Y g; exact (cone_untranspose_natural X Y g). Qed.
Next Obligation. intros X Y g h e d; simpl; reflexivity. Qed.
Next Obligation. intros X h e d u; destruct u; reflexivity. Qed.
Next Obligation. intros X p d e; reflexivity. Qed.

(* The components are the two named maps, on the nose. *)
Example coneset_natural_iso_to (X : obj[Sets]) :
  transform[to ConeSet_Natural_Iso] X = cone_transpose X := eq_refl.

Example coneset_natural_iso_from (X : obj[Sets]) :
  transform[from ConeSet_Natural_Iso] X = cone_untranspose X := eq_refl.

(* The cone presheaf is representable, represented by the cone set. *)
Program Definition ConeSet_Representable : Representable (ConePresheaf F) := {|
  repr_obj := (cone_apex F : obj[Sets^op]);
  represented := {| to := _; from := _ |}
|}.
Next Obligation. exact (from ConeSet_Natural_Iso). Defined.
Next Obligation. exact (to ConeSet_Natural_Iso). Defined.
Next Obligation. exact (iso_from_to ConeSet_Natural_Iso). Qed.
Next Obligation. exact (iso_to_from ConeSet_Natural_Iso). Qed.

End Remark.

(** ** The adjunction reading of the remark *)

(* The cone-set construction as a choice of limits of a fixed shape. *)
Definition ConeSet_HasLimitsOfShape (J : Category) :
  HasLimitsOfShape J Sets := fun F => cone_set_Limit F.

(* #353's adjunction, fed the cone-set oracle.  Stated outside the section
   below so that [J] is an explicit argument, as it is for the oracle. *)
Definition ConeSet_Diagonal_Limit_Adjunction (J : Category) :
  @Diagonal Sets J ⊣ LimitFunctor (ConeSet_HasLimitsOfShape J) :=
  Diagonal_Limit_Adjunction (ConeSet_HasLimitsOfShape J).

Section Adjunction.

Context {J : Category}.
Context (F : J ⟶ Sets).

(* Four strict readbacks: the adjoint's value, its leg, its backward
   transposition, and its counit. *)
Example coneset_lim_obj :
  lim_obj (ConeSet_HasLimitsOfShape J) F = cone_apex F := eq_refl.

Example coneset_lim_leg (j : J) :
  lim_leg (ConeSet_HasLimitsOfShape J) F j = cone_leg_at F j := eq_refl.

Example coneset_adj_from_is_untranspose (X : obj[Sets])
  (h : X ~{Sets}~> cone_apex F) (j : J) :
  transform[from (@adj _ _ _ _ (ConeSet_Diagonal_Limit_Adjunction J) X F) h] j
  = @vertex_map _ _ _ _ (cone_untranspose F X h) j := eq_refl.

(*
   本节说明伴随、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example coneset_counit (j : J) :
  transform[lim_counit (ConeSet_HasLimitsOfShape J) F] j
  = cone_leg_at F j ∘ id := eq_refl.

(*
   本节说明 Cone 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma coneset_adj_to_is_transpose (X : obj[Sets]) (p : ACone X F) :
  to (@adj _ _ _ _ (ConeSet_Diagonal_Limit_Adjunction J) X F)
     (snd (Cone_Natural_Transform F X) p)
  ≈ cone_transpose F X p.
Proof. intros e d u; reflexivity. Qed.

End Adjunction.

(** ** Equalizers: Awodey's concrete presentation *)

Section Equalizers.

Context {X Y : SetoidObject}.
Context (f g : X ~{Sets}~> Y).

(* The existing [HasEqualizers Sets]' apex is the compatible-family setoid
   over the walking parallel pair, and its leg is evaluation at [ParX]. *)
Example existing_apex_is_limit_obj :
  projT1 (@equalizer Sets Sets_HasEqualizers X Y f g)
  = Sets_limit_obj (APair f g) := eq_refl.

Example existing_leg_is_limit_leg :
  projT1 (projT2 (@equalizer Sets Sets_HasEqualizers X Y f g))
  = Sets_limit_leg (APair f g) ParX := eq_refl.

(* Awodey's [{x ∈ A | f x = g x}], as a sub-setoid. *)
Program Definition sets_eq_obj : SetoidObject := {|
  carrier   := { a : X & f a ≈ g a };
  is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |}
|}.
Next Obligation. equivalence. Qed.

Program Definition sets_eq_incl : sets_eq_obj ~{Sets}~> X := {|
  morphism := fun p => `1 p
|}.
Next Obligation. intros p q Hpq; exact Hpq. Qed.

Program Definition sets_eq_desc {Z : SetoidObject} (h : Z ~{Sets}~> X)
  (Hh : f ∘ h ≈ g ∘ h) : Z ~{Sets}~> sets_eq_obj := {|
  morphism := fun z => (h z; Hh z)
|}.
Next Obligation. intros Z h Hh z z' Hz; simpl; now rewrite Hz. Qed.

(* "with unique factorization because the inclusion is monic". *)
Program Definition sets_IsEqualizer :
  IsEqualizer f g sets_eq_obj sets_eq_incl := {|
  fork_eq := _;
  eq_desc := fun Z h Hh => {| unique_obj := sets_eq_desc h Hh |}
|}.
Next Obligation. intros p; exact (`2 p). Qed.
Next Obligation. intros Z h Hh z; reflexivity. Qed.
Next Obligation. intros Z h Hh v Hv z; simpl; symmetry; exact (Hv z). Qed.

(* The existing instance, read as an elementary equalizer. *)
Definition existing_IsEqualizer :
  IsEqualizer f g (Sets_limit_obj (APair f g))
              (Sets_limit_leg (APair f g) ParX) :=
  projT2 (projT2 (@equalizer Sets Sets_HasEqualizers X Y f g)).

(* The gap between Awodey's presentation and the existing one is one
   application of [equalizer_unique].  The strict form is refused at
   CONVERSION and is pinned in the probe. *)
Definition concrete_vs_existing :
  @Isomorphism Sets sets_eq_obj (Sets_limit_obj (APair f g)) :=
  equalizer_unique f g sets_IsEqualizer existing_IsEqualizer.

End Equalizers.

(** ** Riehl's Karoubi instance *)

Section Karoubi.

Context {X : SetoidObject}.
Context (e : X ~{Sets}~> X).

(*
   本节说明等化子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition karoubi_med {Z : SetoidObject} (h : Z ~{Sets}~> X)
  (Hh : @id Sets X ∘ h ≈ e ∘ h) : Z ~{Sets}~> sets_split_obj e := {|
  morphism := fun z => (h z; _)
|}.
Next Obligation. intros Z h Hh z; simpl; symmetry; exact (Hh z). Qed.
Next Obligation. intros Z h Hh z z' Hz; simpl; now rewrite Hz. Qed.

Program Definition karoubi_IsEqualizer :
  IsEqualizer (@id Sets X) e (sets_split_obj e) (sets_split_s e) := {|
  fork_eq := _;
  eq_desc := fun Z h Hh => {| unique_obj := karoubi_med h Hh |}
|}.
Next Obligation. intros p; simpl; symmetry; exact (`2 p). Qed.
Next Obligation. intros Z h Hh z; reflexivity. Qed.
Next Obligation. intros Z h Hh v Hv z; simpl; symmetry; exact (Hv z). Qed.

End Karoubi.

(** ** Seven Sketches: the limit in coordinates *)

Section Tuple.

Context {G : Quiver}.
Context (D : Diagram G Sets).

(* Compatibility along the GENERATING EDGES -- the book's condition. *)
Definition tuple_compat (x : ∀ i : G, D i) : Type :=
  ∀ (i j : G) (e : edges i j), dedge D e (x i) ≈ x j.

(*
   本节说明 Cone 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma tuple_compat_paths (x : ∀ i : G, D i) (H : tuple_compat x)
  {i j : G} (p : tlist edges i j) : dpath D p (x i) ≈ x j.
Proof.
  induction p as [ | a b e p IH ]; simpl.
  - reflexivity.
  - rewrite <- IH; now rewrite (H _ _ e).
Qed.

(* What agrees on the nose. *)
Example tuple_fobj_strict (i : G) : fobj[FunctorOfDiagram D] i = D i
  := eq_refl.

Example tuple_inner_strict :
  Sets_iprod_obj (fun d : FreeOnQuiver G => fobj[FunctorOfDiagram D] d)
  = Sets_iprod_obj (fun i : G => D i) := eq_refl.

(* The book's set of tuples. *)
Program Definition tuple_obj : SetoidObject := {|
  carrier   := { x : Sets_iprod_obj (fun i : G => D i) & tuple_compat x };
  is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |}
|}.
Next Obligation.
  constructor.
  - intros p i; reflexivity.
  - intros p q Hpq i; symmetry; exact (Hpq i).
  - intros p q r Hpq Hqr i; transitivity (`1 q i);
    [exact (Hpq i)|exact (Hqr i)].
Qed.

(* Forward: restrict the path condition to single edges. *)
Program Definition tuple_fwd :
  Sets_limit_obj (FunctorOfDiagram D) ~{Sets}~> tuple_obj := {|
  morphism := fun p => (`1 p ; fun i j e => _)
|}.
Next Obligation. intros p i j e; exact (`2 p i j (tlist_singleton e)). Defined.
Next Obligation. intros p q Hpq i; exact (Hpq i). Qed.

(* Backward: extend along paths.  The natural [rewrite <- (dpath_fmap D f)]
   is stuck on an unresolved [ProperProxy]; the explicit [transitivity]
   through [dpath] is what goes through. *)
Program Definition tuple_bwd :
  tuple_obj ~{Sets}~> Sets_limit_obj (FunctorOfDiagram D) := {|
  morphism := fun p => (`1 p ; fun i j f => _)
|}.
Next Obligation.
  intros p i j f; simpl in f.
  transitivity (dpath D f (`1 p i)).
  - symmetry; exact (dpath_fmap D f (`1 p i)).
  - exact (tuple_compat_paths (`1 p) (`2 p) f).
Defined.
Next Obligation. intros p q Hpq i; exact (Hpq i). Qed.

(* Theorem 3.95: the limit IS the set of compatible tuples. *)
Program Definition tuple_iso :
  @Isomorphism Sets (Sets_limit_obj (FunctorOfDiagram D)) tuple_obj := {|
  to := tuple_fwd; from := tuple_bwd
|}.
Next Obligation. intros p i; reflexivity. Qed.
Next Obligation. intros p i; reflexivity. Qed.

(* "with the coordinate projections as the legs". *)
Program Definition tuple_proj (i : G) : tuple_obj ~{Sets}~> D i := {|
  morphism := fun p => `1 p i
|}.
Next Obligation. intros i p q Hpq; exact (Hpq i). Qed.

Lemma tuple_proj_is_leg (i : G) :
  tuple_proj i ∘ to tuple_iso ≈ Sets_limit_leg (FunctorOfDiagram D) i.
Proof. intros p; reflexivity. Qed.

Lemma tuple_proj_is_leg_inv (i : G) :
  Sets_limit_leg (FunctorOfDiagram D) i ∘ from tuple_iso ≈ tuple_proj i.
Proof. intros p; reflexivity. Qed.

End Tuple.

(** ** Seven Sketches: presentation-independence *)

Section Presentation.

Context (G : Quiver).
Context (R : PathRel G).
Context (S : PresentedQuiver G R ⟶ Sets).

(* The restriction of S along the quotient projection. *)
Definition Srestr : FreeOnQuiver G ⟶ Sets := S ◯ PresentedQuiverProj G R.

(* The imposed equations touch neither the objects nor the compatibility
   predicate nor the carrier -- only the hom-setoid, which the limit
   carrier does not read. *)
Example pres_fobj_strict (i : G) : fobj[S] i = fobj[Srestr] i := eq_refl.

Example pres_compat_strict
  (x : Sets_iprod_obj (fun d : PresentedQuiver G R => fobj[S] d)) :
  Sets_limit_compatible S x = Sets_limit_compatible Srestr x := eq_refl.

Example pres_carrier_strict :
  Sets_limit_carrier S = Sets_limit_carrier Srestr := eq_refl.

Program Definition pres_fwd :
  Sets_limit_obj S ~{Sets}~> Sets_limit_obj Srestr := {|
  morphism := fun p => p
|}.
Next Obligation. intros p q Hpq i; exact (Hpq i). Qed.

Program Definition pres_bwd :
  Sets_limit_obj Srestr ~{Sets}~> Sets_limit_obj S := {|
  morphism := fun p => p
|}.
Next Obligation. intros p q Hpq i; exact (Hpq i). Qed.

(* Both legs are the identity on elements.  The OBJECT-level [eq_refl] is
   nevertheless refused; see the header, and the probe. *)
Program Definition pres_iso :
  @Isomorphism Sets (Sets_limit_obj S) (Sets_limit_obj Srestr) := {|
  to := pres_fwd; from := pres_bwd
|}.
Next Obligation. intros p i; reflexivity. Qed.
Next Obligation. intros p i; reflexivity. Qed.

Lemma pres_iso_legs (i : G) :
  Sets_limit_leg Srestr i ∘ to pres_iso ≈ Sets_limit_leg S i.
Proof. intros p; reflexivity. Qed.

Lemma pres_iso_legs_inv (i : G) :
  Sets_limit_leg S i ∘ from pres_iso ≈ Sets_limit_leg Srestr i.
Proof. intros p; reflexivity. Qed.

End Presentation.
