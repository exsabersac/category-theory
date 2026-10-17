Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Elements.
Require Import Category.Construction.Elements.Kan.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** 每个取值于集合的函子典范地是 representable 的余极限。 *)

(* nLab: https://ncatlab.org/nlab/show/density+theorem
   nLab: https://ncatlab.org/nlab/show/co-Yoneda+lemma

   密度定理 / 余 Yoneda：每个函子（在适当设定下）是 representable 的（余）极限；
   余 Yoneda 把预层表示为 Yoneda 嵌入下元素范畴上的余极限。本文件形式化相关同构与组装。
   原英文文首极长（约 25KB）；本波次译为定义性导言，细节原文若仍残留于文件其它处，属后续波次。 *)

Section Density.

Context {D : Category}.
Context (K : D ⟶ Sets).

(** ** The index category and the diagram of representables *)

(*指数是 对要素范畴的OPOSITE:展开了。
d霄->ZWP. 页:1
56. ZWP1 但这必须让签约国实现婿的则是历史。*)

Definition ElementsOp : Category := (Elements K)^op.

(*Sung的某些方面。 ,,,,,,,, 继,,,,,,,,,,,,,,,,,,,,是吗,采取协调一致的。
与元素充分发挥的相反。 没有义务,合作和协调
迥促使*)

Definition DensityDiagram : ElementsOp ⟶ [D, Sets] :=
  Curried_Hom D ◯ (Elements_proj K)^op.

Example density_diagram_obj (d : D) (x : K d) :
  DensityDiagram ((d; x) : ElementsOp) = [Hom d,─] := eq_refl.

(** ** The Yoneda transformation at an element *)

(*
   For x an element of K d, the 变换 [Hom d,-] ==> K whose

   本节说明相关定义、性质与动机。 component at e carries g : d ~> e [fmap[K] g x]. Respectfulness is [elements_respects_cond] both naturality orientations are [fmap_comp] read at element.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition yo_component {d : D} (x : K d) (e : D) :
  @hom Sets ([Hom d,─] e) (K e) :=
  @Build_SetoidMorphism (d ~{D}~> e) _ (K e) _
    (fun g => fmap[K] g x)
    (fun u v H => elements_respects_cond K u v H).

Lemma yo_naturality {d : D} (x : K d) {e e' : D} (f : e ~> e') :
  fmap[K] f ∘ yo_component x e ≈ yo_component x e' ∘ fmap[[Hom d,─]] f.
Proof. intro g; symmetry; exact (@fmap_comp _ _ K _ _ _ f g x). Qed.

Lemma yo_naturality_sym {d : D} (x : K d) {e e' : D} (f : e ~> e') :
  yo_component x e' ∘ fmap[[Hom d,─]] f ≈ fmap[K] f ∘ yo_component x e.
Proof. intro g; exact (@fmap_comp _ _ K _ _ _ f g x). Qed.

Definition yo_inj {d : D} (x : K d) : [Hom d,─] ⟹ K :=
  @Build_Transform D Sets ([Hom d,─]) K
    (fun e => yo_component x e)
    (fun e e' f => yo_naturality x f)
    (fun e e' f => yo_naturality_sym x f).

(** ** The canonical cocone *)

Definition density_inj (j : ElementsOp) :
  @hom ([D, Sets]) (DensityDiagram j) K := yo_inj (`2 j).

Example density_inj_at (d : D) (x : K d) (e : D) (g : d ~> e) :
  transform[density_inj ((d; x) : ElementsOp)] e g = fmap[K] g x := eq_refl.

(*
   本节说明相关定义、性质与动机。 Cocone coherence. For f : x ~> y [Elements K] diagram sends f.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma density_cocone_coherence {x y : Elements K}
      (f : x ~{Elements K}~> y) :
  density_inj x ∘ @fmap _ _ DensityDiagram y x f ≈ density_inj y.
Proof.
  intros e g.
  exact (elements_comp_cond K g (`1 f) (`2 f) (reflexivity _)).
Qed.

Definition DensityCocone : Cocone DensityDiagram.
Proof.
  unshelve eapply Build_Cone.
  - exact K.
  - unshelve eapply Build_ACone.
    + exact (fun j => density_inj j).
    + intros x y f; exact (density_cocone_coherence f).
Defined.

Example density_cocone_apex : vertex_obj[DensityCocone] = K := eq_refl.

Example density_cocone_inj (j : ElementsOp) :
  cocone_inj DensityCocone j = density_inj j := eq_refl.

(** ** The mediating transformation out of K *)

Section Mediator.

Context (M : Cocone DensityDiagram).

(*
   本节说明相关定义、性质与动机。 Respectfulness ELEMENT argument, derived from cocone coherence. at [elements_same] not assumed. Two `≈`-equal elements over one 对象 D are DIFFERENT 对象 [Elements K] -- 对象 are compared Leibniz equality -- so their injections are priori unrelated;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma den_med_respects {e : D} (z w : K e) (H : z ≈ w) :
  transform[cocone_inj M ((e; z) : ElementsOp)] e id
    ≈ transform[cocone_inj M ((e; w) : ElementsOp)] e id.
Proof.
  pose proof (cocone_inj_coherence M (elements_same K z w H) e id) as Hc.
  simpl in Hc.
  rewrite <- Hc.
  apply proper_morphism.
  now rewrite id_left.
Qed.

(* Evaluation at the identity: z : K e goes to the value at [id[e]] of
   the competing injection at the object (e, z). *)

Definition den_med_component (e : D) :
  @hom Sets (K e) (vertex_obj[M] e) :=
  @Build_SetoidMorphism (K e) _ (vertex_obj[M] e) _
    (fun z => transform[cocone_inj M ((e; z) : ElementsOp)] e id)
    (fun z w H => den_med_respects z w H).

(* Naturality: one step of the competing injection's own naturality, then
   cocone coherence at the chosen lift [Elements_lift K z f], whose image
   under the projection is f itself definitionally. *)

Lemma den_med_naturality {e e' : D} (f : e ~> e') :
  fmap[vertex_obj[M]] f ∘ den_med_component e
    ≈ den_med_component e' ∘ fmap[K] f.
Proof.
  intro z; simpl.
  pose proof (naturality[cocone_inj M ((e; z) : ElementsOp)] e e' f id) as Hn.
  simpl in Hn.
  rewrite Hn.
  pose proof (cocone_inj_coherence M (Elements_lift K z f) e' id) as Hc.
  simpl in Hc.
  rewrite <- Hc.
  apply proper_morphism.
  now rewrite id_left, id_right.
Qed.

Lemma den_med_naturality_sym {e e' : D} (f : e ~> e') :
  den_med_component e' ∘ fmap[K] f
    ≈ fmap[vertex_obj[M]] f ∘ den_med_component e.
Proof. symmetry; apply den_med_naturality. Qed.

Definition den_med : K ~{[D, Sets]}~> vertex_obj[M] :=
  @Build_Transform D Sets K (vertex_obj[M])
    (fun e => den_med_component e)
    (fun e e' f => den_med_naturality f)
    (fun e e' f => den_med_naturality_sym f).

Lemma den_med_commutes (j : ElementsOp) :
  den_med ∘ density_inj j ≈ cocone_inj M j.
Proof.
  destruct j as [d x].
  intros e g; simpl.
  pose proof (cocone_inj_coherence M (Elements_lift K x g) e id) as Hc.
  simpl in Hc.
  rewrite <- Hc.
  apply proper_morphism.
  unfold op; now rewrite id_left.
Qed.

Lemma den_med_unique (v : K ~{[D, Sets]}~> vertex_obj[M]) :
  (∀ j : ElementsOp, v ∘ density_inj j ≈ cocone_inj M j) → den_med ≈ v.
Proof.
  intros Hv e z; simpl.
  rewrite <- (Hv ((e; z) : ElementsOp) e id).
  simpl.
  apply proper_morphism.
  apply elements_id_cond.
Qed.

End Mediator.

(** ** Mac Lane III.7 Theorem 1 *)

Definition density : IsColimitCocone DensityCocone.
Proof.
  intro M.
  unshelve refine {| unique_obj := den_med M |}.
  - exact (den_med_commutes M).
  - exact (den_med_unique M).
Defined.

(** ** Derived packagings and corollaries *)

Definition density_IsAColimit : IsAColimit DensityDiagram K :=
  colimitcocone_isacolimit density.

Definition DensityColimit : Colimit DensityDiagram :=
  limitcone_limit DensityCocone density.

Definition density_med (M : Cocone DensityDiagram) :
  K ~{[D, Sets]}~> vertex_obj[M] := unique_obj (density M).

Example density_med_is_den_med (M : Cocone DensityDiagram) :
  density_med M = den_med M := eq_refl.

Lemma density_med_commutes (M : Cocone DensityDiagram) (j : ElementsOp) :
  density_med M ∘ density_inj j ≈ cocone_inj M j.
Proof. exact (den_med_commutes M j). Qed.

Lemma density_med_uniq (M : Cocone DensityDiagram)
      (v : K ~{[D, Sets]}~> vertex_obj[M]) :
  (∀ j : ElementsOp, v ∘ density_inj j ≈ cocone_inj M j) →
  density_med M ≈ v.
Proof. exact (den_med_unique M v). Qed.

(* The elementary content: every element of K e is the value at [id[e]]
   of the injection at its own object of the index. *)

Lemma density_elements_covered {e : D} (z : K e) :
  transform[density_inj ((e; z) : ElementsOp)] e id ≈ z.
Proof. apply elements_id_cond. Qed.

(* The injections are jointly epic: K is generated by representables. *)

Lemma density_jointly_epic {G : [D, Sets]}
      (u v : K ~{[D, Sets]}~> G) :
  (∀ j : ElementsOp, u ∘ density_inj j ≈ v ∘ density_inj j) → u ≈ v.
Proof.
  intros H e z.
  transitivity (transform[u] e (fmap[K] id z)).
  - apply proper_morphism; symmetry; apply elements_id_cond.
  - rewrite (H ((e; z) : ElementsOp) e id).
    simpl; apply proper_morphism; apply elements_id_cond.
Qed.

End Density.

(** ** The presheaf dual (Mac Lane III.7, the dual remark; Awodey 8.6) *)

Section PresheafDensity.

Context {C : Category}.
Context (P : C^op ⟶ Sets).

(* The index needs no construction: [PElements P] is DEFINED as
   [(Elements P)^op], which is [ElementsOp P] on the nose. *)

Example presheaf_index : ElementsOp P = PElements P := eq_refl.

Definition PDensityDiagram : PElements P ⟶ [C^op, Sets] := DensityDiagram P.

(* The value at (c, x) is the CONTRAVARIANT representable, because
   [Curried_CoHom C] is by definition [Curried_Hom C^op]. *)

Example pdensity_diagram_obj (c : C) (x : P c) :
  PDensityDiagram ((c; x) : PElements P) = [Hom ─,c] := eq_refl.

Definition PDensityCocone : Cocone PDensityDiagram := DensityCocone P.

Definition presheaf_density : IsColimitCocone PDensityCocone := density P.

Example pdensity_inj (c : C) (x : P c) (e : C) (g : e ~{C}~> c) :
  transform[cocone_inj PDensityCocone ((c; x) : PElements P)] e g
    = fmap[P] g x := eq_refl.

(*
   The other evident description of the diagram agrees on 对象 AND on

   本节说明相关定义、性质与动机。 arrows, both [eq_refl]; two 函子 RECORDS do not (probe negative 1), because [PElements_proj] is [Program 定义] whose law fields are opaque obligations.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example pdd_via_proj_obj (c : C) (x : P c) :
  PDensityDiagram ((c; x) : PElements P)
    = (Curried_CoHom C ◯ PElements_proj P) ((c; x) : PElements P) := eq_refl.

Example pdd_via_proj_fmap (x y : PElements P) (f : x ~{PElements P}~> y) :
  @fmap _ _ PDensityDiagram x y f
    = @fmap _ _ (Curried_CoHom C ◯ PElements_proj P) x y f := eq_refl.

End PresheafDensity.

(** ** The connection to the coend form of co-Yoneda *)

(* These two [Require]s are for this section alone.  They are NOT the
   route by which the theorem above is proved; see the header. *)

Require Import Category.Instance.Sets.Coend.
Require Import Category.Theory.Coend.Yoneda.

Section CoendConnection.

Context {C : Category}.
Context (F : C ⟶ Sets).

(* The coend's cowedge leg IS the density cocone's injection, on the
   nose: both send (g, a) to [fmap[F] g a]. *)

Example coy_leg_is_density_inj (c x : C) (g : x ~{C}~> c) (a : F x) :
  coy_leg F c x (g, a)
    = transform[density_inj F ((x; a) : ElementsOp F)] c g := eq_refl.

(*
   本节说明相关定义、性质与动机。 The naturality-in-c upgrade LEGS. [Theory/Coend/Yoneda.v]. fixes c section variable;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem coy_leg_natural_in_apex (x : C) (a : F x) :
  { tau : [Hom x,─] ~{[C, Sets]}~> F
  & ∀ (c : C) (g : x ~{C}~> c), transform[tau] c g = coy_leg F c x (g, a) }.
Proof. exists (yo_inj F a); intros c g; reflexivity. Defined.

Example coy_leg_natural_witness (x : C) (a : F x) :
  `1 (coy_leg_natural_in_apex x a) = yo_inj F a := eq_refl.

(*
   本节说明相关定义、性质与动机。 The coend's inverse map is "insert at identity", running it. back through mediator gives density injection at (c, b) applied [id] -- left-hand side [density_elements_covered].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example coy_from_at (c : C) (b : F c) :
  coy_from F c b = ci (YoI F c) c (id, b) := eq_refl.

Example coy_to_from_is_covering (c : C) (b : F c) :
  coy_to F c (coy_from F c b)
    = transform[density_inj F ((c; b) : ElementsOp F)] c id := eq_refl.

End CoendConnection.

(** ** Non-vacuity *)

Require Import Category.Instance.One.
Require Import Category.Functor.Diagonal.

Section Witness.

(* The two-element setoid, and the constant functor at it over the
   terminal category.  Over 1 the representables are singleton-valued,
   so this K is provably not one of them. *)

Definition DensityBool : Sets :=
  {| carrier := bool ; is_setoid := eq_Setoid bool |}.

Definition KBool : 1 ⟶ Sets := Diagonal _1 DensityBool.

Example kbool_obj : KBool ttt = DensityBool := eq_refl.

Definition et : ElementsOp KBool := (ttt; true).
Definition ef : ElementsOp KBool := (ttt; false).

(*
   The diagram is CONSTANT at the one 可表, and there are no

   本节说明相关定义、性质与动机。 态射 between two elements, so theorem here says that two-element set is 余积 two copies singleton.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example kbool_diagram_constant :
  DensityDiagram KBool et = DensityDiagram KBool ef := eq_refl.

Lemma kbool_injections_differ :
  density_inj KBool et ≈ density_inj KBool ef → False.
Proof. intro H; pose proof (H ttt ttt) as Hb; discriminate. Qed.

Lemma kbool_objects_differ : et = ef → False.
Proof.
  intro H.
  pose proof (f_equal (fun j : ElementsOp KBool => (`2 j : bool)) H) as Hb.
  discriminate.
Qed.

(*
   The two elements are not merely DISTINCT 对象 of the index: there

   本节说明相关定义、性质与动机。 is no 态射 between them either, covariant [Elements] reading. This is what makes "2 = 1 + 1" description above honest rather than decorative, audit found it asserted prose pinned nowhere, so it is lemma now. A 态射 (ttt;true) ~> (ttt;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma kbool_no_hom_et_ef :
  ((ttt; true) ~{Elements KBool}~> (ttt; false)) → False.
Proof. intros [f Hf]; simpl in Hf; discriminate. Qed.

(* The apex is not a representable: [Hom ttt,-] is singleton-valued over
   1, so an isomorphism would collapse [true] onto [false]. *)

Lemma kbool_not_representable :
  KBool ≅[[1, Sets]] @Curried_Hom _1 ttt → False.
Proof.
  intro i.
  assert (Ht := iso_from_to i ttt true).
  assert (Hf := iso_from_to i ttt false).
  simpl in Ht, Hf.
  destruct (transform[to i] ttt true).
  destruct (transform[to i] ttt false).
  rewrite Ht in Hf.
  discriminate.
Qed.

(* A competing cocone with the same apex but injections twisted by
   [negb].  The mediator it produces computes. *)

Definition neg_inj (j : ElementsOp KBool) :
  @hom ([1, Sets]) (DensityDiagram KBool j) KBool :=
  yo_inj KBool (negb (`2 j)).

Lemma neg_cocone_coherence {x y : Elements KBool}
      (f : x ~{Elements KBool}~> y) :
  neg_inj x ∘ @fmap _ _ (DensityDiagram KBool) y x f ≈ neg_inj y.
Proof.
  destruct f as [f0 Hf].
  intros e g; simpl in *.
  now rewrite Hf.
Qed.

Definition NegCocone : Cocone (DensityDiagram KBool).
Proof.
  unshelve eapply Build_Cone.
  - exact KBool.
  - unshelve eapply Build_ACone.
    + exact (fun j => neg_inj j).
    + intros x y f; exact (neg_cocone_coherence f).
Defined.

Example neg_med_true :
  transform[density_med KBool NegCocone] ttt true = false := eq_refl.

Example neg_med_false :
  transform[density_med KBool NegCocone] ttt false = true := eq_refl.

Lemma neg_med_not_id :
  density_med KBool NegCocone ≈ nat_id → False.
Proof. intro H; pose proof (H ttt true) as Hb; discriminate. Qed.

End Witness.

(** ** Probe: negatives of three kinds, with positive controls *)

(*
   本节说明相关定义、性质与动机。 Each [Fail] below was stripped once its error read off, so its. KIND is known it is not vacuously green.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ProbeConversion.

Context {C : Category}.
Context (P : C^op ⟶ Sets).

(* Controls: the two functors agree on objects and on arrows. *)

Definition ctrl_pdd_obj (c : C) (x : P c) :
  PDensityDiagram P ((c; x) : PElements P)
    = (Curried_CoHom C ◯ PElements_proj P) ((c; x) : PElements P)
  := pdd_via_proj_obj P c x.

Definition ctrl_pdd_fmap (x y : PElements P) (f : x ~{PElements P}~> y) :
  @fmap _ _ (PDensityDiagram P) x y f
    = @fmap _ _ (Curried_CoHom C ◯ PElements_proj P) x y f
  := pdd_via_proj_fmap P x y f.

(* NEGATIVE 1 (CONVERSION).  Stripped, this reports
   [cannot unify "PDensityDiagram P" and
   "Curried_CoHom C ◯ PElements_proj P"].  The two records differ only
   in their functor-law fields, which [PElements_proj] supplies as
   opaque [Program] obligations. *)

Fail Example neg_pdd_records :
  PDensityDiagram P = Curried_CoHom C ◯ PElements_proj P := eq_refl.

End ProbeConversion.

Section ProbeMediator.

Context {D : Category}.
Context (K : D ⟶ Sets).

(* Controls. *)

Example ctrl_diag_def :
  DensityDiagram K = Curried_Hom D ◯ (Elements_proj K)^op := eq_refl.

Definition ctrl_med_commutes (M : Cocone (DensityDiagram K))
  (j : ElementsOp K) :
  density_med K M ∘ density_inj K j ≈ cocone_inj M j
  := density_med_commutes K M j.

(*
   本节说明相关定义、性质与动机。 NEGATIVE 2 (CONVERSION). Stripped, this reports. [cannot unify "density_med K M ∘ density_inj K j" "cocone_inj M j"].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Example neg_med_commutes_strict (M : Cocone (DensityDiagram K))
  (j : ElementsOp K) :
  density_med K M ∘ density_inj K j = cocone_inj M j := eq_refl.

(* Control for negative 3: the composite is formable with the OPPOSITE of
   the projection. *)

Check (Curried_Hom D ◯ (Elements_proj K)^op).

(*
   本节说明相关定义、性质与动机。 NEGATIVE 3 (TYPING). Stripped, this reports. ["Elements_proj K" has type "Elements K ⟶ D" while it is expected have type "Elements K ⟶ D^op" (cannot unify "D" "(D^op)")].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (Curried_Hom D ◯ Elements_proj K).

End ProbeMediator.

Section ProbeUniverse.

Universe uo uh us.
Constraint uh < uo.
Constraint uh < us.

(* Controls: at a category whose OBJECTS sit strictly ABOVE its homs,
   both the index category and the Yoneda transformation are formable,
   and [DensityDiagram] itself is nameable. *)

Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) => ElementsOp K).
Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) => @yo_inj D K).
Check @DensityDiagram.

(*
   本节说明相关定义、性质与动机。 NEGATIVE 4 (FORMABILITY). Stripped, this reports universe. inconsistency naming declared levels: [Cannot enforce uh = _ because uh < uo <= _].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fail Check (fun (D : Category@{uo uh uh}) (K : D ⟶ Sets@{uh us}) =>
              DensityDiagram K).

End ProbeUniverse.

(* Instrument check: [Fail] does report an error when its command
   SUCCEEDS, so the four negatives above are genuine failures and not an
   inert tactic. *)

Fail Fail Check density.
