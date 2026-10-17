(* 相关说明。 （已译） *)

Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Thin.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Matr.GL.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Order.
Require Import Category.Instance.Grp.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

(*
 Book:      Awodey, "Category Theory", 2nd ed., §7.1, printed p. 153 —
 nLab:      https://ncatlab.org/nlab/show/representation
 nLab:      https://ncatlab.org/nlab/show/group+representation
 Wikipedia: https://en.wikipedia.org/wiki/Group_representation

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** From group 对象 幺半群 对象 （已译） *)

(*
   本节说明 Rep 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition grp_mon (G : GrpObject) : MonObject := {|
  mon_setoid := grp_setoid G;
  mon_unit   := grp_unit G;
  mon_op     := grp_mul G;

  mon_op_respects := grp_mul_respects G
|}.
Next Obligation.
  intros G a b c; symmetry; apply grp_mul_assoc.
Qed.
Next Obligation.
  intros G a; apply grp_mul_unit_l.
Qed.
Next Obligation.
  intros G a; apply grp_mul_unit_r.
Qed.

(* 相关说明。 （已译） *)
Example grp_mon_carrier (G : GrpObject) :
  carrier (grp_mon G) = carrier (grp_setoid G) := eq_refl.

Example grp_mon_unit (G : GrpObject) :
  @mon_unit (grp_mon G) = grp_unit G := eq_refl.

Example grp_mon_op (G : GrpObject) :
  @mon_op (grp_mon G) = grp_mul G := eq_refl.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma units_equiv {M : MonObject}
  {PM : PropEquiv (is_setoid (mon_setoid M))}
  (x y : carrier (grp_setoid (UnitsOf M PM))) : `1 x ≈ `1 y → x ≈ y.
Proof. intro H; exact H. Qed.

(*
   本节说明hom、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition rmod_hom_monoid_prop (K : RingObject) (V : RModObject K) :
  PropEquiv (is_setoid (mon_setoid (hom_monoid (RMod K) V))) :=
  @locally_prop (RMod K) (RMod_LocallyPropositional K) V V.

(** ** Representations *)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Record RepObject (K : RingObject) (G : GrpObject) := {
  rep_mod :> RModObject K;

  rep_hom : GrpHom G (UnitsOf (hom_monoid (RMod K) rep_mod) (rmod_hom_monoid_prop K rep_mod))
}.

Arguments rep_mod {K G} _.
Arguments rep_hom {K G} _.

(*
   本节说明 Rep 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition rep_act {K : RingObject} {G : GrpObject} (V : RepObject K G)
  (g : carrier G) : rep_mod V ~{RMod K}~> rep_mod V :=
  `1 (grp_map (rep_hom V) g).

Lemma rep_act_respects {K : RingObject} {G : GrpObject}
  (V : RepObject K G) : Proper (equiv ==> equiv) (rep_act V).
Proof.
  intros g h Hgh.
  exact (proper_morphism (grp_map (rep_hom V)) g h Hgh).
Qed.

Lemma rep_act_unit {K : RingObject} {G : GrpObject} (V : RepObject K G) :
  rep_act V (grp_unit G) ≈ id.
Proof. exact (grp_map_unit (rep_hom V)). Qed.

Lemma rep_act_mul {K : RingObject} {G : GrpObject} (V : RepObject K G)
  (g h : carrier G) :
  rep_act V (grp_mul G g h) ≈ rep_act V g ∘ rep_act V h.
Proof. exact (grp_map_mul (rep_hom V) g h). Qed.

(*
   本节说明 Rep 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition rep_act_iso {K : RingObject} {G : GrpObject}
  (V : RepObject K G) (g : carrier G) :
  rep_mod V ≅[RMod K] rep_mod V := {|
  to   := rep_act V g;
  from := rep_act V (grp_inv G g)
|}.
Next Obligation.
  intros K G V g.
  transitivity (rep_act V (grp_unit G)).
  - rewrite <- rep_act_mul.
    apply rep_act_respects.
    apply grp_mul_inv_r.
  - apply rep_act_unit.
Qed.
Next Obligation.
  intros K G V g.
  transitivity (rep_act V (grp_unit G)).
  - rewrite <- rep_act_mul.
    apply rep_act_respects.
    apply grp_mul_inv_l.
  - apply rep_act_unit.
Qed.

(* 相关说明。 （已译） *)

(* Forgetting invertibility witness: working form [Deloop]
 spine 所消耗. Its [mon_map] IS [rep_act]. （已译） *)
Program Definition monhom_of_rep {K : RingObject} {G : GrpObject}
  (V : RepObject K G) :
  MonHom (grp_mon G) (hom_monoid (RMod K) (rep_mod V)) := {|
  mon_map := rep_act V
|}.
Next Obligation. intros K G V; exact (rep_act_respects V). Qed.
Next Obligation. intros K G V; exact (rep_act_unit V). Qed.
Next Obligation. intros K G V a b; exact (rep_act_mul V a b). Qed.

(*
   本节说明 Rep 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition rep_of_monhom {K : RingObject} {G : GrpObject}
  (V : RModObject K) (h : MonHom (grp_mon G) (hom_monoid (RMod K) V)) :
  GrpHom G (UnitsOf (hom_monoid (RMod K) V) (rmod_hom_monoid_prop K V)) := {|
  grp_map := {| morphism := fun g : carrier G =>
    (mon_map h g; (mon_map h (grp_inv G g); (_, _))) |}
|}.
Next Obligation.
  intros K G V h g.
  transitivity (mon_map h (grp_unit G)).
  - rewrite <- (mon_map_op h g (grp_inv G g)).
    apply (mon_map_respects h).
    apply grp_mul_inv_r.
  - apply (mon_map_unit h).
Qed.
Next Obligation.
  intros K G V h g.
  transitivity (mon_map h (grp_unit G)).
  - rewrite <- (mon_map_op h (grp_inv G g) g).
    apply (mon_map_respects h).
    apply grp_mul_inv_l.
  - apply (mon_map_unit h).
Qed.
Next Obligation.
  intros K G V h g g' Hgg'.
  exact (mon_map_respects h g g' Hgg').
Qed.
Next Obligation.
  intros K G V h; exact (mon_map_unit h).
Qed.
Next Obligation.
  intros K G V h a b; exact (mon_map_op h a b).
Qed.

(* The packaged representation. *)
Definition RepOfMonHom {K : RingObject} {G : GrpObject}
  (V : RModObject K) (h : MonHom (grp_mon G) (hom_monoid (RMod K) V)) :
  RepObject K G :=
  {| rep_mod := V; rep_hom := rep_of_monhom V h |}.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma monhom_rep_round {K : RingObject} {G : GrpObject}
  (V : RModObject K) (h : MonHom (grp_mon G) (hom_monoid (RMod K) V))
  (g : carrier G) :
  mon_map (monhom_of_rep (RepOfMonHom V h)) g ≈ mon_map h g.
Proof. reflexivity. Qed.

Lemma rep_monhom_round {K : RingObject} {G : GrpObject}
  (V : RepObject K G) (g : carrier G) :
  rep_act (RepOfMonHom (rep_mod V) (monhom_of_rep V)) g ≈ rep_act V g.
Proof. reflexivity. Qed.

(*
   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma rep_monhom_round_elt {K : RingObject} {G : GrpObject}
  (V : RepObject K G) (g : carrier G) :
  `1 (grp_map (rep_of_monhom (rep_mod V) (monhom_of_rep V)) g)
    ≈ `1 (grp_map (rep_hom V) g).
Proof. reflexivity. Qed.

(** ** Intertwiners *)

(* A 态射 representations: module map commuting two
 actions. The 复合 spelled at [RMod K], actions being
 endomorphisms underlying modules. （已译） *)
Record Intertwiner {K : RingObject} {G : GrpObject}
       (V W : RepObject K G) := {
  itw_map :> rep_mod V ~{RMod K}~> rep_mod W;

  itw_equivar : ∀ g : carrier G,
    itw_map ∘ rep_act V g ≈ rep_act W g ∘ itw_map
}.

Arguments itw_map {K G V W} _.
Arguments itw_equivar {K G V W} _ _.

(* * ** The 范畴 representations （已译） *)

Program Definition Rep (K : RingObject) (G : GrpObject) : Category := {|
  obj := RepObject K G;
  hom := fun V W => Intertwiner V W;
  homset := fun V W =>
    {| equiv := fun f g => itw_map f ≈ itw_map g |};
  id := fun V => {| itw_map := id |};
  compose := fun U V W f g => {| itw_map := itw_map f ∘ itw_map g |}
|}.
Next Obligation.
  intros K G V W; constructor.
  - intros f; reflexivity.
  - intros f g Hfg; symmetry; exact Hfg.
  - intros f g h H1 H2; transitivity (itw_map g); assumption.
Qed.
Next Obligation.
  intros K G V g.
  rewrite id_left, id_right; reflexivity.
Qed.
Next Obligation.
  intros K G U V W f g gr.
  rewrite <- comp_assoc.
  rewrite (itw_equivar g gr).
  rewrite comp_assoc.
  rewrite (itw_equivar f gr).
  rewrite <- comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  intros K G U V W f f' Hf g g' Hg.
  exact (@compose_respects (RMod K) (rep_mod U) (rep_mod V) (rep_mod W)
           _ _ Hf _ _ Hg).
Qed.
Next Obligation. intros K G V W f; exact (id_left (itw_map f)). Qed.
Next Obligation. intros K G V W f; exact (id_right (itw_map f)). Qed.
Next Obligation.
  intros K G U V W X f g h.
  exact (comp_assoc (itw_map f) (itw_map g) (itw_map h)).
Qed.
Next Obligation.
  intros K G U V W X f g h.
  exact (comp_assoc_sym (itw_map f) (itw_map g) (itw_map h)).
Qed.

(** ** The comparison functors *)

(* A 函子 out delooping IS representation: value at the
 single 对象 module, action arrows spine
 homomorphism, made invertible [rep_of_monhom]. （已译） *)
Definition rep_of_functor {K : RingObject} {G : GrpObject}
  (F : Deloop (grp_mon G) ⟶ RMod K) : RepObject K G :=
  RepOfMonHom (G := G) (F ttt : RModObject K)
    (hom_monoid_of_functor (C := RMod K) F).

(* ...and conversely, through Construction/Deloop/Functors.v's spine. *)
Definition functor_of_rep {K : RingObject} {G : GrpObject}
  (V : RepObject K G) : Deloop (grp_mon G) ⟶ RMod K :=
  functor_of_hom_monoid (C := RMod K) (rep_mod V) (monhom_of_rep V).

(* The action representation read off 函子 函子's
 [fmap], definitionally — fact every obligation below leans on. （已译） *)
Lemma rep_of_functor_act {K : RingObject} {G : GrpObject}
  (F : Deloop (grp_mon G) ⟶ RMod K) (g : carrier G) :
  rep_act (rep_of_functor F) g ≈ fmap[F] g.
Proof. reflexivity. Qed.

Lemma functor_of_rep_fmap {K : RingObject} {G : GrpObject}
  (V : RepObject K G) (g : carrier G) :
  @fmap _ _ (functor_of_rep V) ttt ttt g ≈ rep_act V g.
Proof. reflexivity. Qed.

(* Reading representation intertwiners off 函子: the
 态射 action takes transformation single component,
 whose 自然性 at g IS intertwining square. （已译） *)
Program Definition Rep_to (K : RingObject) (G : GrpObject) :
  [Deloop (grp_mon G), RMod K] ⟶ Rep K G := {|
  fobj := fun F => rep_of_functor F;
  fmap := fun F F' η => {| itw_map := transform[η] ttt |}
|}.
Next Obligation.
  intros K G F F' η g.
  exact (@naturality_sym _ _ F F' η ttt ttt g).
Qed.
Next Obligation.
  intros K G F F' η θ Hηθ; exact (Hηθ ttt).
Qed.
Next Obligation.
  intros K G F; exact (@fmap_id _ _ F ttt).
Qed.
Next Obligation.
  intros K G F F' F'' η θ; simpl; reflexivity.
Qed.

(* Materializing intertwiner 常值 transformation family;
 自然性 intertwining square. （已译） *)
Program Definition Rep_from (K : RingObject) (G : GrpObject) :
  Rep K G ⟶ [Deloop (grp_mon G), RMod K] := {|
  fobj := fun V => functor_of_rep V;
  fmap := fun V W h => {| transform := fun _ => itw_map h |}
|}.
Next Obligation.
  intros K G V W h [] [] g.
  symmetry; exact (itw_equivar h g).
Qed.
Next Obligation.
  intros K G V W h [] [] g.
  exact (itw_equivar h g).
Qed.
Next Obligation.
  intros K G V W h h' Hh []; exact Hh.
Qed.
Next Obligation.
  intros K G V [].
  symmetry; exact (rep_act_unit V).
Qed.
Next Obligation.
  intros K G U V W f g []; simpl; reflexivity.
Qed.

(** ** The equivalence *)

(* The representation-side round trip: two representations have the
 same module same action, so 恒等 module map an
 intertwiner both directions. （已译） *)
Program Definition Rep_action_round_iso {K : RingObject} {G : GrpObject}
  (V : RepObject K G) :
  @Isomorphism (Rep K G) (rep_of_functor (functor_of_rep V)) V := {|
  to   := {| itw_map := id |};
  from := {| itw_map := id |}
|}.
Next Obligation.
  intros K G V g; rewrite id_left, id_right; reflexivity.
Qed.
Next Obligation.
  intros K G V g; rewrite id_left, id_right; reflexivity.
Qed.
Next Obligation. intros K G V; exact (id_left (@id (RMod K) _)). Qed.
Next Obligation. intros K G V; exact (id_left (@id (RMod K) _)). Qed.

(*
   本节说明函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Rep_round_iso {K : RingObject} {G : GrpObject}
  (F : Deloop (grp_mon G) ⟶ RMod K) :
  @Isomorphism ([Deloop (grp_mon G), RMod K])
    (functor_of_rep (rep_of_functor F)) F := {|
  to   := {| transform := fun x =>
    match x return
      (functor_of_rep (rep_of_functor F) x ~{RMod K}~> F x)
    with ttt => id end |};
  from := {| transform := fun x =>
    match x return
      (F x ~{RMod K}~> functor_of_rep (rep_of_functor F) x)
    with ttt => id end |}
|}.
Next Obligation.
  intros K G F [] [] g.
  transitivity (@fmap _ _ F ttt ttt g).
  - exact (id_right (@fmap _ _ F ttt ttt g)).
  - symmetry; exact (id_left (@fmap _ _ F ttt ttt g)).
Qed.
Next Obligation.
  intros K G F [] [] g.
  transitivity (@fmap _ _ F ttt ttt g).
  - exact (id_right (@fmap _ _ F ttt ttt g)).
  - symmetry; exact (id_left (@fmap _ _ F ttt ttt g)).
Qed.
Next Obligation.
  intros K G F [] [] g.
  transitivity (@fmap _ _ F ttt ttt g).
  - exact (id_right (@fmap _ _ F ttt ttt g)).
  - symmetry; exact (id_left (@fmap _ _ F ttt ttt g)).
Qed.
Next Obligation.
  intros K G F [] [] g.
  transitivity (@fmap _ _ F ttt ttt g).
  - exact (id_right (@fmap _ _ F ttt ttt g)).
  - symmetry; exact (id_left (@fmap _ _ F ttt ttt g)).
Qed.
Next Obligation.
  intros K G F [].
  transitivity (@id (RMod K) (F ttt)).
  - exact (id_left (@id (RMod K) (F ttt))).
  - symmetry; apply fmap_id.
Qed.
Next Obligation.
  intros K G F [].
  transitivity (@id (RMod K) (F ttt)).
  - exact (id_left (@id (RMod K) (F ttt))).
  - symmetry.
    exact (@fmap_id _ _ (functor_of_rep (rep_of_functor F)) ttt).
Qed.

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Rep_Fun_equiv (K : RingObject) (G : GrpObject) :
  [Deloop (grp_mon G), RMod K] ≅[Cat] Rep K G := {|
  to   := Rep_to K G;
  from := Rep_from K G
|}.
Next Obligation.
  (* Rep_to ◯ Rep_from ≈ Id, through the representation-side round trip *)
  intros K G.
  exists (fun V => Rep_action_round_iso V).
  intros V W h a; simpl; reflexivity.
Qed.
Next Obligation.
  (* Rep_from ◯ Rep_to ≈ Id, through the transparent functor-side one *)
  intros K G.
  exists (fun F => Rep_round_iso F).
  intros F F' η [] a; simpl; reflexivity.
Qed.

(** ** Awodey's degeneracy *)

(* In a thin category any functor carries any ENDOmorphism to an
   identity: its image is parallel to [id], and thinness identifies
   parallel morphisms.  Neither the group hypothesis nor the one-object
   hypothesis plays any part. *)
Lemma thin_functor_endo_trivial {B C : Category} (T : Thin C)
  (F : B ⟶ C) {x : B} (f : x ~> x) : fmap[F] f ≈ id.
Proof. exact (T (F x) (F x) (fmap[F] f) id). Qed.

(* Awodey's statement: a representation of a group in a thin category
   is trivial — every group element acts as the identity. *)
Theorem thin_group_functor_trivial {G : GrpObject} {C : Category}
  (T : Thin C) (F : Deloop (grp_mon G) ⟶ C) (g : carrier G) :
  @fmap _ _ F ttt ttt g ≈ id.
Proof. exact (thin_functor_endo_trivial T F g). Qed.

(* Instantiated at a preorder.  The statement is about [Proset], not
   about posets: Instance/Poset.v's [Poset] is DEFINED as [Proset P] and
   drops antisymmetry, so nothing here would be strengthened by naming
   it.  [proset_thin] is Instance/Proset/Order.v's, cited. *)
Corollary proset_group_functor_trivial {G : GrpObject} {A : Type}
  {R : relation A} (P : RelationClasses.PreOrder R)
  (F : Deloop (grp_mon G) ⟶ Proset P) (g : carrier G) :
  @fmap _ _ F ttt ttt g ≈ id.
Proof. exact (thin_group_functor_trivial (proset_thin P) F g). Qed.

(** ** Witnesses *)

(* Double negation in an abelian group, the one fact Instance/Ab.v
   leaves unstated among its negation lemmas. *)
Lemma ab_neg_neg (A : AbObject) (a : carrier (cmon_setoid A)) :
  ab_neg A (ab_neg A a) ≈ a.
Proof. symmetry; apply ab_neg_unique; apply ab_neg_right. Qed.

(* The trivial representation any group any module: every element
 acts 恒等. Available at every K G, so [RepObject] is
 never empty. （已译） *)
Program Definition rep_id_unit {K : RingObject} (V : RModObject K) :
  carrier (grp_setoid (UnitsOf (hom_monoid (RMod K) V) (rmod_hom_monoid_prop K V))) :=
  (id; (id; (_, _))).
Next Obligation. intros K V; exact (id_left (@id (RMod K) V)). Qed.
Next Obligation. intros K V; exact (id_left (@id (RMod K) V)). Qed.

Lemma rep_id_unit_respects {K : RingObject} {G : GrpObject}
  (V : RModObject K) :
  Proper (equiv ==> equiv) (fun _ : carrier G => rep_id_unit V).
Proof. intros g g' Hgg'; apply units_equiv; reflexivity. Qed.

Lemma rep_id_unit_is_unit {K : RingObject} (V : RModObject K) :
  rep_id_unit V ≈ grp_unit (UnitsOf (hom_monoid (RMod K) V) (rmod_hom_monoid_prop K V)).
Proof. apply units_equiv; reflexivity. Qed.

Lemma rep_id_unit_mul {K : RingObject} (V : RModObject K) :
  rep_id_unit V
    ≈ grp_mul (UnitsOf (hom_monoid (RMod K) V) (rmod_hom_monoid_prop K V))
        (rep_id_unit V) (rep_id_unit V).
Proof.
  apply units_equiv; symmetry; exact (id_left (@id (RMod K) V)).
Qed.

(* Spelled term reason given at [rmod_neg_hom]: the
 obligation numbering not field numbering, every field
 here already 引理. （已译） *)
Definition trivial_rep {K : RingObject} {G : GrpObject}
  (V : RModObject K) : RepObject K G :=
  {| rep_mod := V
   ; rep_hom :=
       {| grp_map := {| morphism := fun _ : carrier G => rep_id_unit V
                      ; proper_morphism := rep_id_unit_respects V |}
        ; grp_map_unit := rep_id_unit_is_unit V
        ; grp_map_mul := fun a b => rep_id_unit_mul V |} |}.

(* Negation is a module endomorphism: additive because negation
   distributes over addition in an abelian group, K-linear because
   r·(−m) ≈ −(r·m) ([rm_smul_neg_r]). *)
Lemma ab_neg_hom_smul {K : RingObject} (V : RModObject K)
  (r : carrier (rig_setoid (ring_rig K)))
  (m : carrier (cmon_setoid V)) :
  ab_neg V (rm_smul V r m) ≈ rm_smul V r (ab_neg V m).
Proof. symmetry; apply rm_smul_neg_r. Qed.

(* Written as an explicit record literal rather than through [Program]:
   every field is an existing lemma, so there is nothing to defer, and
   Instance/Ab.v's exported [ab_neg_respects] instance would otherwise
   silently discharge one hole and shift the obligation numbering. *)
Definition rmod_neg_hom {K : RingObject} (V : RModObject K) :
  V ~{RMod K}~> V :=
  {| rm_hom :=
       {| cmon_map := {| morphism        := ab_neg V
                       ; proper_morphism := ab_neg_respects V |}
        ; cmon_map_zero := ab_neg_zero V
        ; cmon_map_plus := ab_neg_plus V |}
   ; rm_map_smul := ab_neg_hom_smul V |}.

(* 相关说明。 （已译） *)
Definition sign_act {K : RingObject} (V : RModObject K) (b : bool) :
  V ~{RMod K}~> V :=
  if b then rmod_neg_hom V else id.

Lemma sign_act_involutive {K : RingObject} (V : RModObject K)
  (b : bool) : sign_act V b ∘ sign_act V b ≈ id.
Proof.
  destruct b.
  - intro a; simpl; apply ab_neg_neg.
  - exact (id_left (@id (RMod K) V)).
Qed.

(*
   本节说明 Rep 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sign_unit {K : RingObject} (V : RModObject K)
  (b : carrier Z2) :
  carrier (grp_setoid (UnitsOf (hom_monoid (RMod K) V) (rmod_hom_monoid_prop K V))) :=
  (sign_act V b;
   (sign_act V b;
    (sign_act_involutive V b, sign_act_involutive V b))).

Lemma sign_unit_respects {K : RingObject} (V : RModObject K) :
  Proper (equiv ==> equiv) (sign_unit V).
Proof.
  intros b b' Hbb'; simpl in Hbb'; subst; reflexivity.
Qed.

Lemma sign_unit_is_unit {K : RingObject} (V : RModObject K) :
  sign_unit V (grp_unit Z2)
    ≈ grp_unit (UnitsOf (hom_monoid (RMod K) V) (rmod_hom_monoid_prop K V)).
Proof. apply units_equiv; reflexivity. Qed.

Lemma sign_unit_mul {K : RingObject} (V : RModObject K)
  (a b : carrier Z2) :
  sign_unit V (grp_mul Z2 a b)
    ≈ grp_mul (UnitsOf (hom_monoid (RMod K) V) (rmod_hom_monoid_prop K V))
        (sign_unit V a) (sign_unit V b).
Proof.
  apply units_equiv; symmetry.
  destruct a, b.
  - exact (sign_act_involutive V true).
  - exact (id_right (rmod_neg_hom V)).
  - exact (id_left (rmod_neg_hom V)).
  - exact (id_left (@id (RMod K) V)).
Qed.

Definition sign_rep {K : RingObject} (V : RModObject K) :
  RepObject K Z2 :=
  {| rep_mod := V
   ; rep_hom :=
       {| grp_map := {| morphism := sign_unit V
                      ; proper_morphism := sign_unit_respects V |}
        ; grp_map_unit := sign_unit_is_unit V
        ; grp_map_mul := sign_unit_mul V |} |}.

(*
   本节说明 Rep 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sign_rep_moves_one :
  cmon_map (rm_hom (rep_act (sign_rep Int_RMod) true)) 1%Z ≈ (-1)%Z.
Proof. reflexivity. Qed.

Lemma sign_rep_nontrivial :
  rep_act (sign_rep Int_RMod) true ≈ rep_act (sign_rep Int_RMod) false
    → False.
Proof.
  intro H.
  pose proof (H 1%Z) as H1.
  simpl in H1.
  discriminate H1.
Qed.

(* The 恒等 module map not intertwiner between two
 witnesses: actions differ pointwise. （已译） *)
Lemma sign_rep_not_trivial_rep :
  (∀ g : carrier Z2,
     rep_act (sign_rep Int_RMod) g ≈ rep_act (trivial_rep Int_RMod) g)
    → False.
Proof.
  intro H.
  pose proof (H true 1%Z) as H1.
  simpl in H1.
  discriminate H1.
Qed.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sign_not_iso_trivial :
  @Isomorphism (Rep Int_Ring Z2) (sign_rep Int_RMod) (trivial_rep Int_RMod)
    → False.
Proof.
  intro iso.
  assert (Hzero : ∀ n : Z, cmon_map (rm_hom (itw_map (to iso))) n = 0%Z).
  { intro n.
    assert (Hf : cmon_map (rm_hom (itw_map (to iso))) (Z.opp n)
                   = cmon_map (rm_hom (itw_map (to iso))) n)
      by exact (itw_equivar (to iso) true n).
    assert (Hn : cmon_map (rm_hom (itw_map (to iso))) (Z.opp n)
                   = Z.opp (cmon_map (rm_hom (itw_map (to iso))) n))
      by exact (ab_map_neg (rm_hom (itw_map (to iso))) n).
    lia. }
  assert (H1 : cmon_map (rm_hom (itw_map (to iso)))
                 (cmon_map (rm_hom (itw_map (from iso))) 1%Z) = 1%Z)
    by exact (iso_to_from iso 1%Z).
  rewrite (Hzero _) in H1.
  discriminate H1.
Qed.
