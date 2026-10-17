Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

(** * [Sets] is cocomplete *)

(*
 nLab:      https://ncatlab.org/nlab/show/colimit
 Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

Section SetsColimit.

Context {D : Category}.
Context (F : D ⟶ Sets).

(* * ** The indexed coproduct diagram's 对象 （已译） *)

Definition Sets_colim_sum : obj[Sets] := Sets_icoprod_obj (fun d : D => F d).

(* * ** The 关系 generated connecting maps （已译） *)

Inductive colim_rel :
  carrier Sets_colim_sum -> carrier Sets_colim_sum -> Type :=
  | cr_point : forall (d : D) (x y : F d), x ≈ y ->
      colim_rel (existT _ d x) (existT _ d y)
  | cr_glue  : forall (d d' : D) (f : d ~{D}~> d') (x : F d),
      colim_rel (existT _ d x) (existT _ d' (fmap[F] f x))
  | cr_sym   : forall p q, colim_rel p q -> colim_rel q p
  | cr_trans : forall p q r, colim_rel p q -> colim_rel q r -> colim_rel p r.

Lemma colim_rel_refl (p : carrier Sets_colim_sum) : colim_rel p p.
Proof. destruct p as [d x]; apply cr_point; reflexivity. Qed.

Definition colim_rel_Equivalence : Equivalence colim_rel.
Proof.
  constructor.
  - exact colim_rel_refl.
  - exact cr_sym.
  - exact cr_trans.
Defined.

(* * ** The colimit apex: coproduct quotiented 关系 （已译） *)

Definition Sets_colim_obj : obj[Sets] :=
  SetsQuotient Sets_colim_sum colim_rel colim_rel_Equivalence.

Lemma Sets_colim_coarser : SetoidCoarser colim_rel.
Proof.
  intros [d x] [d' y] [e Hxy]; simpl in *.
  destruct e; simpl in *.
  now apply cr_point.
Qed.

Program Definition Sets_colim_inj (d : D) :
  F d ~{Sets}~> Sets_colim_obj := {|
  morphism := fun x => existT _ d x
|}.
Next Obligation. intros d x y Hxy; apply cr_point; exact Hxy. Qed.

Definition Sets_colim_inj_donors (d : D) : F d ~{Sets}~> Sets_colim_obj :=
  sets_quot_proj Sets_colim_sum colim_rel colim_rel_Equivalence
    Sets_colim_coarser ∘ Sets_icoprod_inj (fun d : D => F d) d.

Example Sets_colim_inj_is_donor_composite (d : D) (x : F d) :
  Sets_colim_inj d x = Sets_colim_inj_donors d x.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Sets_colim_carrier_is_coproduct :
  carrier Sets_colim_obj = Sets_icoprod_carrier (fun d : D => F d).
Proof. reflexivity. Qed.

(* ... apex's own `≈` IS generated 关系. （已译） *)
Example Sets_colim_equiv_is_rel (p q : carrier Sets_colim_sum) :
  @equiv _ Sets_colim_obj p q = colim_rel p q.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Example Sets_colim_inj_at (d : D) (x : F d) :
  Sets_colim_inj d x = existT _ d x.
Proof. reflexivity. Qed.

(** ** The colimit cocone *)

Program Definition Sets_colim_cocone : Cocone F := {|
  vertex_obj := Sets_colim_obj;
  coneFrom   := {| vertex_map := Sets_colim_inj |}
|}.
Next Obligation.
  intros d d' f x.
  exact (cr_sym _ _ (cr_glue d' d f x)).
Qed.

(* 相关说明。 （已译） *)

Definition Sets_colim_med_fun (N : Cocone F)
  (p : carrier Sets_colim_sum) : carrier (vertex_obj[N]) :=
  match p with
  | existT _ d x => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d x
  end.

Lemma Sets_colim_med_respects (N : Cocone F)
  (p q : carrier Sets_colim_sum) (H : colim_rel p q) :
  Sets_colim_med_fun N p ≈ Sets_colim_med_fun N q.
Proof.
  induction H as [d x y Hxy | d d' f x | p q H IH | p q r H1 IH1 H2 IH2].
  - now apply proper_morphism.
  - symmetry.
    exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) d' d f x).
  - now symmetry.
  - now transitivity (Sets_colim_med_fun N q).
Qed.

Program Definition Sets_colim_med (N : Cocone F) :
  Sets_colim_obj ~{Sets}~> vertex_obj[N] := {|
  morphism := Sets_colim_med_fun N
|}.
Next Obligation.
  intros N p q Hpq; exact (Sets_colim_med_respects N p q Hpq).
Qed.

(*
   本节说明 Cocomplete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Sets_colim_triangle (N : Cocone F) (d : D) (x : F d) :
  Sets_colim_med N (Sets_colim_inj d x)
    = @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d x.
Proof. reflexivity. Qed.

(*
   本节说明（余）端相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma colim_rel_separates (N : Cocone F) (p q : carrier Sets_colim_sum) :
  (Sets_colim_med_fun N p ≈ Sets_colim_med_fun N q -> False) ->
  colim_rel p q -> False.
Proof. intros Hne Hpq; exact (Hne (Sets_colim_med_respects N p q Hpq)). Qed.

(** ** The colimit *)

Program Definition Sets_Colimit : Colimit F := {|
  limit_cone := Sets_colim_cocone;
  ump_limits := fun N => {| unique_obj := Sets_colim_med N |}
|}.
Next Obligation. intros N d x; reflexivity. Qed.
Next Obligation.
  intros N v Hv p; destruct p as [d x]; symmetry; exact (Hv d x).
Qed.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Sets_Colimit_cocone :
  @limit_cone _ _ _ Sets_Colimit = Sets_colim_cocone.
Proof. reflexivity. Qed.

End SetsColimit.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_Cocomplete@{uc ud uo uso} :
  @Cocomplete@{uc ud uo uso} Sets@{uo uso} := fun D F => Sets_Colimit F.

(* * * Non-vacuity, at two-对象 discrete shape （已译） *)

(* Everything below about ONE shape ONE diagram. It witness,
 not general non-collapse 定理, header says so. （已译） *)

Section TwoDiscreteWitness.

(* The two-object discrete shape.  Its hom type IS index equality, by
   conversion, which is precisely why [cr_glue] has nothing to glue across
   the two objects: a morphism can only relate an index to itself. *)
Definition TwoDisc : Category := DiscreteCat bool.

Example two_disc_hom_is_eq (b b' : bool) :
  (b ~{TwoDisc}~> b') = (b = b').
Proof. reflexivity. Qed.

(* ... shape really does have two 对象, so "the two fibres"
 below names two things not one. （已译） *)
Lemma two_disc_objects_distinct : (true : TwoDisc) = (false : TwoDisc) -> False.
Proof. discriminate. Qed.

(*
   本节说明 Cocomplete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition TwoPoints : TwoDisc ⟶ Sets := {|
  fobj := fun _ => unit_setoid_object;
  fmap := fun _ _ _ => id
|}.
(* Measured: [fmap_respects] never surfaces obligation here, the
 arrow action being 常值; two do [fmap_id] and
 [fmap_comp]. （已译） *)
Next Obligation. intros x; reflexivity. Qed.
Next Obligation. intros x y z f g; symmetry; apply id_left. Qed.

(*
   本节说明 Cocomplete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition two_sep_leg (b : bool) :
  TwoPoints b ~{Sets}~> bool_setoid_object := {|
  morphism := fun _ => b
|}.
(* Measured: [proper_morphism] never surfaces as an obligation here
   either, the map being constant, so none is written out. *)

Program Definition TwoSep : Cocone TwoPoints := {|
  vertex_obj := bool_setoid_object;
  coneFrom   := {| vertex_map := two_sep_leg |}
|}.
Next Obligation. intros b b' e x; exact (eq_sym e). Qed.

(*
   本节说明 Cocomplete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition two_fibre_point_true : carrier (TwoPoints true) := ttt.
Definition two_fibre_point_false : carrier (TwoPoints false) := ttt.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem two_fibres_not_collapsed :
  colim_rel TwoPoints
    (existT _ true two_fibre_point_true)
    (existT _ false two_fibre_point_false) -> False.
Proof.
  apply (colim_rel_separates TwoPoints TwoSep).
  discriminate.
Qed.

(* 相关说明。 （已译） *)
Corollary two_fibres_not_equal_in_colimit :
  @equiv _ (Sets_colim_obj TwoPoints)
    (existT _ true two_fibre_point_true)
    (existT _ false two_fibre_point_false) -> False.
Proof. exact two_fibres_not_collapsed. Qed.

(*
   本节说明 Cocomplete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma empty_shape_colim_empty (F : DiscreteCat False ⟶ Sets)
  (p : carrier (Sets_colim_obj F)) : False.
Proof. destruct p as [d x]; destruct d. Qed.

End TwoDiscreteWitness.
