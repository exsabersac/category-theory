Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Comp.
Require Import Category.Instance.Variety.
Require Import Category.Instance.Variety.Free.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/variety+of+algebras
 Wikipedia: https://en.wikipedia.org/wiki/Variety_(universal_algebra)

   本文件给出极限实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Module UA := Category.Instance.Comp.UniversalAlgebra.

#[local] Obligation Tactic := idtac.

Section SVarietyLimit.

Context {S : UA.OpSignature}.
Context (E : UA.EqSignature S).
Context {J : Category}.
Context (F : J ⟶ SVariety E).

(* The underlying diagram of setoids. *)
Definition svlim_UF : J ⟶ Sets := SVariety_Forget E ◯ F.

(* 相关说明。 （已译） *)
Definition svlim_obj : SetoidObject := Sets_limit_obj svlim_UF.

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition svlim_op (o : UA.operation S)
  (k : UA.arity o → carrier svlim_obj) : carrier svlim_obj.
Proof.
  exists (fun d => soa_op (`1 (F d)) o (fun i => `1 (k i) d)).
  intros d d' f; simpl.
  transitivity (soa_op (`1 (F d')) o
                  (fun i => salg_map (`1 (fmap[F] f)) (`1 (k i) d))).
  - exact (salg_commute (`1 (fmap[F] f)) o (fun i => `1 (k i) d)).
  - apply (soa_op_respects (`1 (F d')) o); intro i.
    exact (`2 (k i) d d' f).
Defined.

(* The propositional equality Instance/Sets/Propositional.v's limit
 transport, supplied components' own [soa_prop] no
 假设 limit. （已译） *)
Definition svlim_soa : SetoidOpAlgebra S := {|
  soa_obj := svlim_obj;
  soa_op := svlim_op;
  soa_op_respects := fun o k1 k2 H d =>
    soa_op_respects (`1 (F d)) o _ _ (fun i => H i d);
  soa_prop := limit_PropEquiv svlim_UF (fun d => soa_prop (`1 (F d)))
|}.

(* 相关说明。 （已译） *)
Definition svlim_eval (d : J) :
  UA.AlgHom (soa_alg svlim_soa) (soa_alg (`1 (F d))).
Proof. exists (fun p => `1 p d). intros o args; reflexivity. Defined.

(* 相关说明。 （已译） *)
Lemma svlim_satisfies : ssatisfies E svlim_soa.
Proof.
  intros e args d.
  assert (HL : `1 (@UA.lhs S E (soa_alg svlim_soa) e args) d
               = @UA.lhs S E (soa_alg (`1 (F d))) e (fun i => `1 (args i) d))
    by exact (@UA.lhs_natural S E _ _ (svlim_eval d) e args).
  assert (HR : `1 (@UA.rhs S E (soa_alg svlim_soa) e args) d
               = @UA.rhs S E (soa_alg (`1 (F d))) e (fun i => `1 (args i) d))
    by exact (@UA.rhs_natural S E _ _ (svlim_eval d) e args).
  change (`1 (@UA.lhs S E (soa_alg svlim_soa) e args) d
          ≈ `1 (@UA.rhs S E (soa_alg svlim_soa) e args) d).
  rewrite HL, HR.
  exact (`2 (F d) e (fun i => `1 (args i) d)).
Qed.

Definition svlim_alg : SVariety E := (svlim_soa; svlim_satisfies).

Program Definition svlim_leg (d : J) : svlim_alg ~{SVariety E}~> F d :=
  ({| salg_map := fun p : carrier svlim_obj => `1 p d |}; I).
Next Obligation. intros d p q H; exact (H d). Qed.
Next Obligation. intros d o args; simpl; reflexivity. Qed.

Program Definition svlim_cone : Cone F := {|
  vertex_obj := svlim_alg;
  coneFrom := {| vertex_map := svlim_leg |}
|}.
Next Obligation. intros d d' f p; exact (`2 p d d' f). Qed.

(*
   本节说明 Limit 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition svlim_med_map (N : Cone F)
  (x : carrier (soa_obj (`1 (vertex_obj[N])))) : carrier svlim_obj.
Proof.
  exists (fun d => salg_map (`1 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) d)) x).
  intros d d' f.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) d d' f x).
Defined.

Program Definition svlim_med (N : Cone F) :
  vertex_obj[N] ~{SVariety E}~> svlim_alg :=
  ({| salg_map := svlim_med_map N |}; I).
Next Obligation.
  intros N x y H d; simpl.
  exact (salg_respects (`1 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) d)) x y H).
Qed.
Next Obligation.
  intros N o args d; simpl.
  exact (salg_commute (`1 (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) d)) o args).
Qed.

Program Definition SVariety_Limit : Limit F := {|
  limit_cone := svlim_cone;
  ump_limits := fun N => {| unique_obj := svlim_med N |}
|}.
Next Obligation. intros N d x; simpl; reflexivity. Qed.
Next Obligation. intros N v Hv x d; simpl; symmetry; exact (Hv d x). Qed.

End SVarietyLimit.

Arguments svlim_UF {_} _ {_} _.
Arguments svlim_obj {_} _ {_} _.
Arguments svlim_op {_} _ {_} _ _ _.
Arguments svlim_soa {_} _ {_} _.
Arguments svlim_eval {_} _ {_} _ _.
Arguments svlim_satisfies {_} _ {_} _ _ _ _.
Arguments svlim_alg {_} _ {_} _.
Arguments svlim_leg {_} _ {_} _ _.
Arguments svlim_cone {_} _ {_} _.
Arguments svlim_med_map {_} _ {_} _ _ _.
Arguments svlim_med {_} _ {_} _ _.
Arguments SVariety_Limit {_} _ {_} _.

Definition SVariety_Complete {S : UA.OpSignature} (E : UA.EqSignature S) :
  @Complete (SVariety E) := fun J F => SVariety_Limit E F.

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example svariety_complete_carrier {S : UA.OpSignature} (E : UA.EqSignature S)
  {J : Category} (F : J ⟶ SVariety E) :
  carrier (soa_obj (`1 (vertex_obj[@limit_cone _ _ _ (SVariety_Complete E J F)])))
    = Sets_limit_carrier (svlim_UF E F) := eq_refl.

Example svariety_complete_op {S : UA.OpSignature} (E : UA.EqSignature S)
  {J : Category} (F : J ⟶ SVariety E) (o : UA.operation S)
  (k : UA.arity o → carrier (svlim_obj E F)) (d : J) :
  `1 (soa_op (`1 (vertex_obj[@limit_cone _ _ _ (SVariety_Complete E J F)])) o k) d
    = soa_op (`1 (F d)) o (fun i => `1 (k i) d) := eq_refl.

Example svariety_complete_leg {S : UA.OpSignature} (E : UA.EqSignature S)
  {J : Category} (F : J ⟶ SVariety E) (d : J) (p : carrier (svlim_obj E F)) :
  salg_map (`1 (@vertex_map _ _ _ _
                 (@coneFrom _ _ _ (@limit_cone _ _ _ (SVariety_Complete E J F))) d)) p
    = `1 p d := eq_refl.

(*
   本节说明函子、（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section ForgetContinuous.

Context {S : UA.OpSignature}.
Context (E : UA.EqSignature S).
Context {J : Category}.
Context (G : J ⟶ SVariety E).
Context (N : Cone G) (HN : IsLimitCone N).
Context (M : Cone (SVariety_Forget E ◯ G)).

(* 相关说明。 （已译） *)
Definition svf_to : svlim_alg E G ~{SVariety E}~> vertex_obj[N] :=
  unique_obj (HN (svlim_cone E G)).

Lemma svf_to_legs (d : J) (p : carrier (svlim_obj E G)) :
  salg_map (`1 (cone_leg N d)) (salg_map (`1 svf_to) p) ≈ `1 p d.
Proof. exact (unique_property (HN (svlim_cone E G)) d p). Qed.

(* It retraction [svlim_med]: [svf_to ∘ svlim_med N] the
 恒等 both mediators [N] itself. （已译） *)
Lemma svf_to_med (y : carrier (soa_obj (`1 (vertex_obj[N])))) :
  salg_map (`1 svf_to) (salg_map (`1 (svlim_med E G N)) y) ≈ y.
Proof.
  assert (Hid : unique_obj (HN N) ≈ id[vertex_obj[N]]).
  { apply (uniqueness (HN N)); intros d x; reflexivity. }
  assert (Hcomp : unique_obj (HN N) ≈ svf_to ∘ svlim_med E G N).
  { apply (uniqueness (HN N)); intros d x; simpl.
    exact (svf_to_legs d (svlim_med_map E G N x)). }
  exact (transitivity (symmetry (Hcomp y)) (Hid y)).
Qed.

(* 相关说明。 （已译） *)
Definition svf_family (x : carrier (vertex_obj[M])) : carrier (svlim_obj E G).
Proof.
  (* 相关说明。 （已译） *)
  exists (fun d => cone_leg M d x).
  intros d d' f.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ M) d d' f x).
Defined.

Program Definition svf_med :
  vertex_obj[M] ~{Sets}~> SVariety_Forget E (vertex_obj[N]) := {|
  morphism := fun x => salg_map (`1 svf_to) (svf_family x)
|}.
Next Obligation.
  intros x y Hxy.
  apply (salg_respects (`1 svf_to)).
  intro d; simpl.
  exact (proper_morphism (cone_leg M d) x y Hxy).
Qed.

Lemma svf_med_legs (d : J) :
  cone_leg (FCone (SVariety_Forget E) N) d ∘ svf_med ≈ cone_leg M d.
Proof. intro x; exact (svf_to_legs d (svf_family x)). Qed.

Lemma svf_med_unique
  (v : vertex_obj[M] ~{Sets}~> SVariety_Forget E (vertex_obj[N])) :
  (∀ d : J, cone_leg (FCone (SVariety_Forget E) N) d ∘ v ≈ cone_leg M d) →
  svf_med ≈ v.
Proof.
  intros Hv x; simpl.
  transitivity (salg_map (`1 svf_to) (salg_map (`1 (svlim_med E G N)) (v x))).
  - apply (salg_respects (`1 svf_to)).
    intro d; simpl; symmetry; exact (Hv d x).
  - exact (svf_to_med (v x)).
Qed.

End ForgetContinuous.

Arguments svf_to {_} _ {_} _ _ _.
Arguments svf_to_legs {_} _ {_} _ _ _ _ _.
Arguments svf_to_med {_} _ {_} _ _ _ _.
Arguments svf_family {_} _ {_} _ _ _.
Arguments svf_med {_} _ {_} _ _ _ _.
Arguments svf_med_legs {_} _ {_} _ _ _ _ _ _.
Arguments svf_med_unique {_} _ {_} _ _ _ _ _ _ _.

Definition SVariety_Forget_continuous {S : UA.OpSignature}
  (E : UA.EqSignature S) : ContinuousFunctor (SVariety_Forget E) :=
  fun J G N HN M =>
    {| unique_obj := svf_med E G N HN M
     ; unique_property := svf_med_legs E G N HN M
     ; uniqueness := svf_med_unique E G N HN M |}.
