Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Transform.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.

(*
   本文件给出合同相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   nLab: https://ncatlab.org/nlab/show/normal+subgroup
   nLab: https://ncatlab.org/nlab/show/congruence
   Wikipedia: https://en.wikipedia.org/wiki/Normal_subgroup

   本节说明hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition grp_MonInverses (H : GrpObject) : MonInverses (grp_deloop_monoid H) :=
  @Build_MonInverses (grp_deloop_monoid H)
    (grp_inv H) (grp_mul_inv_l H) (grp_mul_inv_r H).

Definition grp_deloop_GrpObject (H : GrpObject)
  : Category.Construction.Deloop.GrpObject :=
  GrpObject_of (grp_MonInverses H).

(*
   本节说明 Congruence 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example deloop_GrpObject_agrees (H : GrpObject) :
  Deloop (grp_deloop_GrpObject H) = grp_deloop H := eq_refl.

Example deloop_GrpObject_monoid (H : GrpObject) :
  Category.Construction.Deloop.grp_monoid (grp_deloop_GrpObject H)
    = grp_deloop_monoid H := eq_refl.

(*
   本节说明 Congruence 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition grp_deloop_IsGroupoid' (H : GrpObject) : IsGroupoid (grp_deloop H) :=
  Deloop_IsGroupoid (grp_deloop_GrpObject H).

Example grp_deloop_ginv (H : GrpObject) (a : carrier H) :
  ginv (grp_deloop_IsGroupoid' H) (x:=ttt) (y:=ttt) a = grp_inv H a := eq_refl.

Example grp_deloop_ginv_Free (H : GrpObject) (a : carrier H) :
  ginv (grp_deloop_IsGroupoid H) (x:=ttt) (y:=ttt) a = grp_inv H a := eq_refl.

(** ** Arithmetic of the delooping

    Every one of these is [eq_refl]; they are recorded so that the
    congruence proofs below can be read as group computations without
    unfolding [Deloop]. *)

Section DeloopArithmetic.

Context {G : GrpObject}.

(** An element of G, read as an arrow of the delooping.  Definitional in
    both directions; it exists only to give the elaborator the hom type
    when a [HomCongruence] field is applied to a group element. *)
Definition deloop_arr (a : carrier G) : ttt ~{grp_deloop G}~> ttt := a.

Example deloop_hom_type (x y : grp_deloop G) :
  (x ~{grp_deloop G}~> y) = carrier G := eq_refl.

Example deloop_id_is_unit : @id (grp_deloop G) ttt = grp_unit G := eq_refl.

Example deloop_compose_is_mul (f g : carrier G) :
  @compose (grp_deloop G) ttt ttt ttt f g = grp_mul G f g := eq_refl.

End DeloopArithmetic.

(*
   本节说明 Congruence 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition ns_rel {G : GrpObject} (N : NormalSubgroup G)
  : HomRelT (grp_deloop G) := fun _ _ f g => quot_rel N f g.

(** The relation IS [quot_rel], by convertibility -- so every lemma #313
    proves about [quot_rel] is a lemma about this congruence. *)
Example ns_rel_is_quot_rel {G : GrpObject} (N : NormalSubgroup G)
  (f g : carrier G) : ns_rel N ttt ttt f g = quot_rel N f g := eq_refl.

(** Mac Lane §II.8 Exercise 2, one direction.  Kept a plain [Definition]
    rather than an [Instance], following [FunctorKernel_Congruence]'s own
    convention in [Construction/Quotient.v]: nothing new enters
    typeclass search, and the witness stays transparent. *)
Definition ns_congruence {G : GrpObject} (N : NormalSubgroup G)
  : @HomCongruence (grp_deloop G) (ns_rel N) :=
  @Build_HomCongruence (grp_deloop G) (ns_rel N)
    (fun x y f g H   => quot_rel_of_equiv N f g H)
    (fun x y f g H   => quot_rel_sym N f g H)
    (fun x y f g h H1 H2 => quot_rel_trans N f g h H1 H2)
    (fun x y z f f' g g' H1 H2 => quot_rel_mul N f f' g g' H1 H2).

(*
   本节说明 Congruence 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ns_prel {G : GrpObject} (N : NormalSubgroup G)
  : HomRelT (grp_deloop G) := fun _ _ f g => quot_equiv N f g.

Example ns_prel_is_truncation {G : GrpObject} (N : NormalSubgroup G)
  (f g : carrier G) :
  ns_prel N ttt ttt f g = inhabited (ns_rel N ttt ttt f g) := eq_refl.

(* Built tactically rather than as a term: a bare [match] on [inhabited] is
   elaborated with a [Type] motive and is refused, even where the branch's
   result is a [Prop]. *)
Definition ns_prel_congruence {G : GrpObject} (N : NormalSubgroup G)
  : @HomCongruence (grp_deloop G) (ns_prel N).
Proof.
  unshelve refine (@Build_HomCongruence (grp_deloop G) (ns_prel N) _ _ _ _).
  (* [HomRelT] ascribes sort [Type] to each relation, so the goal is
     converted to its [inhabited] form before any elimination. *)
  - intros x y f g H; exact (inhabits (quot_rel_of_equiv N f g H)).
  - intros x y f g H; unfold ns_prel, quot_equiv in *;
      destruct H as [h]; exact (inhabits (quot_rel_sym N f g h)).
  - intros x y f g h H1 H2; unfold ns_prel, quot_equiv in *;
      destruct H1 as [h1], H2 as [h2];
      exact (inhabits (quot_rel_trans N f g h h1 h2)).
  - intros x y z f f' g g' H1 H2; unfold ns_prel, quot_equiv in *;
      destruct H1 as [h1], H2 as [h2];
      exact (inhabits (quot_rel_mul N f f' g g' h1 h2)).
Defined.

(** The quotient category of the delooping.  The congruence witness is
    passed explicitly, since [ns_prel_congruence] is not an instance. *)
Definition deloop_quotient {G : GrpObject} (N : NormalSubgroup G) : Category :=
  @Quotient (grp_deloop G) (ns_prel N) (ns_prel_congruence N).

Definition deloop_quotient_proj {G : GrpObject} (N : NormalSubgroup G)
  : grp_deloop G ⟶ deloop_quotient N :=
  @QuotientProj (grp_deloop G) (ns_prel N) (ns_prel_congruence N).

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma quot_rel_flip {G : GrpObject} (N : NormalSubgroup G) (a b : carrier G) :
  quot_rel N a b ↔ sub_mem N (grp_mul G (grp_inv G b) a).
Proof.
  split; intro K; unfold quot_rel in *.
  - apply (sub_at N (a := grp_mul G (grp_mul G (grp_inv G b)
                                      (grp_mul G a (grp_inv G b)))
                       (grp_inv G (grp_inv G b)))).
    + rewrite (grp_inv_inv G b).
      rewrite (grp_mul_assoc G (grp_inv G b) (grp_mul G a (grp_inv G b)) b).
      rewrite (grp_mul_assoc G a (grp_inv G b) b).
      rewrite (grp_mul_inv_l G b), (grp_mul_unit_r G a).
      reflexivity.
    + exact (ns_conj N (grp_inv G b) _ K).
  - apply (sub_at N (a := grp_mul G (grp_mul G b
                                      (grp_mul G (grp_inv G b) a))
                       (grp_inv G b))).
    + rewrite <- (grp_mul_assoc G b (grp_inv G b) a).
      rewrite (grp_mul_inv_r G b), (grp_mul_unit_l G a).
      reflexivity.
    + exact (ns_conj N b _ K).
Qed.

(** Issue #301's own formula, as the congruence's relation. *)
Corollary ns_rel_flip {G : GrpObject} (N : NormalSubgroup G) (f g : carrier G) :
  ns_rel N ttt ttt f g ↔ sub_mem N (grp_mul G (grp_inv G g) f).
Proof. exact (quot_rel_flip N f g). Qed.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Converse.

Context {G : GrpObject}.
Context (R : HomRelT (grp_deloop G)).
Context `{HR : @HomCongruence (grp_deloop G) R}.

Definition cong_mem (a : carrier G) : Type :=
  R ttt ttt (deloop_arr a) (@id (grp_deloop G) ttt).

Program Definition cong_sub : Subgroup G := {|
  sub_mem := cong_mem
|}.
Next Obligation.                       (* ≈-saturation *)
  intros a b Hab Ha; unfold cong_mem in *.
  exact (@cong_trans (grp_deloop G) R HR ttt ttt
           (deloop_arr b) (deloop_arr a) id
           (@cong_incl (grp_deloop G) R HR ttt ttt
              (deloop_arr b) (deloop_arr a) (symmetry Hab)) Ha).
Qed.
Next Obligation.                       (* the unit *)
  unfold cong_mem; apply cong_refl.
Qed.
Next Obligation.                       (* closure under product *)
  intros a b Ha Hb; unfold cong_mem in *.
  exact (@cong_trans (grp_deloop G) R HR ttt ttt
           (deloop_arr (grp_mul G a b)) (id ∘ id) id
           (@cong_comp (grp_deloop G) R HR ttt ttt ttt
              (deloop_arr a) id (deloop_arr b) id Ha Hb)
           (@cong_incl (grp_deloop G) R HR ttt ttt (id ∘ id) id (id_left id))).
Qed.
Next Obligation.                       (* closure under inverse *)
  intros a Ha; unfold cong_mem in *.
  apply cong_sym.
  refine (@cong_trans (grp_deloop G) R HR ttt ttt id
            (deloop_arr (grp_inv G a) ∘ deloop_arr a) _ _ _).
  - exact (@cong_incl (grp_deloop G) R HR ttt ttt id
             (deloop_arr (grp_inv G a) ∘ deloop_arr a)
             (symmetry (grp_mul_inv_l G a))).
  - refine (@cong_trans (grp_deloop G) R HR ttt ttt _
              (deloop_arr (grp_inv G a) ∘ id) _ _ _).
    + exact (@cong_comp (grp_deloop G) R HR ttt ttt ttt
               (deloop_arr (grp_inv G a)) (deloop_arr (grp_inv G a))
               (deloop_arr a) id (cong_refl _) Ha).
    + exact (@cong_incl (grp_deloop G) R HR ttt ttt
               (deloop_arr (grp_inv G a) ∘ id) (deloop_arr (grp_inv G a))
               (id_right _)).
Qed.

(** Normality is the fifth field, and it is where the congruence's
    two-sided compatibility with composition is spent: t on the left and
    t⁻¹ on the right. *)
Program Definition cong_ns : NormalSubgroup G := {|
  ns_sub := cong_sub
|}.
Next Obligation.
  intros t a Ha; simpl in *; unfold cong_mem in *.
  refine (@cong_trans (grp_deloop G) R HR ttt ttt _
            ((deloop_arr t ∘ id) ∘ deloop_arr (grp_inv G t)) id _ _).
  - exact (@cong_comp (grp_deloop G) R HR ttt ttt ttt
             (deloop_arr t ∘ deloop_arr a) (deloop_arr t ∘ id)
             (deloop_arr (grp_inv G t)) (deloop_arr (grp_inv G t))
             (@cong_comp (grp_deloop G) R HR ttt ttt ttt
                (deloop_arr t) (deloop_arr t) (deloop_arr a) id
                (cong_refl _) Ha)
             (cong_refl _)).
  - apply cong_incl.
    rewrite id_right.
    exact (grp_mul_inv_r G t).
Qed.

End Converse.

(** Membership in the recovered subgroup IS relatedness to the identity,
    by convertibility. *)
Example cong_mem_is_class_of_id {G : GrpObject} (R : HomRelT (grp_deloop G))
  `{HR : @HomCongruence (grp_deloop G) R} (a : carrier G) :
  sub_mem (@cong_ns G R HR) a = R ttt ttt (deloop_arr a) (@id (grp_deloop G) ttt)
  := eq_refl.

(** ** The two maps are mutually inverse *)

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma ns_of_cong_of_ns {G : GrpObject} (N : NormalSubgroup G) (a : carrier G) :
  sub_mem (@cong_ns G (ns_rel N) (ns_congruence N)) a ↔ sub_mem N a.
Proof. exact (quot_rel_unit_iff N a). Qed.

(*
   本节说明 Congruence 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma cong_of_ns_of_cong {G : GrpObject} (R : HomRelT (grp_deloop G))
  `{HR : @HomCongruence (grp_deloop G) R}
  (x y : grp_deloop G) (f g : carrier G) :
  ns_rel (@cong_ns G R HR) x y f g ↔ R x y f g.
Proof.
  destruct x, y; split; intro K.
  - refine (@cong_trans (grp_deloop G) R HR ttt ttt (deloop_arr f)
              (deloop_arr (grp_mul G f (grp_inv G g)) ∘ deloop_arr g)
              (deloop_arr g) _ _).
    + apply cong_incl; simpl.
      rewrite (grp_mul_assoc G f (grp_inv G g) g),
              (grp_mul_inv_l G g), (grp_mul_unit_r G f).
      reflexivity.
    + refine (@cong_trans (grp_deloop G) R HR ttt ttt _
                (id ∘ deloop_arr g) _ _ _).
      * exact (@cong_comp (grp_deloop G) R HR ttt ttt ttt
                 (deloop_arr (grp_mul G f (grp_inv G g))) id
                 (deloop_arr g) (deloop_arr g) K (cong_refl _)).
      * apply cong_incl; apply id_left.
  - refine (@cong_trans (grp_deloop G) R HR ttt ttt _
              (deloop_arr g ∘ deloop_arr (grp_inv G g)) id _ _).
    + exact (@cong_comp (grp_deloop G) R HR ttt ttt ttt
               (deloop_arr f) (deloop_arr g)
               (deloop_arr (grp_inv G g)) (deloop_arr (grp_inv G g))
               K (cong_refl _)).
    + apply cong_incl; exact (grp_mul_inv_r G g).
Qed.

(*
   本节说明 Congruence 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Packaging.

Context {G : GrpObject}.

(** A congruence, as data: the relation together with its four laws. *)
Definition CongData : Type :=
  { R : HomRelT (grp_deloop G) & HomCongruence R }.

Program Definition NS_Setoid : SetoidObject := {|
  carrier := NormalSubgroup G;
  is_setoid := {| equiv := fun N M =>
    (∀ a : carrier G, sub_mem N a → sub_mem M a)
      * (∀ a : carrier G, sub_mem M a → sub_mem N a) |}
|}.
Next Obligation.
  constructor.
  - intro N; split; intros a Ha; exact Ha.
  - intros N M [H1 H2]; split; assumption.
  - intros N M P [H1 H2] [H3 H4]; split; intros a Ha; auto.
Qed.

Program Definition Cong_Setoid : SetoidObject := {|
  carrier := CongData;
  is_setoid := {| equiv := fun R S =>
    ∀ (x y : grp_deloop G) (f g : x ~> y),
      (`1 R x y f g → `1 S x y f g) * (`1 S x y f g → `1 R x y f g) |}
|}.
Next Obligation.
  constructor.
  - intros R x y f g; split; intro K; exact K.
  - intros R S H x y f g; destruct (H x y f g); split; assumption.
  - intros R S T H1 H2 x y f g.
    destruct (H1 x y f g), (H2 x y f g); split; auto.
Qed.

Program Definition ns_to_cong : NS_Setoid ~{Sets}~> Cong_Setoid := {|
  morphism := fun N => existT _ (ns_rel N) (ns_congruence N)
|}.
Next Obligation.
  intros N M [H1 H2] x y f g; simpl; split; intro K.
  - exact (H1 _ K).
  - exact (H2 _ K).
Qed.

Program Definition cong_to_ns : Cong_Setoid ~{Sets}~> NS_Setoid := {|
  morphism := fun R => @cong_ns G (`1 R) (`2 R)
|}.
Next Obligation.
  intros R S H; simpl; split; intros a Ha.
  - exact (fst (H ttt ttt a (@id (grp_deloop G) ttt)) Ha).
  - exact (snd (H ttt ttt a (@id (grp_deloop G) ttt)) Ha).
Qed.

(** Mac Lane §II.8 Exercise 2, as a bijection: the normal subgroups of G
    are the congruences on its delooping. *)
Program Definition ns_cong_iso : NS_Setoid ≅[Sets] Cong_Setoid := {|
  to := ns_to_cong;
  from := cong_to_ns
|}.
Next Obligation.
  intros R x y f g; simpl.
  destruct x, y.
  exact (@cong_of_ns_of_cong G (`1 R) (`2 R) ttt ttt f g).
Qed.
Next Obligation.
  intros N; simpl; split; intros a Ha.
  - exact (fst (ns_of_cong_of_ns N a) Ha).
  - exact (snd (ns_of_cong_of_ns N a) Ha).
Qed.

End Packaging.

(*
   本节说明 Congruence 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition congruence_normal_subgroup (G : GrpObject)
  : @NS_Setoid G ≅[Sets] @Cong_Setoid G := @ns_cong_iso G.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Necessity.

Context {G : GrpObject}.
Context (S : Subgroup G).

Definition sub_rel : HomRelT (grp_deloop G) := fun _ _ f g => quot_rel S f g.

(*
   本节说明 Congruence 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sub_rel_unit_iff (a : carrier G) :
  quot_rel S a (grp_unit G) ↔ sub_mem S a.
Proof.
  split; intro K; unfold quot_rel in *.
  - apply (sub_at S (a := grp_mul G a (grp_inv G (grp_unit G)))); [| exact K ].
    rewrite (grp_inv_unit G); apply (grp_mul_unit_r G).
  - apply (sub_at S (a := a)); [| exact K ].
    rewrite (grp_inv_unit G); symmetry; apply (grp_mul_unit_r G).
Qed.

Lemma sub_rel_congruence_normal `{HR : @HomCongruence (grp_deloop G) sub_rel} :
  ∀ t a : carrier G, sub_mem S a →
    sub_mem S (grp_mul G (grp_mul G t a) (grp_inv G t)).
Proof.
  intros t a Ha.
  apply (fst (sub_rel_unit_iff _)).
  exact (@ns_conj G (@cong_ns G sub_rel HR) t a
           (snd (sub_rel_unit_iff a) Ha)).
Qed.

End Necessity.

(*
   本节说明 Congruence 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem congruence_iff_normal {G : GrpObject} (S : Subgroup G) :
  (@HomCongruence (grp_deloop G) (sub_rel S))
    ↔ (∀ t a : carrier G, sub_mem S a →
         sub_mem S (grp_mul G (grp_mul G t a) (grp_inv G t))).
Proof.
  split.
  - intro HR; exact (@sub_rel_congruence_normal G S HR).
  - intro Hn.
    exact (ns_congruence (@Build_NormalSubgroup G S Hn)).
Qed.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Corollary.

Context {G : GrpObject}.
Context (N : NormalSubgroup G).

Definition quot_to_deloop : deloop_quotient N ⟶ grp_deloop (QuotientGrp N) :=
  Build_Functor (deloop_quotient N) (grp_deloop (QuotientGrp N))
    (fun x => x)
    (fun x y f => f)
    (fun x y f g H => H)
    (fun x => inhabits (quot_rel_refl N _))
    (fun x y z f g => inhabits (quot_rel_refl N _)).

Definition deloop_to_quot : grp_deloop (QuotientGrp N) ⟶ deloop_quotient N :=
  Build_Functor (grp_deloop (QuotientGrp N)) (deloop_quotient N)
    (fun x => x)
    (fun x y f => f)
    (fun x y f g H => H)
    (fun x => inhabits (quot_rel_refl N _))
    (fun x y z f g => inhabits (quot_rel_refl N _)).

(** Both functors are the identity on objects and on arrows, so both round
    trips have [eq_refl] object components. *)
Lemma deloop_quotient_round_to :
  @equiv _ (@Functor_StrictEq_Setoid (deloop_quotient N) (deloop_quotient N))
    (deloop_to_quot ◯ quot_to_deloop) (Id[deloop_quotient N]).
Proof.
  exists (fun _ => eq_refl); intros x y f; simpl;
    constructor; apply quot_rel_refl.
Qed.

Lemma deloop_quotient_round_from :
  @equiv _ (@Functor_StrictEq_Setoid (grp_deloop (QuotientGrp N))
              (grp_deloop (QuotientGrp N)))
    (quot_to_deloop ◯ deloop_to_quot) (Id[grp_deloop (QuotientGrp N)]).
Proof.
  exists (fun _ => eq_refl); intros x y f; simpl;
    constructor; apply quot_rel_refl.
Qed.

Definition deloop_quotient_iso
  : deloop_quotient N ≅[StrictCat] grp_deloop (QuotientGrp N) :=
  @Build_Isomorphism StrictCat (deloop_quotient N) (grp_deloop (QuotientGrp N))
    quot_to_deloop deloop_to_quot
    deloop_quotient_round_from deloop_quotient_round_to.

(** The weaker [Cat] reading, derived.  [≅[Cat]] IS equivalence of
    categories here; the [StrictCat] statement above is the strong one. *)
Definition deloop_quotient_Cat_iso
  : deloop_quotient N ≅[Cat] grp_deloop (QuotientGrp N) :=
  @Build_Isomorphism Cat (deloop_quotient N) (grp_deloop (QuotientGrp N))
    quot_to_deloop deloop_to_quot
    (strict_equiv_implies_fun_equiv _ _ deloop_quotient_round_from)
    (strict_equiv_implies_fun_equiv _ _ deloop_quotient_round_to).

End Corollary.

(** ** Group homomorphisms as functors between deloopings *)

Section Homomorphisms.

Context {G K : GrpObject}.

(** A group homomorphism is a monoid homomorphism of the delooped
    monoids: unit and product preservation are its two fields, and
    respectfulness is the underlying setoid morphism's. *)
Definition hom_MonHom (h : G ~{Grp}~> K)
  : MonHom (grp_deloop_monoid G) (grp_deloop_monoid K) :=
  @Build_MonHom (grp_deloop_monoid G) (grp_deloop_monoid K)
    (grp_map h) (proper_morphism (grp_map h))
    (grp_map_unit h) (grp_map_mul h).

(** ...hence a functor, by [Construction/Deloop/Transform.v]'s
    [Deloop_map]; nothing here is new, and the action on arrows is the
    homomorphism's action on elements by convertibility. *)
Definition deloop_hom (h : G ~{Grp}~> K) : grp_deloop G ⟶ grp_deloop K :=
  Deloop_map (hom_MonHom h).

Example deloop_hom_fmap (h : G ~{Grp}~> K) (a : carrier G) :
  @fmap _ _ (deloop_hom h) ttt ttt a = grp_map h a := eq_refl.

End Homomorphisms.

(*
   本节说明函子、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Kernel.

Context {G K : GrpObject}.
Context (h : G ~{Grp}~> K).

Definition kernel_cong : HomRelT (grp_deloop G) := FunctorKernel (deloop_hom h).

Definition kernel_ns : NormalSubgroup G :=
  @cong_ns G kernel_cong (FunctorKernel_Congruence (deloop_hom h)).

Lemma kernel_ns_iff (a : carrier G) :
  sub_mem kernel_ns a ↔ sub_mem (KernelNS h) a.
Proof.
  simpl; unfold cong_mem, kernel_cong, FunctorKernel; simpl.
  split; intro K'.
  - rewrite K'; apply (grp_map_unit h).
  - rewrite K'; symmetry; apply (grp_map_unit h).
Qed.

(** Hence the two quotients agree, through #313's own comparison. *)
Definition kernel_quot_congr
  : QuotientGrp kernel_ns ≅[Grp] QuotientGrp (KernelNS h) :=
  quot_congr kernel_ns (KernelNS h)
    (fun a => fst (kernel_ns_iff a)) (fun a => snd (kernel_ns_iff a)).

(*
   本节说明函子、等价、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma kernel_cong_iff (f g : carrier G) :
  ns_rel (KernelNS h) ttt ttt f g ↔ kernel_cong ttt ttt f g.
Proof.
  unfold kernel_cong, FunctorKernel, ns_rel, quot_rel; simpl.
  split; intro K'.
  - apply (grp_cancel_r K (grp_inv K (grp_map h g))).
    rewrite (grp_mul_inv_r K (grp_map h g)).
    rewrite <- (grp_map_inv h g).
    rewrite <- (grp_map_mul h).
    exact K'.
  - rewrite (grp_map_mul h), (grp_map_inv h), K'.
    apply (grp_mul_inv_r K).
Qed.

End Kernel.

(*
   本节说明函子、（余）强度相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Specialization.

Context {G K : GrpObject}.
Context (N : NormalSubgroup G).
Context (p : Kills N K).

(** The hypothesis of the categorical theorem, discharged by #313's
    descent lemma with no reshaping.  It is stated over the UNTRUNCATED
    [ns_rel], which is what #313's descent lemma proves. *)
Definition deloop_kills
  : ∀ x y (f g : x ~{grp_deloop G}~> y), ns_rel N x y f g →
      fmap[deloop_hom (`1 p)] f ≈ fmap[deloop_hom (`1 p)] g :=
  fun x y f g H => kills_descends N p f g H.

(*
   本节说明 Congruence 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition deloop_pkills
  : ∀ x y (f g : x ~{grp_deloop G}~> y), ns_prel N x y f g →
      fmap[deloop_hom (`1 p)] f ≈ fmap[deloop_hom (`1 p)] g.
Proof.
  intros x y f g H.
  apply (@pequiv_to _ _ (grp_prop K)).
  unfold ns_prel, quot_equiv in H; destruct H as [h].
  apply (@pequiv_from _ _ (grp_prop K)).
  exact (deloop_kills x y f g h).
Defined.

Definition cat_lift : deloop_quotient N ⟶ grp_deloop K :=
  @QuotientLift (grp_deloop G) (ns_prel N) (ns_prel_congruence N)
    (grp_deloop K) (deloop_hom (`1 p)) deloop_pkills.

(*
   本节说明函子、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition cat_med : QuotientGrp N ~{Grp}~> K :=
  @Build_GrpHom' (QuotientGrp N) K
    {| morphism := fun a =>
         @fmap _ _ (cat_lift ◯ deloop_to_quot N) ttt ttt a
     ; proper_morphism :=
         @fmap_respects _ _ (cat_lift ◯ deloop_to_quot N) ttt ttt |}
    (fun a b => @fmap_comp _ _ (cat_lift ◯ deloop_to_quot N) ttt ttt ttt a b).

(*
   本节说明 Congruence 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example cat_med_is_quot_med (a : carrier (QuotientGrp N)) :
  grp_map cat_med a = grp_map (quot_med N p) a := eq_refl.

(** Awodey §4.5 Exercise 1.  The existence half is [QuotientLift]; the
    uniqueness half is [QuotientLift_unique], applied at the delooping's
    single object.  No group-level uniqueness argument is written. *)
Definition hom_theorem_via_quotient_category
  : ∃! u : QuotientGrp N ~{Grp}~> K, u ∘ quot_proj N ≈ `1 p.
Proof.
  unshelve refine {| unique_obj := cat_med |}.
  - intro a; simpl; reflexivity.
  - intros v Hv a.
    exact (symmetry
             (@QuotientLift_unique (grp_deloop G) (ns_prel N)
                (ns_prel_congruence N)
                (grp_deloop K) (deloop_hom (`1 p)) deloop_pkills
                (deloop_hom v ◯ quot_to_deloop N)
                (fun _ => eq_refl)
                (fun x y f => Hv f)
                ttt ttt a)).
Defined.

Example hom_theorem_via_quotient_category_obj (a : carrier (QuotientGrp N)) :
  grp_map (unique_obj hom_theorem_via_quotient_category) a
    = grp_map (quot_med N p) a := eq_refl.

End Specialization.

(*
   本节说明 Congruence 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition hom_theorem_from_category {G K : GrpObject} (N : NormalSubgroup G)
  (h : G ~{Grp}~> K)
  (Hkill : ∀ a : carrier G, sub_mem N a → grp_map h a ≈ grp_unit K) :
  ∃! u : QuotientGrp N ~{Grp}~> K, u ∘ quot_proj N ≈ h :=
  hom_theorem_via_quotient_category N (existT _ h Hkill).

(*
   本节说明函子、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example deloop_proj_fmap {G : GrpObject} (N : NormalSubgroup G) (a : carrier G) :
  @fmap _ _ (quot_to_deloop N ◯ deloop_quotient_proj N) ttt ttt a
    = @fmap _ _ (deloop_hom (quot_proj N)) ttt ttt a := eq_refl.

Lemma deloop_proj_fobj {G : GrpObject} (N : NormalSubgroup G)
  (x : grp_deloop G) :
  fobj[quot_to_deloop N ◯ deloop_quotient_proj N] x
    = fobj[deloop_hom (quot_proj N)] x.
Proof. destruct x; reflexivity. Qed.

(*
   本节说明 Congruence 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** The congruence merges: the rotation is related to the identity arrow
    (which is [s3_unit], since [grp_unit S3 = s3_unit] and
    [deloop_id_is_unit] holds by [eq_refl]). *)
Example A3_relates_rotation : ns_rel A3 ttt ttt S3_r s3_unit := eq_refl.

(** ...and separates: the reflection is not. *)
Theorem A3_separates_reflection : ns_rel A3 ttt ttt S3_s s3_unit → False.
Proof. simpl; discriminate. Qed.

(** So the projection functor is not faithful -- which is the whole point
    of a quotient category, and Fong and Spivak's "equations merge, never
    add" read at one object. *)
Theorem A3_proj_not_faithful :
  (∀ (x y : grp_deloop S3) (f g : x ~> y),
     ns_rel A3 x y f g → f ≈ g) → False.
Proof.
  intro Hf.
  pose proof (Hf ttt ttt S3_r s3_unit A3_relates_rotation) as E.
  discriminate E.
Qed.

(*
   本节说明 Congruence 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition coset_witness : carrier S3 := grp_mul S3 S3_s S3_r.

Example coset_right : sub_mem S3_refl_sub
  (grp_mul S3 coset_witness (grp_inv S3 S3_r)) := eq_refl.

Theorem coset_orientations_differ :
  sub_mem S3_refl_sub (grp_mul S3 (grp_inv S3 S3_r) coset_witness) → False.
Proof. simpl; discriminate. Qed.

(*
   本节说明 Congruence 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem S3_refl_sub_no_congruence :
  @HomCongruence (grp_deloop S3) (sub_rel S3_refl_sub) → False.
Proof.
  intro HR.
  exact (S3_refl_sub_not_normal
           (fst (congruence_iff_normal S3_refl_sub) HR)).
Qed.

(** The recovered normal subgroup of A3's congruence has A3's members,
    at the concrete witness: both directions, computed. *)
Example A3_round_forward :
  sub_mem (@cong_ns S3 (ns_rel A3) (ns_congruence A3)) S3_r := eq_refl.

Theorem A3_round_backward :
  sub_mem (@cong_ns S3 (ns_rel A3) (ns_congruence A3)) S3_s → False.
Proof. simpl; discriminate. Qed.
