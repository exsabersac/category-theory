Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.EckmannHilton.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * 范畴的中心 *)

(* nLab:      https://ncatlab.org/nlab/show/center+of+a+category
   nLab:      https://ncatlab.org/nlab/show/Eckmann-Hilton+argument

   范畴的中心 (center) 收集与一切态射交换的自同态（或相关的自然变换数据）。本文件在
   setoid 设定下给出中心对象/幺半群结构，并与 Eckmann–Hilton 论证的零元阴影相联系
   （见 Theory/EckmannHilton.v）。文内其它长注释后续可续译。 *)

(*
   本节说明相关定义、性质与动机。 Why this is arity-zero shadow Eckmann–Hilton. nLab: https://ncatlab.org/nlab/show/Eckmann-Hilton+argument nLab: https://ncatlab.org/nlab/show/center+of+a+范畴 Paper: Eckmann, Hilton, "Group-like structures 一般地 范畴 I", Mathematische Annalen 145, 1962 Read

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明相关定义、性质与动机。 THREE DIFFERENT THINGS ARE CALLED A CENTRE. All three are this tree,. they are three different KINDS. Naming them together once is cheaper than disambiguating them repeatedly downstream.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The centre as a setoid and as a monoid *)

Section Centre.

Context {C : Category}.

(*
   The carrier: the hom-setoid of the 函子 范畴 `[C, C]` at the

   本节：identity 函子. This is categorical home centre — 对象 `[C, C]` are 函子 its 态射 are 自然变换 (Instance/Fun.v), so `Id[C] ~{[C, C]}~> Id[C]` is `Id[C] ⟹ Id[C]` setoid is [Transform_Setoid], comparing two transformations

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition centre_setoid : SetoidObject := {|
  carrier   := @hom ([C, C]) Id[C] Id[C];
  is_setoid := @homset ([C, C]) Id[C] Id[C]
|}.

(*
   The 幺半群 structure needs no proof: it is Construction/Deloop.v's

   本节说明相关定义、性质与动机。 endomorphism 幺半群 对象 Id[C] 范畴 `[C, C]`.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition centre_monoid : MonObject := hom_monoid ([C, C]) Id[C].

(* The three data fields, definitionally.  [Set Primitive Projections] gives
   record eta, so the carrier equation is an equation of records. *)

Example centre_monoid_setoid : mon_setoid centre_monoid = centre_setoid
  := eq_refl.

Example centre_monoid_carrier :
  carrier centre_monoid = (Id[C] ⟹ Id[C]) := eq_refl.

Example centre_monoid_unit :
  @mon_unit centre_monoid = @nat_id C C Id[C] := eq_refl.

Example centre_monoid_op :
  @mon_op centre_monoid = @nat_compose C C Id[C] Id[C] Id[C] := eq_refl.

(** ** Commutativity, directly from naturality *)

(*
   The whole content of the exercise, at a single 对象.  Read α's

   本节说明相关定义、性质与动机。 naturality square at 态射 `transform[β] x : x ~> x`; because `fmap[Id]` is definitionally identity 态射, square is already commutation.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma centre_commutes_at (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[α] x ∘ transform[β] x ≈ transform[β] x ∘ transform[α] x.
Proof.
  symmetry.
  exact (naturality[α] x x (transform[β] x)).
Qed.

(*
   The centre is a COMMUTATIVE 幺半群: vertical 复合 of 自然

   本节说明相关定义、性质与动机。 endotransformations identity 函子 is commutative. This is pinned constant Mac Lane §II.5 Exercise 8 / Riehl Exercise 1.7.iv.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem centre_commutative (α β : Id[C] ⟹ Id[C]) :
  nat_compose α β ≈[Fun] nat_compose β α.
Proof.
  intro x.
  exact (centre_commutes_at α β x).
Qed.

(* The same statement read through the monoid packaging, so that a consumer
   holding [centre_monoid] can quote commutativity in the monoid's own
   vocabulary. *)
Corollary centre_monoid_commutative (α β : carrier centre_monoid) :
  mon_op α β ≈ mon_op β α.
Proof. exact (centre_commutative α β). Qed.

End Centre.

(** ** The Eckmann–Hilton packaging *)

(*
   本节说明相关定义、性质与动机。 The traditional route: exhibit two unital operations that interchange and. invoke Theory/EckmannHilton.v. Everything 本节 is honest about being consistency exhibit rather than independent derivation;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section CentreEH.

Context {C : Category}.

(*
   The first operation is vertical 复合.  The second is the SAME

   本节说明相关定义、性质与动机。 复合 its arguments swapped — which, [centre_vcomp_op_is_hcompose] below, is exactly Godement horizontal 复合 other order, two agreeing components at identity 函子.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition centre_vcomp (α β : Id[C] ⟹ Id[C]) : Id[C] ⟹ Id[C] :=
  nat_compose α β.

Definition centre_vcomp_op (α β : Id[C] ⟹ Id[C]) : Id[C] ⟹ Id[C] :=
  nat_compose β α.

(* Components, definitionally: `f` composes in the given order, `g` in the
   opposite one. *)

Example centre_vcomp_component (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[centre_vcomp α β] x = transform[α] x ∘ transform[β] x := eq_refl.

Example centre_vcomp_op_component (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[centre_vcomp_op α β] x = transform[β] x ∘ transform[α] x
  := eq_refl.

(** *** The second operation IS the horizontal composite, componentwise *)

(*
   本节说明相关定义、性质与动机。 [nat_hcompose ε η : J ◯ F ⟹ K ◯ G] lands at `Id ◯ Id`, not at `Id`, so. two transformations do not have same TYPE no equation between them can be written without transport.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example centre_hcompose_is_vcomp (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[nat_hcompose α β] x = transform[nat_compose α β] x := eq_refl.

Example centre_vcomp_op_is_hcompose (α β : Id[C] ⟹ Id[C]) (x : C) :
  transform[centre_vcomp_op α β] x = transform[nat_hcompose β α] x := eq_refl.

(* Both whiskerings against the identity functor are the identity on
   components, which is the other half of the same observation. *)

Example centre_whisker_left (α : Id[C] ⟹ Id[C]) (x : C) :
  transform[Id[C] ⊳ α] x = transform[α] x := eq_refl.

Example centre_whisker_right (α : Id[C] ⟹ Id[C]) (x : C) :
  transform[α ⊲ Id[C]] x = transform[α] x := eq_refl.

(** *** The seven hypotheses of [eh_comm] *)

(* Respectfulness: both operations are [nat_compose] up to argument order,
   so both are [nat_compose_respects] (the second with its two arguments
   exchanged). *)

Definition centre_vcomp_respects :
  Proper (equiv ==> equiv ==> equiv) centre_vcomp.
Proof. repeat intro; now apply nat_compose_respects. Qed.

Definition centre_vcomp_op_respects :
  Proper (equiv ==> equiv ==> equiv) centre_vcomp_op.
Proof. repeat intro; now apply nat_compose_respects. Qed.

(*
   The four 单位律.  Both operations take [nat_id] as a two-sided unit —

   本节说明相关定义、性质与动机。 this is coincidence units that makes Eckmann–Hilton argument applicable at all, here it is not accident construction but fact that both operations ARE vertical 复合.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition centre_vcomp_unit_l (α : Id[C] ⟹ Id[C]) :
  centre_vcomp nat_id α ≈[Fun] α := nat_id_left C C Id[C] Id[C] α.

Definition centre_vcomp_unit_r (α : Id[C] ⟹ Id[C]) :
  centre_vcomp α nat_id ≈[Fun] α := nat_id_right C C Id[C] Id[C] α.

Definition centre_vcomp_op_unit_l (α : Id[C] ⟹ Id[C]) :
  centre_vcomp_op nat_id α ≈[Fun] α := nat_id_right C C Id[C] Id[C] α.

Definition centre_vcomp_op_unit_r (α : Id[C] ⟹ Id[C]) :
  centre_vcomp_op α nat_id ≈[Fun] α := nat_id_left C C Id[C] Id[C] α.

(*
   本节说明相关定义、性质与动机。 The interchange law, orientation Theory/EckmannHilton.v states it:. `f (g b) (g c d) ≈ g (f c) (f b d)`. 分量地 goal is `(b ∘ a) ∘ (d ∘ c) ≈ (b ∘ d) ∘ (a ∘ c)`;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma centre_interchange (a b c d : Id[C] ⟹ Id[C]) :
  centre_vcomp (centre_vcomp_op a b) (centre_vcomp_op c d)
    ≈[Fun] centre_vcomp_op (centre_vcomp a c) (centre_vcomp b d).
Proof.
  intro x.
  simpl.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity |].
  rewrite !comp_assoc.
  apply compose_respects; [| reflexivity].
  exact (centre_commutes_at a d x).
Qed.

(** *** Commutativity via [eh_comm] *)

(* All seven hypotheses discharged, the abstract argument applied.  The
   conclusion is [centre_commutative] again, reached the long way. *)
Theorem centre_commutative_EH (α β : Id[C] ⟹ Id[C]) :
  centre_vcomp α β ≈[Fun] centre_vcomp β α.
Proof.
  exact (eh_comm centre_vcomp centre_vcomp_op nat_id nat_id
           centre_vcomp_respects centre_vcomp_op_respects
           centre_vcomp_unit_l centre_vcomp_unit_r
           centre_vcomp_op_unit_l centre_vcomp_op_unit_r
           centre_interchange α β).
Qed.

(*
   本节说明相关定义、性质与动机。 [eh_ops] — Eckmann–Hilton conclusion that two operations. COINCIDE — degenerates here into commutativity second time, since second operation is first its arguments swapped.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary centre_EH_ops (α β : Id[C] ⟹ Id[C]) :
  centre_vcomp α β ≈[Fun] centre_vcomp_op α β.
Proof.
  exact (eh_ops centre_vcomp centre_vcomp_op nat_id nat_id
           centre_vcomp_respects centre_vcomp_op_respects
           centre_vcomp_unit_l centre_vcomp_unit_r
           centre_vcomp_op_unit_l centre_vcomp_op_unit_r
           centre_interchange α β).
Qed.

(*
   本节说明相关定义、性质与动机。 Likewise [eh_units]: two units coincide. Here they were literally.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary centre_EH_units : (nat_id : Id[C] ⟹ Id[C]) ≈[Fun] nat_id.
Proof.
  exact (eh_units centre_vcomp centre_vcomp_op nat_id nat_id
           centre_vcomp_respects centre_vcomp_op_respects
           centre_vcomp_unit_l centre_vcomp_unit_r
           centre_vcomp_op_unit_l centre_vcomp_op_unit_r
           centre_interchange).
Qed.

(** *** Why the EH route cannot be independent *)

(*
   本节说明相关定义、性质与动机。 The claim, machine-checked. Take interchange law HYPOTHESIS —. not proved [centre_interchange], but any statement that shape — instantiate its second third arguments at [nat_id].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem centre_interchange_forces_commutative
  (inter : ∀ a b c d : Id[C] ⟹ Id[C],
      centre_vcomp (centre_vcomp_op a b) (centre_vcomp_op c d)
        ≈[Fun] centre_vcomp_op (centre_vcomp a c) (centre_vcomp b d))
  (α δ : Id[C] ⟹ Id[C]) :
  centre_vcomp α δ ≈[Fun] centre_vcomp δ α.
Proof.
  (*
   本节说明相关定义、性质与动机。 Instantiate at (α, 1, 1, δ), writing 1 [nat_id]:. f (g α 1) (g 1 δ) ≈ g (f α 1) (f 1 δ). 分量地 即 `(1 ∘ α x) ∘ (δ x ∘ 1) ≈ (1 ∘ δ x) ∘ (α x ∘ 1)`, cancelling four units leaves `α x ∘ δ x ≈ δ x ∘ α x`, which is goal.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  specialize (inter α nat_id nat_id δ).
  intro x.
  specialize (inter x).
  simpl in *.
  rewrite !id_left, !id_right in inter.
  exact inter.
Qed.

End CentreEH.

(** ** The centre of Sets is trivial *)

(*
   本节说明相关定义、性质与动机。 Mac Lane asks centre Set. The probe is standard one: a. point setoid X is same thing 态射 into X from singleton, naturality α at that 态射 pins α's component at X identity.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明相关定义、性质与动机。 The singleton setoid used probe's domain is carrier of. [Sets_Terminal] (Instance/Sets.v), [poly_unit] under `=`. UNIVERSE ANNOTATION, why it is not decoration. `Sets@{o so}` has carriers at `o` 对象 at `so` (Instance/Sets.v).

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition centre_Sets_point@{o so} {X : obj[Sets@{o so}]}
  (x : carrier X) :
  ({| carrier := poly_unit@{o} |} : obj[Sets@{o so}]) ~{Sets@{o so}}~> X := {|
  morphism := fun _ => x
|}.

(*
   本节说明相关定义、性质与动机。 The probe's underlying function is given literally, so it computes; the. [Program] wrapper touches only respectfulness certificate.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example centre_Sets_point_computes@{o so} {X : obj[Sets@{o so}]}
  (x : carrier X) (u : poly_unit@{o}) : centre_Sets_point x u = x := eq_refl.

(* Pointwise form: every centre element of `Sets` acts as the identity on
   every point of every setoid. *)
Theorem centre_Sets_trivial@{o so} (α : Id[Sets@{o so}] ⟹ Id[Sets@{o so}])
  (X : obj[Sets@{o so}]) (x : carrier X) : transform[α] X x ≈ x.
Proof.
  symmetry.
  exact (naturality[α] ({| carrier := poly_unit@{o} |} : obj[Sets@{o so}]) X
           (centre_Sets_point x) ttt).
Qed.

(* Packaged form: every centre element of `Sets` IS the identity
   transformation, in the hom-setoid of `[Sets, Sets]`. *)
Corollary centre_Sets_trivial_nat@{o so}
  (α : Id[Sets@{o so}] ⟹ Id[Sets@{o so}]) : α ≈[Fun] nat_id.
Proof.
  intros X x.
  simpl.
  apply centre_Sets_trivial.
Qed.

(* Hence the centre of `Sets` is a singleton: it is the trivial monoid. *)
Corollary centre_Sets_subsingleton@{o so}
  (α β : Id[Sets@{o so}] ⟹ Id[Sets@{o so}]) : α ≈[Fun] β.
Proof.
  transitivity (@nat_id Sets@{o so} Sets@{o so} Id[Sets@{o so}]).
  - apply centre_Sets_trivial_nat.
  - symmetry; apply centre_Sets_trivial_nat.
Qed.

(** ** The centre of Coq is trivial *)

(*
   本节说明相关定义、性质与动机。 The same probe over Instance/Coq.v, where hom-setoid is pointwise. Leibniz equality (Instance/Coq.v), so conclusion is equation rather than `≈`.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem centre_Coq_trivial (α : Id[Coq] ⟹ Id[Coq])
  (X : obj[Coq]) (x : X) : transform[α] X x = x.
Proof.
  symmetry.
  exact (naturality[α] poly_unit X (fun _ => x) ttt).
Qed.

Corollary centre_Coq_trivial_nat (α : Id[Coq] ⟹ Id[Coq]) :
  α ≈[Fun] nat_id.
Proof.
  intros X x.
  simpl.
  apply centre_Coq_trivial.
Qed.
