Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Instance.Sets.Pushout.

Generalizable All Variables.

(* * * Quotient 对象 setoid: witness half Mac Lane §V.7
 Definition 3 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/quotient+set
 nLab:      https://ncatlab.org/nlab/show/coimage
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_object

   本文件给出集合范畴相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section SetsQuotObj.

Universe o so.
Constraint o < so.

(* 相关说明。 （已译） *)

(*
   本节说明 QuotObj 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_quot_epi_surjective {X : SetoidObject@{o o}}
  (q : @QuotObj Sets@{o so} X) :
  ∀ b : carrier (quot_cod q), ∃ a : carrier X, quot_epi q a ≈ b :=
  fun b => epic_implies_surjective (quot_epi q) (quot_is_epic q) b.

(* ... conversely every surjection setoids presents quotient
 对象, forward leg [mk_quot]. （已译） *)
Definition Sets_quot_of_surjection {X B : SetoidObject@{o o}}
  (h : X ~{Sets@{o so}}~> B)
  (Hs : ∀ b : carrier B, ∃ a : carrier X, h a ≈ b) :
  @QuotObj Sets@{o so} X :=
  mk_quot h (surjective_implies_epic h Hs).

(* * ** The quotient setoid 等价 关系, a
 quotient 对象 （已译） *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SetsQuotient_QuotObj (A : SetoidObject@{o o})
  (R : crelation (carrier A)) (HR : Equivalence R) (HC : SetoidCoarser R) :
  @QuotObj Sets@{o so} A :=
  Sets_quot_of_surjection (sets_quot_proj A R HR HC)
    (fun b => (b; @Equivalence_Reflexive _ R HR b)).

(** ** The coimage of a setoid map *)

Section Coimage.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(*
   本节说明拉回/推出、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sets_coimage_rel : crelation (carrier X) := fun a b => f a ≈ f b.

Lemma sets_coimage_rel_Equivalence : Equivalence sets_coimage_rel.
Proof.
  constructor; unfold sets_coimage_rel.
  - intro a; reflexivity.
  - intros a b H; now symmetry.
  - intros a b c H1 H2; now transitivity (f b).
Qed.

(* Coarser than `≈` because f is a setoid map: this IS [proper_morphism]. *)
Definition sets_coimage_rel_coarser : SetoidCoarser sets_coimage_rel :=
  fun a b H => proper_morphism f a b H.

Definition Sets_coimage : @QuotObj Sets@{o so} X :=
  SetsQuotient_QuotObj X sets_coimage_rel sets_coimage_rel_Equivalence
    sets_coimage_rel_coarser.

(* f itself respects own kernel 关系, IDENTITY
 implication, so descended map [sets_quot_med] at witness. （已译） *)
Definition sets_coimage_resp : RespMap sets_coimage_rel Y :=
  existT (SetsRespects sets_coimage_rel Y) f
    (fun a b (H : sets_coimage_rel a b) => H).

Definition sets_coimage_factor :
  Y ~{Sets@{o so}^op}~> quot_cod Sets_coimage :=
  sets_quot_med sets_coimage_rel sets_coimage_rel_Equivalence
    sets_coimage_resp.

(*
   本节说明 QuotObj 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma sets_coimage_commutes :
  sub_mono Sets_coimage ∘[Sets@{o so}^op] sets_coimage_factor ≈ f.
Proof. intro a; simpl; reflexivity. Qed.

(*
   本节说明 QuotObj 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sets_coimage_pick (w : @QuotObj Sets@{o so} X)
  (p : carrier (quot_cod w)) : carrier X :=
  `1 (Sets_quot_epi_surjective w p).

Lemma sets_coimage_pick_eq (w : @QuotObj Sets@{o so} X)
  (p : carrier (quot_cod w)) :
  quot_epi w (sets_coimage_pick w p) ≈ p.
Proof. exact (`2 (Sets_quot_epi_surjective w p)). Qed.

(* 相关说明。 （已译） *)
Definition sets_coimage_med (w : @QuotObj Sets@{o so} X)
  (g : Y ~{Sets@{o so}^op}~> quot_cod w)
  (Hg : sub_mono w ∘[Sets@{o so}^op] g ≈ f) :
  quot_cod Sets_coimage ~{Sets@{o so}^op}~> quot_cod w.
Proof.
  unshelve refine {| morphism := sets_coimage_pick w |}.
  intros p q Hpq.
  change (f (sets_coimage_pick w p) ≈ f (sets_coimage_pick w q)).
  transitivity (g (quot_epi w (sets_coimage_pick w p))).
  - symmetry; exact (Hg _).
  - transitivity (g (quot_epi w (sets_coimage_pick w q))).
    + apply proper_morphism.
      rewrite !sets_coimage_pick_eq; exact Hpq.
    + exact (Hg _).
Defined.

Lemma sets_coimage_least (w : @QuotObj Sets@{o so} X)
  (g : Y ~{Sets@{o so}^op}~> quot_cod w)
  (Hg : sub_mono w ∘[Sets@{o so}^op] g ≈ f) :
  @sub_le (Sets@{o so}^op) X Sets_coimage w.
Proof.
  exists (sets_coimage_med w g Hg).
  intro a.
  change (f (sets_coimage_pick w (quot_epi w a)) ≈ f a).
  unfold sets_coimage_pick.
  transitivity
    (g (quot_epi w (`1 (Sets_quot_epi_surjective w (quot_epi w a))))).
  - symmetry; exact (Hg _).
  - transitivity (g (quot_epi w a)).
    + apply proper_morphism.
      exact (`2 (Sets_quot_epi_surjective w (quot_epi w a))).
    + exact (Hg a).
Qed.

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_CoimageOf : @ImageOf (Sets@{o so}^op) Y X f := {|
  im_sub := Sets_coimage;
  im_factor := sets_coimage_factor;
  im_commutes := sets_coimage_commutes;
  im_least := fun w g Hg => sets_coimage_least w g Hg
|}.

End Coimage.

(*
   本节说明 QuotObj 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance Sets_HasCoimages : @HasImages (Sets@{o so}^op) :=
  @Build_HasImages (Sets@{o so}^op) (fun Y X f => @Sets_CoimageOf X Y f).

(*
   本节说明子对象、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_quot_join {X : SetoidObject@{o o}}
  (q r : @QuotObj Sets@{o so} X) : @QuotObj Sets@{o so} X :=
  quot_join q r.

(* 相关说明。 （已译） *)

(*
   本节说明 QuotObj 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fixpoint nat_tri (n : nat) : nat :=
  match n with
  | O => 0
  | S O => 1
  | S (S O) => 2
  | S (S (S m)) => nat_tri m
  end.

Definition nat_mod3 : crelation (carrier NatDiscrete@{o}) :=
  fun m n => nat_tri m = nat_tri n.

Lemma nat_mod3_Equivalence : Equivalence nat_mod3.
Proof.
  constructor.
  - intro m; reflexivity.
  - intros m n H; now symmetry.
  - intros m n k H1 H2; now transitivity (nat_tri n).
Qed.

Definition nat_mod3_coarser : SetoidCoarser nat_mod3 :=
  fun m n (H : m = n) => f_equal nat_tri H.

(* The three quotient 对象 discrete setoid [nat]:
 Instance/Sets/Quotient.v's parity, residue mod 3, that
 file's total 关系. （已译） *)
Definition Sets_Q_parity : @QuotObj Sets@{o so} NatDiscrete@{o} :=
  SetsQuotient_QuotObj NatDiscrete@{o} nat_parity nat_parity_Equivalence
    nat_parity_coarser.

Definition Sets_Q_mod3 : @QuotObj Sets@{o so} NatDiscrete@{o} :=
  SetsQuotient_QuotObj NatDiscrete@{o} nat_mod3 nat_mod3_Equivalence
    nat_mod3_coarser.

Definition Sets_Q_total : @QuotObj Sets@{o so} NatDiscrete@{o} :=
  SetsQuotient_QuotObj NatDiscrete@{o} (TotalRelT NatDiscrete@{o})
    (TotalRelT_Equivalence NatDiscrete@{o})
    (TotalRelT_coarser NatDiscrete@{o}).

(*
   本节说明 QuotObj 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Sets_Q_total_below (w : @QuotObj Sets@{o so} NatDiscrete@{o}) :
  @sub_le (Sets@{o so}^op) NatDiscrete@{o} Sets_Q_total w.
Proof.
  unshelve eexists.
  - unshelve refine {| morphism := fun _ : carrier (quot_cod w) => 0%nat |}.
    intros p q Hpq; exact ttt.
  - intro a; exact ttt.
Defined.

(*
   本节说明 QuotObj 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma Sets_meet_collapse (v : @QuotObj Sets@{o so} NatDiscrete@{o})
  (H1 : @sub_le (Sets@{o so}^op) NatDiscrete@{o} v Sets_Q_parity)
  (H2 : @sub_le (Sets@{o so}^op) NatDiscrete@{o} v Sets_Q_mod3)
  (m n : nat) : quot_epi v m ≈ quot_epi v n.
Proof.
  destruct H1 as [k1 Hk1].
  destruct H2 as [k2 Hk2].
  assert (step : ∀ p : nat, quot_epi v p ≈ quot_epi v (S p)).
  { intro p.
    transitivity (k2 p); [ symmetry; exact (Hk2 p) | ].
    transitivity (k2 (S (S (S p)))).
    { exact (proper_morphism k2 p (S (S (S p)))
               (eq_refl : nat_tri p = nat_tri p)). }
    transitivity (quot_epi v (S (S (S p)))); [ exact (Hk2 _) | ].
    transitivity (k1 (S (S (S p)))); [ symmetry; exact (Hk1 _) | ].
    transitivity (k1 (S p)).
    { exact (proper_morphism k1 (S (S (S p))) (S p)
               (eq_refl : Nat.even (S p) = Nat.even (S p))). }
    exact (Hk1 _). }
  assert (zero : ∀ p : nat, quot_epi v 0%nat ≈ quot_epi v p).
  { induction p as [| p IH]; [ reflexivity | now rewrite IH ]. }
  now rewrite <- (zero m), <- (zero n).
Qed.

Lemma Sets_Q_total_IsMeet :
  @IsMeet (Sets@{o so}^op) NatDiscrete@{o} Sets_Q_parity Sets_Q_mod3
    Sets_Q_total.
Proof.
  constructor.
  - intro b; destruct b; exact (Sets_Q_total_below _).
  - intros v Hv.
    unshelve eexists.
    + unshelve refine
        {| morphism :=
             fun p : carrier (quot_cod Sets_Q_total) => quot_epi v p |}.
      intros p q _.
      exact (Sets_meet_collapse v (Hv true) (Hv false) p q).
    + intro a; reflexivity.
Defined.

(*
   本节说明 QuotObj 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Sets_quot_meet_parity_mod3 :
  @quot_meet Sets@{o so} Sets_HasPushouts NatDiscrete@{o}
    Sets_Q_parity Sets_Q_mod3 ≈ Sets_Q_total.
Proof.
  apply (@IsIntersection_unique (Sets@{o so}^op) NatDiscrete@{o} bool
           (sub_pair Sets_Q_parity Sets_Q_mod3)).
  - exact (@sub_meet_IsMeet (Sets@{o so}^op)
             (HasPullbacks_op_of_HasPushouts Sets_HasPushouts)
             NatDiscrete@{o} Sets_Q_parity Sets_Q_mod3).
  - exact Sets_Q_total_IsMeet.
Qed.

(* The same fact read elements pushout apex itself, no
 comparison 同构 sight: pushout two
 projections every natural identified every other. （已译） *)
Corollary Sets_quot_meet_collapses (m n : nat) :
  quot_epi (@quot_meet Sets@{o so} Sets_HasPushouts NatDiscrete@{o}
              Sets_Q_parity Sets_Q_mod3) m
    ≈ quot_epi (@quot_meet Sets@{o so} Sets_HasPushouts NatDiscrete@{o}
                  Sets_Q_parity Sets_Q_mod3) n.
Proof.
  exact (Sets_meet_collapse _ (sub_meet_le_l _ _) (sub_meet_le_r _ _) m n).
Qed.

(* * ** The bottom quotient 对象: [Epic one] inhabitedness （已译） *)

(*
   本节说明子对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Sets_one_epic_of_inhabited {X : SetoidObject@{o o}}
  (x0 : carrier X) : Epic (@one Sets@{o so} Sets_Terminal X).
Proof.
  constructor; intros Z g1 g2 H u.
  destruct u.
  exact (H x0).
Defined.

Definition Sets_quot_bot {X : SetoidObject@{o o}} (x0 : carrier X) :
  @QuotObj Sets@{o so} X :=
  @quot_bot Sets@{o so} Sets_Terminal X (Sets_one_epic_of_inhabited x0).

(* The two 常值 maps 1 → bool, without [Program] (this file has no
 obligations measurements below say so). （已译） *)
Definition Sets_pick (b : bool) :
  @terminal_obj Sets@{o so} Sets_Terminal ~{Sets@{o so}}~>
    bool_setoid_object@{o o}.
Proof.
  unshelve refine {| morphism := fun _ => b |}.
  proper.
Defined.

Lemma Sets_one_not_epic_empty :
  Epic (@one Sets@{o so} Sets_Terminal
          (@initial_obj Sets@{o so} Sets_Initial)) → False.
Proof.
  intros [He].
  assert (H : Sets_pick true
                ∘ @one Sets@{o so} Sets_Terminal
                    (@initial_obj Sets@{o so} Sets_Initial)
              ≈ Sets_pick false
                ∘ @one Sets@{o so} Sets_Terminal
                    (@initial_obj Sets@{o so} Sets_Initial))
    by (intro u; contradiction).
  pose proof (He _ _ _ H ttt) as E.
  cbn in E.
  discriminate E.
Qed.

End SetsQuotObj.
