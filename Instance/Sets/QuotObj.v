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

(** * Quotient objects of a setoid: the witness half of Mac Lane §V.7
      Definition 3 *)

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

(** ** Mac Lane's "where epis are onto" clause, both ways *)

(* The epimorphism of a quotient object of [Sets] is a surjection.  This
   is [Instance/Sets.v]'s [epic_implies_surjective] -- the backward
   leg of [surjectivity_is_epic] -- applied to the [Epic] the
   accessor [quot_is_epic] reads off the [Monic] in [Sets^op].  The
   preimage is DATA: `≈` is [Type]-valued, so [∃] is [sigT] and `1 of
   this is an honest element of the carrier. *)
Definition Sets_quot_epi_surjective {X : SetoidObject@{o o}}
  (q : @QuotObj Sets@{o so} X) :
  ∀ b : carrier (quot_cod q), ∃ a : carrier X, quot_epi q a ≈ b :=
  fun b => epic_implies_surjective (quot_epi q) (quot_is_epic q) b.

(* ... and conversely every surjection of setoids presents a quotient
   object, by the forward leg and [mk_quot]. *)
Definition Sets_quot_of_surjection {X B : SetoidObject@{o o}}
  (h : X ~{Sets@{o so}}~> B)
  (Hs : ∀ b : carrier B, ∃ a : carrier X, h a ≈ b) :
  @QuotObj Sets@{o so} X :=
  mk_quot h (surjective_implies_epic h Hs).

(** ** The quotient of a setoid by an equivalence relation, as a
       quotient object *)

(* [Instance/Sets/Quotient.v]'s [SetsQuotient A R HR] is A with a
   coarser `≈`; its projection is the IDENTITY FUNCTION, so it is
   surjective with the element itself as preimage and the surjectivity
   witness is [Equivalence_Reflexive] and nothing more.  [HC] is not
   decoration: the projection does not exist without it, its
   respectfulness clause being convertible with [SetoidCoarser R]
   (Instance/Sets/Quotient.v). *)
Definition SetsQuotient_QuotObj (A : SetoidObject@{o o})
  (R : crelation (carrier A)) (HR : Equivalence R) (HC : SetoidCoarser R) :
  @QuotObj Sets@{o so} A :=
  Sets_quot_of_surjection (sets_quot_proj A R HR HC)
    (fun b => (b; @Equivalence_Reflexive _ R HR b)).

(** ** The coimage of a setoid map *)

Section Coimage.

Context {X Y : SetoidObject@{o o}}.
Context (f : X ~{Sets@{o so}}~> Y).

(* The kernel relation of f, as a coarsening of X's own `≈`.  The
   OBJECT-level counterpart is Instance/Sets/Pullback.v's [sets_ker],
   the kernel pair; this is the same information as a relation on the
   carrier, which is what Instance/Sets/Quotient.v's quotient consumes. *)
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

(* f itself respects its own kernel relation, by the IDENTITY
   implication, so the descended map is [sets_quot_med] at that witness. *)
Definition sets_coimage_resp : RespMap sets_coimage_rel Y :=
  existT (SetsRespects sets_coimage_rel Y) f
    (fun a b (H : sets_coimage_rel a b) => H).

Definition sets_coimage_factor :
  Y ~{Sets@{o so}^op}~> quot_cod Sets_coimage :=
  sets_quot_med sets_coimage_rel sets_coimage_rel_Equivalence
    sets_coimage_resp.

(* The triangle, read in [Sets^op]: composition there is composition in
   [Sets] with the arguments swapped, so this is
   [sets_coimage_factor ∘ quot_epi Sets_coimage ≈ f] and the projection
   being the identity function leaves nothing to compute. *)
Lemma sets_coimage_commutes :
  sub_mono Sets_coimage ∘[Sets@{o so}^op] sets_coimage_factor ≈ f.
Proof. intro a; simpl; reflexivity. Qed.

(* Minimality needs a map OUT of a competing quotient INTO the coimage,
   whose carrier is the carrier of X -- so it has to choose a preimage.
   [sets_quot_med] is the wrong donor here: it maps out of the quotient,
   not into it.  Choosing is free, the preimage being data. *)
Definition sets_coimage_pick (w : @QuotObj Sets@{o so} X)
  (p : carrier (quot_cod w)) : carrier X :=
  `1 (Sets_quot_epi_surjective w p).

Lemma sets_coimage_pick_eq (w : @QuotObj Sets@{o so} X)
  (p : carrier (quot_cod w)) :
  quot_epi w (sets_coimage_pick w p) ≈ p.
Proof. exact (`2 (Sets_quot_epi_surjective w p)). Qed.

(* The choice is well defined INTO THE COIMAGE, though not into X: two
   preimages of `≈`-equal points have the same value under f, which is
   exactly equality in the coimage. *)
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

(* Theory/Subobject/Lattice.v's [ImageOf], instantiated at [Sets^op]:
   [im_sub] is a quotient object of the DOMAIN, [im_factor] the map from
   the quotient to the codomain, [im_commutes] the triangle, and
   [im_least] says the coimage is BELOW (that is, coarser than) every
   quotient through which f factors. *)
Definition Sets_CoimageOf : @ImageOf (Sets@{o so}^op) Y X f := {|
  im_sub := Sets_coimage;
  im_factor := sets_coimage_factor;
  im_commutes := sets_coimage_commutes;
  im_least := fun w g Hg => sets_coimage_least w g Hg
|}.

End Coimage.

(* The class form.  The anonymous record literal [{| image_of := … |}] is
   REFUSED here -- it elaborates the field against [C := Sets] and reports
   "has type @ImageOf Sets^op X Y f while it is expected to have type
   @ImageOf Sets Y X f" -- so the constructor is named and its category
   argument given explicitly. *)
#[export] Instance Sets_HasCoimages : @HasImages (Sets@{o so}^op) :=
  @Build_HasImages (Sets@{o so}^op) (fun Y X f => @Sets_CoimageOf X Y f).

(* The JOIN of two quotient objects at Sets, by transport and nothing
   else: Theory/Subobject/Quotient.v's [quot_join] wants a [Cartesian]
   structure on the category -- Instance/Sets/Cartesian.v's
   [Sets_Cartesian], which IS a [@Cocartesian (Sets^op)] on the nose
   (Structure/Cocartesian.v makes [Cocartesian C] notation for
   [@Cartesian (C^op)], and [Sets^op^op] is [Sets] by reflexivity) -- and
   the coimages just registered.  The join is the coimage of the pairing
   of the two epis into the product of their codomains.  An earlier
   revision of this file said the join "needs a product instance not
   assembled here"; an audit refuted that by compiling this one line, so
   it is landed rather than left as a false obstruction.  Its least-
   upper-bound property and the lattice laws are [quot_join_is_lub],
   [quot_join_comm] and their siblings, read at [Sets]; none is restated
   here. *)
Definition Sets_quot_join {X : SetoidObject@{o o}}
  (q r : @QuotObj Sets@{o so} X) : @QuotObj Sets@{o so} X :=
  quot_join q r.

(** ** A worked meet: parity ∧ residue-mod-3 on the naturals *)

(* The residue mod 3, by a three-step fixpoint rather than by [Nat.modulo],
   so that [nat_tri (S (S (S m))) = nat_tri m] holds by [eq_refl] and the
   collapse argument below needs no arithmetic lemma.  Its parity
   counterpart, [Nat.even (S (S m)) = Nat.even m], holds by [eq_refl] for
   the same reason. *)
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

(* The three quotient objects of the discrete setoid on [nat]:
   Instance/Sets/Quotient.v's parity, the residue mod 3, and that
   file's total relation. *)
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

(* The total quotient is the BOTTOM of the factorization order on
   quotient objects of [NatDiscrete]: it factors through every quotient
   (every quotient has it below), by the constant map out of that
   quotient's codomain, whose respectfulness is [ttt].  An earlier
   revision of this comment said "every quotient factors through it",
   the reverse direction; the statement below was always the right one. *)
Lemma Sets_Q_total_below (w : @QuotObj Sets@{o so} NatDiscrete@{o}) :
  @sub_le (Sets@{o so}^op) NatDiscrete@{o} Sets_Q_total w.
Proof.
  unshelve eexists.
  - unshelve refine {| morphism := fun _ : carrier (quot_cod w) => 0%nat |}.
    intros p q Hpq; exact ttt.
  - intro a; exact ttt.
Defined.

(* The arithmetic of the meet, done once: a quotient coarser than both
   parity and residue-mod-3 identifies EVERY pair of naturals.  m and
   m+3 agree mod 3, m+3 and m+1 agree in parity, so consecutive
   naturals are identified and induction finishes.  Both steps are
   [eq_refl] at the two invariants. *)
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

(* The stub's [quot_meet] at [Sets], evaluated.  Both sides are greatest
   lower bounds of the same two-element family, so they agree -- at ≈ on
   [QuotObj], which is the strongest relation available here ([QuotObj]
   has no Leibniz antisymmetry, exactly as [SubObj] has none). *)
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

(* The same fact read on elements of the pushout apex itself, with no
   comparison isomorphism in sight: in the pushout of the two
   projections every natural is identified with every other. *)
Corollary Sets_quot_meet_collapses (m n : nat) :
  quot_epi (@quot_meet Sets@{o so} Sets_HasPushouts NatDiscrete@{o}
              Sets_Q_parity Sets_Q_mod3) m
    ≈ quot_epi (@quot_meet Sets@{o so} Sets_HasPushouts NatDiscrete@{o}
                  Sets_Q_parity Sets_Q_mod3) n.
Proof.
  exact (Sets_meet_collapse _ (sub_meet_le_l _ _) (sub_meet_le_r _ _) m n).
Qed.

(** ** The bottom quotient object: [Epic one] is inhabitedness *)

(* Theory/Subobject/Quotient.v's [quot_bot] is conditional on
   [Epic (one : X ~> 1)].  In [Sets] that hypothesis is EXACTLY
   inhabitedness of the carrier, both ways.  Given a point [x0], two maps
   out of the singleton that agree after [one] agree at their only
   argument, because [one x0] IS that argument -- three lines and
   nothing assumed.  At the empty setoid the two constant maps 1 → bool
   agree after ∅ → 1 for free (there is nothing to check) and differ at
   [ttt], so [one] is not epic there.  Hence the coarsest quotient
   object, X ↠ 1, exists at every inhabited setoid and the theory's
   hypothesis is not a gap at [Sets]; it is object-dependent, and this
   pair of constants is the measurement. *)
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

(* The two constant maps 1 → bool, without [Program] (this file has no
   obligations and the measurements below say so). *)
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
