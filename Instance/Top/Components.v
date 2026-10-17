Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Adjunction.Continuity.Equalizer.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Sets.Propositional.Full.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Complete.
Require Import Category.Instance.Top.Cocomplete.
Require Import Category.Instance.Top.Separation.
Require Category.Theory.Concrete.
Require Import Coq.Arith.PeanoNat.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 nLab: https://ncatlab.org/nlab/show/Top
 nLab: https://ncatlab.org/nlab/show/locally+connected+space
 nLab: https://ncatlab.org/nlab/show/connected+space
 Wikipedia: https://en.wikipedia.org/wiki/Locally_connected_space

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

(* * ** Connectedness, Prop-valued locally-常值 form （已译） *)

(* A Prop-valued function [φ] locally 常值 subset [W]: every
 point [W] has open neighbourhood whose trace [W] value of
 [φ] does not change. （已译） *)
Definition LocConstOn@{o} (X : PTop@{o}) (W φ : X → Prop) : Prop :=
  ∀ z, W z → ex (fun O => POpen X O /\ O z /\
                           ∀ w, W w → O w → (φ w <-> φ z)).

(* [W] is connected: every Prop-valued function locally constant on [W] is
   constant on [W]. *)
Definition PConnectedSub@{o} (X : PTop@{o}) (W : X → Prop) : Prop :=
  ∀ φ, LocConstOn X W φ → ∀ a b, W a → W b → φ a → φ b.

(* 相关说明。 （已译） *)
Definition PConnected@{o} (X : PTop@{o}) : Prop :=
  PConnectedSub X (fun _ => True).

(* Local connectedness: every open neighbourhood of a point contains a
   connected open neighbourhood of it. *)
Definition PLocConn@{o} (X : PTop@{o}) : Prop :=
  ∀ x U, POpen X U → U x →
    ex (fun N => POpen X N /\ N x /\ (∀ y, N y → U y) /\ PConnectedSub X N).

(* Two points lie common connected subset: 关系 whose classes
 connected components. （已译） *)
Definition comp_rel@{o} (X : PTop@{o}) (x y : X) : Prop :=
  ex (fun W => PConnectedSub X W /\ W x /\ W y).

Lemma locconst_restrict@{o} (X : PTop@{o}) (W W' φ : X → Prop) :
  (∀ z, W z → W' z) → LocConstOn X W' φ → LocConstOn X W φ.
Proof.
  intros HW H z wz.
  destruct (H z (HW z wz)) as [O [HO [Oz HOw]]].
  exists O; split; [exact HO|split; [exact Oz|]].
  intros w ww Ow; exact (HOw w (HW w ww) Ow).
Qed.

(* 相关说明。 （已译） *)
Lemma point_connected@{o} (X : PTop@{o}) (x : X) :
  PConnectedSub X (fun z => inhabited (x ≈ z)).
Proof.
  intros φ H a b [Ha] [Hb] pa.
  destruct (H a (inhabits Ha)) as [O [HO [Oa HOw]]].
  assert (Ob : O b).
  { apply (popen_proper X O HO a b); [|exact Oa].
    exact (transitivity (symmetry Ha) Hb). }
  exact (proj2 (HOw b (inhabits Hb) Ob) pa).
Qed.

Lemma comp_rel_of_equiv@{o} (X : PTop@{o}) (x y : X) :
  x ≈ y → comp_rel X x y.
Proof.
  intro H. exists (fun z => inhabited (x ≈ z)).
  split; [apply point_connected|].
  split; [exact (inhabits (reflexivity x))|exact (inhabits H)].
Qed.

Lemma comp_rel_sym@{o} (X : PTop@{o}) (x y : X) :
  comp_rel X x y → comp_rel X y x.
Proof. intros [W [HW [wx wy]]]; exists W; exact (conj HW (conj wy wx)). Qed.

(* Two connected subsets sharing a point have a connected union. *)
Lemma union_connected@{o} (X : PTop@{o}) (W1 W2 : X → Prop) (c : X) :
  PConnectedSub X W1 → PConnectedSub X W2 → W1 c → W2 c →
  PConnectedSub X (fun z => W1 z \/ W2 z).
Proof.
  intros H1 H2 c1 c2 φ H a b wa wb pa.
  pose proof (locconst_restrict X W1 _ φ (fun z w => or_introl w) H) as L1.
  pose proof (locconst_restrict X W2 _ φ (fun z w => or_intror w) H) as L2.
  destruct wa as [a1|a2]; destruct wb as [b1|b2].
  - exact (H1 φ L1 a b a1 b1 pa).
  - exact (H2 φ L2 c b c2 b2 (H1 φ L1 a c a1 c1 pa)).
  - exact (H1 φ L1 c b c1 b1 (H2 φ L2 a c a2 c2 pa)).
  - exact (H2 φ L2 a b a2 b2 pa).
Qed.

Lemma comp_rel_trans@{o} (X : PTop@{o}) (x y z : X) :
  comp_rel X x y → comp_rel X y z → comp_rel X x z.
Proof.
  intros [W1 [H1 [w1x w1y]]] [W2 [H2 [w2y w2z]]].
  exists (fun v => W1 v \/ W2 v).
  split; [exact (union_connected X W1 W2 y H1 H2 w1y w2y)|].
  exact (conj (or_introl w1x) (or_intror w2z)).
Qed.

(* The points under component 关系. （已译） *)
Definition CompSetoid@{o} (X : PTop@{o}) : Setoid@{o o} X := {|
  equiv := comp_rel X;
  setoid_equiv := {|
    Equivalence_Reflexive := fun x => comp_rel_of_equiv X x x (reflexivity x);
    Equivalence_Symmetric := comp_rel_sym X;
    Equivalence_Transitive := comp_rel_trans X |}
|}.

(* 相关说明。 （已译） *)
Definition CompSet@{o} (X : PTop@{o}) : SetoidObject@{o o} :=
  {| carrier := pt_carrier X; is_setoid := CompSetoid X |}.

(* Its equality is a proposition, [comp_rel] itself. *)
Definition comp_PropEquiv@{o} (X : PTop@{o}) :
  PropEquiv@{o o} (is_setoid (CompSet X)) :=
  @PropEquiv_of_relation@{o o} _ (CompSetoid X) (comp_rel X)
    (fun _ _ h => h) (fun _ _ h => h).

(* 相关说明。 （已译） *)

(* No separation of the space by two disjoint open sets covering it. *)
Definition PConnectedSep@{o} (X : PTop@{o}) : Prop :=
  ∀ U V, POpen X U → POpen X V → (∀ z, U z \/ V z) →
    (∀ z, U z → V z → False) → ∀ a b, U a → U b.

(* Every continuous map into the discrete two-point space is constant. *)
Definition PConnectedBool@{o} (X : PTop@{o}) : Prop :=
  ∀ g : PMor@{o} X PBool@{o}, ∀ a b, pmap g a = pmap g b.

(* A connected subset lies in one side of every pair of disjoint opens
   covering it. *)
Lemma connected_no_separation@{o} (X : PTop@{o}) (W : X → Prop)
  (HW : PConnectedSub X W) (U V : X → Prop) :
  POpen X U → POpen X V → (∀ z, W z → U z \/ V z) →
  (∀ z, W z → U z → V z → False) →
  ∀ a b, W a → W b → U a → U b.
Proof.
  intros HU HV Hcov Hdis a b wa wb ua.
  refine (HW U _ a b wa wb ua).
  intros z wz. destruct (Hcov z wz) as [uz|vz].
  - exists U. split; [exact HU|split; [exact uz|]].
    intros w _ uw; split; intros _; assumption.
  - exists V. split; [exact HV|split; [exact vz|]].
    intros w ww vw; split; intro h.
    + destruct (Hdis w ww h vw).
    + destruct (Hdis z wz h vz).
Qed.

(* A continuous map into the discrete two-point space is constant on a
   connected subset. *)
Lemma connected_bool_constant@{o} (X : PTop@{o}) (W : X → Prop)
  (HW : PConnectedSub X W) (g : PMor@{o} X PBool@{o}) :
  ∀ a b, W a → W b → pmap g a = pmap g b.
Proof.
  intros a b wa wb.
  refine (HW (fun z => pmap g a = pmap g z) _ a b wa wb eq_refl).
  intros z _. exists (fun w => pmap g z = pmap g w).
  split; [|split; [reflexivity|]].
  - apply (pcont g (fun s => pmap g z = s)).
    intros s t e h; simpl in e; exact (eq_trans h e).
  - intros w _ e; split; intro h; congruence.
Qed.

Corollary PConnected_Sep@{o} (X : PTop@{o}) :
  PConnected X → PConnectedSep X.
Proof.
  intros H U V HU HV Hcov Hdis a b.
  exact (connected_no_separation X _ H U V HU HV (fun z _ => Hcov z)
           (fun z _ => Hdis z) a b I I).
Qed.

Corollary PConnected_Bool@{o} (X : PTop@{o}) :
  PConnected X → PConnectedBool X.
Proof. intros H g a b. exact (connected_bool_constant X _ H g a b I I). Qed.

(* 相关说明。 （已译） *)

Lemma image_connected@{o} {X Y : PTop@{o}} (f : PMor@{o} X Y)
  (W : X → Prop) :
  PConnectedSub X W →
  PConnectedSub Y (fun y => ex (fun x => W x /\ pmap f x = y)).
Proof.
  intros HW φ H a b [xa [wa ea]] [xb [wb eb]] pa.
  subst a b.
  refine (HW (fun x => φ (pmap f x)) _ xa xb wa wb pa).
  intros z wz.
  destruct (H (pmap f z) (ex_intro _ z (conj wz eq_refl)))
    as [O [HO [Oz HOw]]].
  exists (fun x => O (pmap f x)); split; [exact (pcont f O HO)|].
  split; [exact Oz|].
  intros w ww Ow.
  exact (HOw (pmap f w) (ex_intro _ w (conj ww eq_refl)) Ow).
Qed.

Lemma comp_rel_map@{o} {X Y : PTop@{o}} (f : PMor@{o} X Y) (x x' : X) :
  comp_rel X x x' → comp_rel Y (pmap f x) (pmap f x').
Proof.
  intros [W [HW [wx wx']]].
  exists (fun y => ex (fun x => W x /\ pmap f x = y)).
  split; [exact (image_connected f W HW)|].
  split; [exists x; exact (conj wx eq_refl)
         |exists x'; exact (conj wx' eq_refl)].
Qed.

(* A continuous map sends components into components. *)
Definition comp_setoid_map@{o} {X Y : PTop@{o}} (f : PMor@{o} X Y) :
  SetoidMorphism@{o o o} (CompSet X) (CompSet Y).
Proof.
  refine {| morphism := fun x => pmap f x |}.
  intros x x' H; exact (comp_rel_map f x x' H).
Defined.

(* * ** The 范畴: propositional sets locally connected spaces （已译） *)

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition PSetsSub@{o so | o < so +} : Subcategory@{so o so o} Sets@{o so} :=
  PropSets_sub@{o so}.

Definition PSets@{o so | o < so +} : Category@{so o o} :=
  PropSets@{o so}.

(* 相关说明。 （已译） *)
Definition Lconn_Sub@{o so | o < so +} :
  Subcategory@{so o o o} PTopCat@{o so} :=
  PFullSub@{o so} PLocConn@{o}.

Definition Lconn@{o so | o < so +} : Category@{so o o} :=
  Sub@{so o o o so o so} PTopCat@{o so} Lconn_Sub@{o so}.

(** ** The components functor *)

(* On all [PTopCat]: no local connectedness needed 函子. （已译） *)
Program Definition CompTop@{o so | o < so +} :
  PTopCat@{o so} ⟶ PSets@{o so} := {|
  fobj := fun X => (CompSet X; comp_PropEquiv X);
  fmap := fun X Y f => (comp_setoid_map f; I)
|}.
Next Obligation.
  intros X Y f g H x; simpl. apply comp_rel_of_equiv; exact (H x).
Qed.
Next Obligation. intros X x; simpl. apply comp_rel_of_equiv; reflexivity. Qed.
Next Obligation.
  intros X Y Z f g x; simpl. apply comp_rel_of_equiv; reflexivity.
Qed.

(* Mac Lane's C, on the locally connected spaces. *)
Definition components_functor@{o so | o < so +} :
  Lconn@{o so} ⟶ PSets@{o so} :=
  @Compose@{so so so so o} Lconn@{o so} PTopCat@{o so} PSets@{o so}
    CompTop@{o so} (Incl@{so o o o so so} PTopCat@{o so} Lconn_Sub@{o so}).

(* * ** The discrete-space 函子 [Lconn] （已译） *)

Lemma pdisc_locconn@{o} (S : SetoidObject@{o o}) : PLocConn (PDiscrete S).
Proof.
  intros x U HU ux.
  exists (fun y => inhabited (x ≈ y)).
  split; [|split; [exact (inhabits (reflexivity x))|split]].
  - intros a b e [h]. exact (inhabits (transitivity h e)).
  - intros y [h]. exact (HU x y h ux).
  - apply point_connected.
Qed.

(* Instance/Top/Complete.v's [PDisc], corestricted [Lconn]: 对象
 arrow parts, three laws. （已译） *)
Program Definition LDisc@{o so | o < so +} : Sets@{o so} ⟶ Lconn@{o so} := {|
  fobj := fun S => (fobj[PDisc@{o so}] S; pdisc_locconn S);
  fmap := fun S T f => (fmap[PDisc@{o so}] f; I)
|}.
Next Obligation.
  intros S T f g H. exact (@fmap_respects _ _ PDisc@{o so} S T f g H).
Qed.
Next Obligation. intros S. exact (@fmap_id _ _ PDisc@{o so} S). Qed.
Next Obligation.
  intros S T U f g. exact (@fmap_comp _ _ PDisc@{o so} S T U f g).
Qed.

(* Mac Lane's D : Set → Lconn, at the propositional sets. *)
Definition PSetsDisc@{o so | o < so +} : PSets@{o so} ⟶ Lconn@{o so} :=
  @Compose@{so so so so o} PSets@{o so} Sets@{o so} Lconn@{o so}
    LDisc@{o so} (Incl@{so o so o so so} Sets@{o so} PSetsSub@{o so}).

(** ** Exercise 1, first half: C ⊣ D *)

(* Every continuous map into a discrete space on a propositional set is
   constant on each connected subset. *)
Lemma comp_respect@{o} (X : PTop@{o}) (S : SetoidObject@{o o})
  (P : PropEquiv@{o o} (is_setoid S)) (g : PMor@{o} X (PDiscrete S))
  (x y : X) :
  comp_rel X x y → pmap g x ≈ pmap g y.
Proof.
  intro H. apply (@pequiv_to _ _ P).
  destruct H as [W [HW [wx wy]]].
  refine (HW (fun z => @pequiv _ _ P (pmap g x) (pmap g z)) _ x y wx wy
            (pequiv_from _ _ (reflexivity _))).
  intros z wz.
  exists (fun w => @pequiv _ _ P (pmap g z) (pmap g w)).
  split; [|split].
  - apply (pcont g (fun s => @pequiv _ _ P (pmap g z) s)).
    intros s t e p. apply pequiv_from.
    exact (transitivity (pequiv_to _ _ p) e).
  - apply pequiv_from; reflexivity.
  - intros w ww p. split; intro q.
    + apply pequiv_from.
      exact (transitivity (pequiv_to _ _ q) (symmetry (pequiv_to _ _ p))).
    + apply pequiv_from.
      exact (transitivity (pequiv_to _ _ q) (pequiv_to _ _ p)).
Qed.

(* In locally connected space every map 常值 components is
 continuous 进入 discrete space: components open. Local
 connectedness used once, at whole space. （已译） *)
Lemma comp_cont@{o} (X : PTop@{o}) (LC : PLocConn X) (S : SetoidObject@{o o})
  (h : SetoidMorphism@{o o o} (CompSet X) S) :
  @PCont X (PDiscrete S)
    {| morphism := fun x => h x;
       proper_morphism := fun x y e =>
         proper_morphism h x y (comp_rel_of_equiv X x y e) |}.
Proof.
  intros U HU.
  apply (popen_respects X
    (fun y => ex (fun N => (POpen X N /\ PConnectedSub X N /\
                            ex (fun x => N x /\ U (h x))) /\ N y))).
  - intro y; split.
    + intros [N [[_ [HN [x [nx ux]]]] ny]]; simpl.
      assert (Hc : comp_rel X x y) by (exists N; exact (conj HN (conj nx ny))).
      exact (HU (h x) (h y) (proper_morphism h x y Hc) ux).
    + simpl; intro uy.
      destruct (LC y (fun _ => True) (popen_whole X) I)
        as [N [HN [ny [_ Hc]]]].
      exists N. split; [|exact ny].
      split; [exact HN|split; [exact Hc|exists y; exact (conj ny uy)]].
  - apply popen_union. intros N [HN _]; exact HN.
Qed.

(* The hom-set bijection: both directions 恒等 points. （已译） *)
Program Definition comp_adj_iso@{o so | o < so +}
  (X : Lconn@{o so}) (S : PSets@{o so}) :
  @Isomorphism Sets@{o so}
    {| carrier := @hom PSets@{o so} (components_functor@{o so} X) S
     ; is_setoid := @homset PSets@{o so} (components_functor@{o so} X) S |}
    {| carrier := @hom Lconn@{o so} X (PSetsDisc@{o so} S)
     ; is_setoid := @homset Lconn@{o so} X (PSetsDisc@{o so} S) |} := {|
  to   := {| morphism := fun h =>
              (@Build_PMor (`1 X) (PDiscrete (`1 S)) _
                 (comp_cont (`1 X) (`2 X) (`1 S) (`1 h)); I) |};
  from := {| morphism := fun g =>
              ({| morphism := fun x => pmap (`1 g) x;
                  proper_morphism :=
                    comp_respect (`1 X) (`1 S) (`2 S) (`1 g) |}; I) |}
|}.
Next Obligation. intros X S h h' H x; exact (H x). Qed.
Next Obligation. intros X S g g' H x; exact (H x). Qed.
Next Obligation. intros X S g x; simpl; reflexivity. Qed.
Next Obligation. intros X S h x; simpl; reflexivity. Qed.

Definition components_left_adjoint_discrete@{o so | o < so +} :
  @Adjunction@{so o o so o o o o so o so} PSets@{o so} Lconn@{o so}
    components_functor@{o so} PSetsDisc@{o so}.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ components_functor PSetsDisc
                     comp_adj_iso).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(** ** Readbacks *)

Example components_obj@{o so | o < so +} (X : Lconn@{o so}) :
  `1 (fobj[components_functor@{o so}] X) = CompSet (`1 X) := eq_refl.

Example components_equiv@{o so | o < so +} (X : Lconn@{o so})
  (x y : pt_carrier (`1 X)) :
  @equiv _ (is_setoid (`1 (fobj[components_functor@{o so}] X))) x y
    = comp_rel (`1 X) x y := eq_refl.

Example components_fmap@{o so | o < so +} {X Y : Lconn@{o so}}
  (f : X ~{Lconn@{o so}}~> Y) (x : pt_carrier (`1 X)) :
  `1 (fmap[components_functor@{o so}] f) x = pmap (`1 f) x := eq_refl.

Example LDisc_PDisc_obj@{o so | o < so +} (S : Sets@{o so}) :
  `1 (fobj[LDisc@{o so}] S) = fobj[PDisc@{o so}] S := eq_refl.

Example LDisc_PDisc_fmap@{o so | o < so +} {S T : Sets@{o so}}
  (f : S ~{Sets@{o so}}~> T) :
  `1 (fmap[LDisc@{o so}] f) = fmap[PDisc@{o so}] f := eq_refl.

Example PSetsDisc_obj@{o so | o < so +} (S : PSets@{o so}) :
  `1 (fobj[PSetsDisc@{o so}] S) = PDiscrete (`1 S) := eq_refl.

Example adj_to_points@{o so | o < so +} (X : Lconn@{o so}) (S : PSets@{o so})
  (h : components_functor@{o so} X ~{PSets@{o so}}~> S)
  (x : pt_carrier (`1 X)) :
  pmap (`1 (to (@adj _ _ _ _ components_left_adjoint_discrete@{o so} X S) h)) x
    = `1 h x := eq_refl.

Example adj_from_points@{o so | o < so +} (X : Lconn@{o so}) (S : PSets@{o so})
  (g : X ~{Lconn@{o so}}~> PSetsDisc@{o so} S) (x : pt_carrier (`1 X)) :
  `1 (from (@adj _ _ _ _ components_left_adjoint_discrete@{o so} X S) g) x
    = pmap (`1 g) x := eq_refl.

(* The unit sends each point to itself, its own component. *)
Example components_unit_points@{o so | o < so +} (X : Lconn@{o so})
  (x : pt_carrier (`1 X)) :
  pmap (`1 (@unit _ _ _ _ components_left_adjoint_discrete@{o so} X)) x = x
  := eq_refl.

(* 相关说明。 （已译） *)

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition squash_id@{o} (Q : Type@{o}) :
  SetoidMorphism@{o o o} PTwoIndisc@{o} (SquashSetoid Q).
Proof.
  refine {| morphism := fun b : bool => b |}.
  intros x y e; simpl in e; subst; left; reflexivity.
Defined.

(* Merely inhabited [Q] makes 恒等 continuous indiscrete
 two-point space 进入 discrete space [SquashSetoid Q]. （已译） *)
Lemma squash_id_cont@{o} (Q : Type@{o}) (iq : inhabited Q) :
  @PCont PTwoIndisc@{o} (PDiscrete (SquashSetoid Q)) (squash_id Q).
Proof.
  intros U HU x y u. destruct iq as [q].
  apply (HU x y); [right; exact q|exact u].
Qed.

Lemma PTwoIndisc_connected@{o} : PConnected PTwoIndisc@{o}.
Proof.
  intros φ H a b _ _ pa.
  destruct (H a I) as [O [HO [Oa HOw]]].
  exact (proj2 (HOw b I (HO a b Oa)) pa).
Qed.

Lemma PTwoIndisc_PLocConn@{o} : PLocConn PTwoIndisc@{o}.
Proof.
  intros x U HU ux. exists (fun _ => True).
  split; [exact (popen_whole _)|split; [exact I|split]].
  - intros y _; exact (HU x y ux).
  - exact PTwoIndisc_connected.
Qed.

Definition LTwoIndisc@{o so | o < so +} : Lconn@{o so} :=
  (PTwoIndisc@{o}; PTwoIndisc_PLocConn@{o}).

(* A 左伴随 discrete 函子 ALL [Sets] turns every
 merely inhabited type at points' universe inhabitant. （已译） *)
Theorem components_on_all_Sets_unsquashes@{o so +| o < so +}
  (C' : Lconn@{o so} ⟶ Sets@{o so}) (A : C' ⊣ LDisc@{o so}) :
  inhabited (∀ Q : Type@{o}, inhabited Q → Q).
Proof.
  pose (eta := to (@adj _ _ _ _ A LTwoIndisc (C' LTwoIndisc)) id).
  (* 相关说明。 （已译） *)
  assert (He : inhabited (pmap (`1 eta) true ≈ pmap (`1 eta) false)).
  { pose proof (pcont (`1 eta)
                  (fun s => inhabited (pmap (`1 eta) true ≈ s))) as Hc.
    refine (Hc _ true false (inhabits (reflexivity _))).
    intros s t e [h]; exact (inhabits (transitivity h e)). }
  destruct He as [e]. constructor. intros Q iq.
  pose (g := ((@Build_PMor PTwoIndisc (PDiscrete (SquashSetoid Q)) (squash_id Q)
                (squash_id_cont Q iq)); I)
             : LTwoIndisc ~{Lconn@{o so}}~> LDisc (SquashSetoid Q)).
  pose (SQ := SquashSetoid Q).
  pose (gh := from (@adj _ _ _ _ A LTwoIndisc SQ) g).
  assert (Hg : ∀ b, squash_rel Q b (gh (pmap (`1 eta) b))).
  { intro b.
    pose proof (iso_to_from (@adj _ _ _ _ A LTwoIndisc SQ) g b) as E1.
    pose proof (@to_adj_nat_r _ _ _ _ A LTwoIndisc (C' LTwoIndisc) SQ
                  gh id b) as E2.
    pose proof (proper_morphism (to (@adj _ _ _ _ A LTwoIndisc SQ)) _ _
                  (id_right gh) b) as E3.
    simpl in E1, E2, E3.
    exact (squash_trans _ _ _ _ (squash_sym _ _ _ E1)
             (squash_trans _ _ _ _ (squash_sym _ _ _ E3) E2)). }
  pose proof (squash_trans _ _ _ _ (Hg true)
               (squash_trans _ _ _ _ (proper_morphism gh _ _ e)
                  (squash_sym _ _ _ (Hg false)))) as H.
  destruct H as [H|q]; [discriminate H|exact q].
Qed.

(* 相关说明。 （已译） *)
Lemma unsquash_choice@{o} (U : inhabited (∀ Q : Type@{o}, inhabited Q → Q))
  (A B : Type@{o}) (R : A → B → Prop) :
  (∀ a, ex (fun b => R a b)) → ex (fun f : A → B => ∀ a, R a (f a)).
Proof.
  intro H. destruct U as [u].
  exists (fun a => proj1_sig (u {b : B | R a b}
                                (let (b, r) := H a in inhabits (exist _ b r)))).
  intro a. exact (proj2_sig _).
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Components 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition unsquash_Untruncate@{o} :
  inhabited (∀ Q : Type@{o}, inhabited Q → Q) → inhabited Untruncate@{o} :=
  fun H => match H with inhabits u => inhabits (untr_of_choice@{o} u) end.

Definition Untruncate_unsquash@{o} (U : Untruncate@{o}) (Q : Type@{o}) :
  inhabited Q → Q :=
  choice_of_untr@{o} U Q.

(* So a left adjoint of the discrete functor into all of [Sets] makes
   [Untruncate] merely true. *)
Corollary components_on_all_Sets_Untruncate@{o so +| o < so +}
  (C' : Lconn@{o so} ⟶ Sets@{o so}) (A : C' ⊣ LDisc@{o so}) :
  inhabited Untruncate@{o}.
Proof.
  exact (unsquash_Untruncate (components_on_all_Sets_unsquashes C' A)).
Qed.

(* Under [Untruncate], a continuous map into a discrete space on ANY
   setoid is constant on components: the proposition carried along the
   connected subset is the truncation [Powerset_squash] of [≈].（标题）（已译） *)
Lemma comp_respect_U@{o} (U : Untruncate@{o}) (X : PTop@{o})
  (S : SetoidObject@{o o}) (g : PMor@{o} X (PDiscrete S)) (x y : X) :
  comp_rel X x y → pmap g x ≈ pmap g y.
Proof.
  intro H. apply U.
  destruct H as [W [HW [wx wy]]].
  refine (HW (fun z => Powerset_squash (pmap g x ≈ pmap g z)) _ x y wx wy
            (Powerset_squash_intro (reflexivity _))).
  intros z wz.
  exists (fun w => Powerset_squash (pmap g z ≈ pmap g w)).
  split; [|split].
  - apply (pcont g (fun s => Powerset_squash (pmap g z ≈ s))).
    intros s t e p Q k. apply p. intro h. exact (k (transitivity h e)).
  - exact (Powerset_squash_intro (reflexivity _)).
  - intros w ww p. split; intros q Q k.
    + apply q. intro h. apply p. intro h'.
      exact (k (transitivity h (symmetry h'))).
    + apply q. intro h. apply p. intro h'. exact (k (transitivity h h')).
Qed.

(* Mac Lane's C into all of [Sets]: [components_functor] followed by the
   inclusion of [PSets]. *)
Definition components_functor_Sets@{o so | o < so +} :
  Lconn@{o so} ⟶ Sets@{o so} :=
  @Compose@{so so so so o} Lconn@{o so} PSets@{o so} Sets@{o so}
    (Incl@{so o so o so so} Sets@{o so} PSetsSub@{o so})
    components_functor@{o so}.

(* 相关说明。 （已译） *)
Program Definition comp_adj_iso_U@{o so | o < so +} (U : Untruncate@{o})
  (X : Lconn@{o so}) (S : Sets@{o so}) :
  @Isomorphism Sets@{o so}
    {| carrier := @hom Sets@{o so} (components_functor_Sets@{o so} X) S
     ; is_setoid := @homset Sets@{o so} (components_functor_Sets@{o so} X) S |}
    {| carrier := @hom Lconn@{o so} X (LDisc@{o so} S)
     ; is_setoid := @homset Lconn@{o so} X (LDisc@{o so} S) |} := {|
  to   := {| morphism := fun h =>
              (@Build_PMor (`1 X) (PDiscrete S) _
                 (comp_cont (`1 X) (`2 X) S h); I) |};
  from := {| morphism := fun g =>
              {| morphism := fun x => pmap (`1 g) x;
                 proper_morphism := comp_respect_U U (`1 X) S (`1 g) |} |}
|}.
Next Obligation. intros U X S h h' H x; exact (H x). Qed.
Next Obligation. intros U X S g g' H x; exact (H x). Qed.
Next Obligation. intros U X S g x; simpl; reflexivity. Qed.
Next Obligation. intros U X S h x; simpl; reflexivity. Qed.

(* Mac Lane's C ⊣ D with his Set read literally, as all of [Sets], under
   [Untruncate]. *)
Definition components_left_adjoint_discrete_Sets@{o so | o < so +}
  (U : Untruncate@{o}) :
  @Adjunction@{so o o so o o o o so o so} Sets@{o so} Lconn@{o so}
    components_functor_Sets@{o so} LDisc@{o so}.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ components_functor_Sets LDisc
                     (comp_adj_iso_U U)).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

Example adj_Sets_to_points@{o so | o < so +} (U : Untruncate@{o})
  (X : Lconn@{o so}) (S : Sets@{o so})
  (h : components_functor_Sets@{o so} X ~{Sets@{o so}}~> S)
  (x : pt_carrier (`1 X)) :
  pmap (`1 (to (@adj _ _ _ _
                 (components_left_adjoint_discrete_Sets@{o so} U) X S) h)) x
    = h x := eq_refl.

Example adj_Sets_from_points@{o so | o < so +} (U : Untruncate@{o})
  (X : Lconn@{o so}) (S : Sets@{o so})
  (g : X ~{Lconn@{o so}}~> LDisc@{o so} S) (x : pt_carrier (`1 X)) :
  from (@adj _ _ _ _ (components_left_adjoint_discrete_Sets@{o so} U) X S)
    g x = pmap (`1 g) x := eq_refl.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Inductive zig_pt@{} : Set := zig_a | zig_c | zig_b.

Definition zig_setoid@{o} : SetoidObject@{o o} :=
  {| carrier := zig_pt; is_setoid := eq_Setoid zig_pt |}.

Definition zig_open@{o} (U : zig_setoid@{o} → Prop) : Prop :=
  U zig_c → U zig_a /\ U zig_b.

Definition PZig@{o} : PTop@{o}.
Proof.
  refine {| pt_carrier := zig_setoid@{o}; POpen := zig_open@{o} |}.
  - intros U V H HU v. pose proof (HU (proj2 (H zig_c) v)) as [a b].
    exact (conj (proj1 (H zig_a) a) (proj1 (H zig_b) b)).
  - intros U _ x y Hxy u. simpl in Hxy. subst. exact u.
  - intros F HF [U [FU u]]. destruct (HF U FU u) as [a b].
    split; exists U; split; assumption.
  - intros _. split; exact I.
  - intros U V HU HV [u v].
    destruct (HU u), (HV v). split; split; assumption.
Defined.

Lemma PZig_connected@{o} : PConnected PZig@{o}.
Proof.
  intros φ H a b _ _ pa.
  destruct (H zig_c I) as [O [HO [Oc HOw]]].
  destruct (HO Oc) as [Oa Ob].
  assert (Hall : ∀ z : zig_pt, O z) by (intros []; assumption).
  exact (proj2 (HOw b I (Hall b)) (proj1 (HOw a I (Hall a)) pa)).
Qed.

(* It has one component. *)
Corollary PZig_one_component@{o} (x y : zig_pt) : comp_rel PZig@{o} x y.
Proof. exists (fun _ => True). exact (conj PZig_connected (conj I I)). Qed.

Lemma PZig_PLocConn@{o} : PLocConn PZig@{o}.
Proof.
  intros x U HU u.
  destruct x.
  - exists (fun y => inhabited (@equiv _ PZig@{o} zig_a y)).
    split; [|split; [exact (inhabits eq_refl)|split]].
    + intros [h]; discriminate h.
    + intros y [h]; simpl in h; subst; exact u.
    + apply point_connected.
  - exists (fun _ => True).
    split; [intros _; split; exact I|split; [exact I|split]].
    + destruct (HU u) as [a b]. intros [] _; assumption.
    + exact PZig_connected.
  - exists (fun y => inhabited (@equiv _ PZig@{o} zig_b y)).
    split; [|split; [exact (inhabits eq_refl)|split]].
    + intros [h]; discriminate h.
    + intros y [h]; simpl in h; subst; exact u.
    + apply point_connected.
Qed.

(* The parallel pair 进入 indiscrete two-point space: 常值 at
 [false], [true] exactly at [zig_c]. （已译） *)
Definition zig_g_fun@{} (z : zig_pt) : bool :=
  match z with zig_c => true | _ => false end.

Definition zig_f_set@{o} :
  SetoidMorphism@{o o o} zig_setoid@{o} bool_setoid_object@{o o}.
Proof.
  refine {| morphism := fun _ : zig_pt => false |}.
  intros x y _; reflexivity.
Defined.

Definition zig_g_set@{o} :
  SetoidMorphism@{o o o} zig_setoid@{o} bool_setoid_object@{o o}.
Proof.
  refine {| morphism := zig_g_fun |}.
  intros x y e; simpl in e; subst; reflexivity.
Defined.

Definition zig_f_map@{o} : PMor@{o} PZig@{o} PTwoIndisc@{o} :=
  pindisc_mor bool_setoid_object@{o o} PZig@{o} zig_f_set@{o}.

Definition zig_g_map@{o} : PMor@{o} PZig@{o} PTwoIndisc@{o} :=
  pindisc_mor bool_setoid_object@{o o} PZig@{o} zig_g_set@{o}.

(* 相关说明。 （已译） *)
Definition zig_e_fun@{} (b : bool) : zig_pt := if b then zig_a else zig_b.

Definition zig_e_set@{o} :
  SetoidMorphism@{o o o} bool_setoid_object@{o o} zig_setoid@{o}.
Proof.
  refine {| morphism := zig_e_fun |}.
  intros x y e; simpl in e; subst; reflexivity.
Defined.

Definition zig_e_map@{o} : PMor@{o} PBool@{o} PZig@{o} :=
  pdisc_mor bool_setoid_object@{o o} PZig@{o} zig_e_set@{o}.

Definition zig_lift_fun@{} (z : zig_pt) : bool :=
  match z with zig_a => true | zig_b => false | zig_c => true end.

Lemma PTop_zig_equalizer@{o so | o < so +} :
  @IsEqualizer PTopCat@{o so} PZig@{o} PTwoIndisc@{o}
    zig_f_map@{o} zig_g_map@{o} PBool@{o} zig_e_map@{o}.
Proof.
  unshelve econstructor.
  - intros [|]; reflexivity.
  - intros W k Hk.
    assert (Hnc : ∀ w, pmap k w <> zig_c).
    { intros w Hw. pose proof (Hk w) as H. simpl in H.
      rewrite Hw in H. discriminate H. }
    unshelve eexists.
    + unshelve refine (Build_PMor W PBool
        {| morphism := fun w => zig_lift_fun (pmap k w) |} _).
      * intros w1 w2 Hw. simpl. f_equal.
        exact (proper_morphism (pmap k) _ _ Hw).
      * intros V HV.
        apply (popen_respects W
                 (fun w => (fun z => match z with
                                     | zig_a => V true | zig_b => V false
                                     | zig_c => False end) (pmap k w))).
        -- intro w. simpl. pose proof (Hnc w) as Hn.
           destruct (pmap k w); simpl; try tauto; contradiction.
        -- exact (pcont k (fun z => match z with
                                      | zig_a => V true | zig_b => V false
                                      | zig_c => False end)
                        (fun H => False_ind _ H)).
    + intro w. simpl. pose proof (Hnc w) as Hn.
      destruct (pmap k w); simpl; try reflexivity; contradiction.
    + intros v Hv w. simpl. pose proof (Hv w) as H. simpl in H.
      destruct (pmap v w), (pmap k w); simpl in *; congruence.
Qed.

(* The same fork in [Lconn], by fullness. *)
Definition LZig@{o so | o < so +} : Lconn@{o so} :=
  (PZig@{o}; PZig_PLocConn@{o}).

Definition LBool@{o so | o < so +} : Lconn@{o so} :=
  (PBool@{o}; pdisc_locconn bool_setoid_object@{o o}).

Definition zig_f@{o so | o < so +} :
  LZig@{o so} ~{Lconn@{o so}}~> LTwoIndisc@{o so} := (zig_f_map@{o}; I).

Definition zig_g@{o so | o < so +} :
  LZig@{o so} ~{Lconn@{o so}}~> LTwoIndisc@{o so} := (zig_g_map@{o}; I).

Definition zig_e@{o so | o < so +} :
  LBool@{o so} ~{Lconn@{o so}}~> LZig@{o so} := (zig_e_map@{o}; I).

Lemma Lconn_zig_equalizer@{o so | o < so +} :
  @IsEqualizer Lconn@{o so} LZig@{o so} LTwoIndisc@{o so}
    zig_f@{o so} zig_g@{o so} LBool@{o so} zig_e@{o so}.
Proof.
  pose proof PTop_zig_equalizer@{o so} as E.
  unshelve econstructor.
  - exact (fork_eq E).
  - intros W k Hk.
    destruct (eq_desc E (`1 k) Hk) as [u Hu Huniq].
    exists (u; I).
    + exact Hu.
    + intros v Hv. exact (Huniq (`1 v) Hv).
Qed.

(* The discrete two-point space has two components. *)
Lemma pbool_two_components@{o} : comp_rel PBool@{o} true false → False.
Proof.
  intros [W [HW [wt wf]]].
  assert (L : LocConstOn PBool W (fun b => b = true)).
  { intros z _. exists (fun w => w = z). split; [|split; [reflexivity|]].
    - intros x y e h; simpl in e; subst; reflexivity.
    - intros w _ e; subst; tauto. }
  discriminate (HW _ L true false wt wf eq_refl).
Qed.

(* The one-point propositional set. *)
Definition PSetsOne@{o so | o < so +} : PSets@{o so} :=
  (unit_setoid_object@{o o}; unit_PropEquiv@{o o}).

(* 相关说明。 （已译） *)
Theorem components_zig_not_preserved@{o so | o < so +} :
  @IsEqualizer PSets@{o so} _ _
    (fmap[components_functor@{o so}] zig_f@{o so})
    (fmap[components_functor@{o so}] zig_g@{o so})
    (components_functor@{o so} LBool@{o so})
    (fmap[components_functor@{o so}] zig_e@{o so}) → False.
Proof.
  intro HE.
  pose proof (equalizer_monic _ _ HE) as M.
  pose (k1 := ({| morphism := fun _ : unit_setoid_object@{o o} => true;
                  proper_morphism := fun _ _ _ => reflexivity _ |}; I)
              : PSetsOne@{o so} ~{PSets@{o so}}~>
                  components_functor@{o so} LBool@{o so}).
  pose (k2 := ({| morphism := fun _ : unit_setoid_object@{o o} => false;
                  proper_morphism := fun _ _ _ => reflexivity _ |}; I)
              : PSetsOne@{o so} ~{PSets@{o so}}~>
                  components_functor@{o so} LBool@{o so}).
  assert (Hk : fmap[components_functor@{o so}] zig_e@{o so} ∘ k1
                 ≈ fmap[components_functor@{o so}] zig_e@{o so} ∘ k2).
  { intro t. exact (PZig_one_component zig_a zig_b). }
  exact (pbool_two_components (@monic _ _ _ _ M _ k1 k2 Hk ttt)).
Qed.

(* Hence C has no left adjoint: a right adjoint preserves the equalizer. *)
Theorem components_no_left_adjoint@{o so +| o < so +}
  (L : PSets@{o so} ⟶ Lconn@{o so}) (B : L ⊣ components_functor@{o so}) :
  False.
Proof.
  exact (not_PreservesEqualizers_no_left_adjoint _ _ _ _
           Lconn_zig_equalizer@{o so} components_zig_not_preserved@{o so}
           L B).
Qed.

(* The same ANY 左伴随 D, whatever 定义: unit
 at three-point space continuous discrete space, so it
 identifies two images equalizer. （已译） *)
Theorem discrete_left_adjoint_not_preserved@{o so +| o < so +}
  (C : Lconn@{o so} ⟶ PSets@{o so}) (A : C ⊣ PSetsDisc@{o so}) :
  @IsEqualizer PSets@{o so} _ _ (fmap[C] zig_f@{o so}) (fmap[C] zig_g@{o so})
    (C LBool@{o so}) (fmap[C] zig_e@{o so}) → False.
Proof.
  intro EC.
  pose proof (equalizer_monic _ _ EC) as M.
  pose (etaX := @unit _ _ _ _ A LZig).
  pose (etaE := @unit _ _ _ _ A LBool).
  assert (Hconn : ∀ z, inhabited (pmap (`1 etaX) z ≈ pmap (`1 etaX) zig_c)).
  { intro z.
    pose proof (pcont (`1 etaX)
                  (fun s => inhabited (s ≈ pmap (`1 etaX) zig_c))) as Hc.
    assert (Ho : POpen (PDiscrete (`1 (C LZig)))
                   (fun s => inhabited (s ≈ pmap (`1 etaX) zig_c))).
    { intros a b Hab [Ha]. constructor.
      exact (transitivity (symmetry Hab) Ha). }
    specialize (Hc Ho). simpl in Hc.
    destruct z.
    - exact (proj1 (Hc (inhabits (reflexivity _)))).
    - exact (inhabits (reflexivity _)).
    - exact (proj2 (Hc (inhabits (reflexivity _)))). }
  destruct (Hconn zig_a) as [Ha], (Hconn zig_b) as [Hb].
  assert (Nat : etaX ∘ zig_e ≈ fmap[PSetsDisc] (fmap[C] zig_e) ∘ etaE).
  { unfold etaX, etaE, unit.
    rewrite <- (@to_adj_nat_l _ _ _ _ A).
    rewrite <- (@to_adj_nat_r _ _ _ _ A).
    exact (to_adj_respects (H := A) _ _
             (transitivity (id_left _) (symmetry (id_right _)))). }
  assert (Hid : pmap (`1 etaE) true ≈ pmap (`1 etaE) false).
  { pose (k1 := ({| morphism := fun _ : unit_setoid_object@{o o} =>
                                  pmap (`1 etaE) true;
                    proper_morphism := fun _ _ _ => reflexivity _ |}; I)
                : PSetsOne@{o so} ~{PSets@{o so}}~> fobj[C] LBool).
    pose (k2 := ({| morphism := fun _ : unit_setoid_object@{o o} =>
                                  pmap (`1 etaE) false;
                    proper_morphism := fun _ _ _ => reflexivity _ |}; I)
                : PSetsOne@{o so} ~{PSets@{o so}}~> fobj[C] LBool).
    assert (Hk : fmap[C] zig_e ∘ k1 ≈ fmap[C] zig_e ∘ k2).
    { intro t. simpl.
      transitivity (pmap (`1 etaX) zig_a); [symmetry; exact (Nat true)|].
      transitivity (pmap (`1 etaX) zig_c); [exact Ha|].
      transitivity (pmap (`1 etaX) zig_b); [symmetry; exact Hb|].
      exact (Nat false). }
    exact (@monic _ _ _ _ M _ k1 k2 Hk ttt). }
  pose (BoolP := (bool_setoid_object@{o o}; eq_PropEquiv bool)
                 : PSets@{o so}).
  pose (sep := (pdisc_mor bool_setoid_object@{o o}
                  (PDiscrete bool_setoid_object@{o o})
                  setoid_morphism_id; I)
               : LBool ~{Lconn@{o so}}~> PSetsDisc BoolP).
  pose (hsep := from (@adj _ _ _ _ A LBool BoolP) sep).
  assert (Hs : ∀ b, `1 hsep (pmap (`1 etaE) b) ≈ b).
  { intro b.
    pose proof (@to_adj_unit _ _ _ _ A _ _ hsep) as T.
    pose proof (from_adj_comp_law (H := A) sep) as T2.
    exact (transitivity (symmetry T) T2 b). }
  pose proof (proper_morphism (`1 hsep) _ _ Hid) as H3.
  assert (Hbad : @equiv _ bool_setoid_object@{o o} true false).
  { exact (transitivity (symmetry (Hs true)) (transitivity H3 (Hs false))). }
  discriminate Hbad.
Qed.

Theorem discrete_left_adjoint_no_left_adjoint@{o so ua ub +| o < so +}
  (C : Lconn@{o so} ⟶ PSets@{o so})
  (A : @Adjunction@{so o o so o o o o ua o _} PSets@{o so} Lconn@{o so}
         C PSetsDisc@{o so})
  (L : PSets@{o so} ⟶ Lconn@{o so})
  (B : @Adjunction@{so o o so o o o o ub o _} Lconn@{o so} PSets@{o so}
         L C) : False.
Proof.
  exact (not_PreservesEqualizers_no_left_adjoint _ _ _ _
           Lconn_zig_equalizer@{o so}
           (discrete_left_adjoint_not_preserved C A) L B).
Qed.

(* 相关说明。 （已译） *)

(* The empty space, discrete. *)
Definition LEmpty@{o so | o < so +} : Lconn@{o so} :=
  LDisc@{o so} Concrete.empty_setoid_object@{o o}.

Definition swap_set@{o} :
  SetoidMorphism@{o o o} bool_setoid_object@{o o} bool_setoid_object@{o o}.
Proof.
  refine {| morphism := negb |}.
  intros x y e; simpl in e; subst; reflexivity.
Defined.

Definition swap_map@{o} : PMor@{o} PTwoIndisc@{o} PTwoIndisc@{o} :=
  pindisc_mor bool_setoid_object@{o o} PTwoIndisc@{o} swap_set@{o}.

Definition empty_set_map@{o} :
  SetoidMorphism@{o o o} Concrete.empty_setoid_object@{o o} PTwoIndisc@{o}.
Proof.
  refine {| morphism := fun x : False => match x with end |}.
  intros x; destruct x.
Defined.

Definition swap_L@{o so | o < so +} :
  LTwoIndisc@{o so} ~{Lconn@{o so}}~> LTwoIndisc@{o so} := (swap_map@{o}; I).

Definition swap_e@{o so | o < so +} :
  LEmpty@{o so} ~{Lconn@{o so}}~> LTwoIndisc@{o so} :=
  (pdisc_mor Concrete.empty_setoid_object@{o o} PTwoIndisc@{o}
     empty_set_map@{o}; I).

Lemma negb_no_fixpoint@{} (b : bool) : b = negb b → False.
Proof. destruct b; discriminate. Qed.

(* The equalizer 恒等 swap empty space. （已译） *)
Lemma Lconn_swap_equalizer@{o so | o < so +} :
  @IsEqualizer Lconn@{o so} LTwoIndisc@{o so} LTwoIndisc@{o so}
    id swap_L@{o so} LEmpty@{o so} swap_e@{o so}.
Proof.
  unshelve econstructor.
  - intro x; destruct x.
  - intros z h Hh.
    assert (Hno : ∀ p : pt_carrier (`1 z), False).
    { intro p. apply (negb_no_fixpoint (pmap (`1 h) p)). exact (Hh p). }
    unshelve refine {| unique_obj := _ |}.
    + unshelve refine (_; I).
      unshelve refine (@Build_PMor (`1 z)
                         (PDiscrete Concrete.empty_setoid_object@{o o})
                         {| morphism := fun p => match Hno p with end |} _).
      * intros p; destruct (Hno p).
      * intros U HU. apply (popen_respects _ (fun _ => False)).
        -- intro p; destruct (Hno p).
        -- apply popen_empty.
    + intro p; destruct (Hno p).
    + intros v _ p; destruct (Hno p).
Qed.

(* C does not preserve it: one component two-point space a
 fork 进入 empty set. （已译） *)
Theorem components_swap_not_preserved@{o so | o < so +} :
  @IsEqualizer PSets@{o so} _ _ (fmap[components_functor@{o so}] id)
    (fmap[components_functor@{o so}] swap_L@{o so})
    (components_functor@{o so} LEmpty@{o so})
    (fmap[components_functor@{o so}] swap_e@{o so}) → False.
Proof.
  intro HE.
  pose (k := ({| morphism := fun _ : unit_setoid_object@{o o} => true;
                 proper_morphism := fun _ _ _ => reflexivity _ |}; I)
             : PSetsOne@{o so} ~{PSets@{o so}}~>
                 components_functor@{o so} LTwoIndisc@{o so}).
  assert (Hk : fmap[components_functor@{o so}] id ∘ k
                 ≈ fmap[components_functor@{o so}] swap_L@{o so} ∘ k).
  { intro t. exists (fun _ => True).
    exact (conj PTwoIndisc_connected (conj I I)). }
  destruct (eq_desc HE k Hk) as [v _ _].
  exact (`1 v ttt).
Qed.

(* * ** Outside [Lconn]: D all [PTopCat] has no 左伴随 （已译） *)

(* 相关说明。 （已译） *)
Lemma pconv_not_locconn@{o} : PLocConn PConv@{o} → False.
Proof.
  intro LC.
  destruct (LC None (fun _ => True) (popen_whole _) I)
    as [N [HN [nN [_ HC]]]].
  destruct (HN nN) as [K HK].
  assert (L : LocConstOn PConv N (fun z => z = Some K)).
  { intros z _. destruct z as [m|].
    - exists (fun w => w = Some m). split; [|split; [reflexivity|]].
      + intro H; discriminate H.
      + intros w _ e; subst; tauto.
    - exists (fun w => match w with
                       | None => True
                       | Some m => (S K <= m)%nat end).
      split; [|split; [exact I|]].
      + intros _. exists (S K). intros m Hm; exact Hm.
      + intros w _ Hw. destruct w as [m|]; [|tauto].
        split; intro e; [injection e as e; subst; exfalso;
                          exact (Nat.nle_succ_diag_l _ Hw)|discriminate]. }
  discriminate (HC _ L (Some K) None (HK K (le_n K)) nN eq_refl).
Qed.

(* 相关说明。 （已译） *)
Definition PSetsDiscTop@{o so | o < so +} : PSets@{o so} ⟶ PTopCat@{o so} :=
  @Compose@{so so so so o} PSets@{o so} Sets@{o so} PTopCat@{o so}
    PDisc@{o so} (Incl@{so o so o so so} Sets@{o so} PSetsSub@{o so}).

Theorem discrete_no_left_adjoint_on_PTop@{o so +| o < so +}
  (C' : PTopCat@{o so} ⟶ PSets@{o so}) (A : C' ⊣ PSetsDiscTop@{o so}) :
  False.
Proof.
  pose (Q := C' PConv).
  pose (eta := to (@adj _ _ _ _ A PConv Q) id).
  pose (P := `2 Q).
  (* 相关说明。 （已译） *)
  assert (Hopen : POpen PConv
            (fun z => @pequiv _ _ P (pmap eta z) (pmap eta None))).
  { apply (pcont eta (fun s => @pequiv _ _ P s (pmap eta None))).
    intros s t e p. apply pequiv_from.
    exact (transitivity (symmetry e) (pequiv_to _ _ p)). }
  destruct (Hopen (pequiv_from _ _ (reflexivity _))) as [N HN].
  pose (BoolP := (bool_setoid_object@{o o}; eq_PropEquiv bool)
                 : PSets@{o so}).
  pose (f := pconv_ind_mor@{o} N
             : PConv ~{PTopCat@{o so}}~> PSetsDiscTop BoolP).
  pose (g := from (@adj _ _ _ _ A PConv BoolP) f).
  assert (Hf : ∀ z, pmap f z = (`1 g) (pmap eta z)).
  { intro z.
    pose proof (iso_to_from (@adj _ _ _ _ A PConv BoolP) f z) as E1.
    pose proof (@to_adj_nat_r _ _ _ _ A PConv Q BoolP g id z) as E2.
    pose proof (proper_morphism (to (@adj _ _ _ _ A PConv BoolP)) _ _
                  (id_right g) z) as E3.
    simpl in E1, E2, E3.
    exact (eq_trans (eq_sym E1) (eq_trans (eq_sym E3) E2)). }
  pose proof (Hf (Some N)) as HN1. pose proof (Hf None) as HN0.
  pose proof (proper_morphism (`1 g) _ _
                (pequiv_to _ _ (HN N (le_n N)))) as Hg.
  simpl in HN1, HN0, Hg.
  rewrite Nat.eqb_refl in HN1.
  rewrite <- HN1, <- HN0 in Hg. discriminate Hg.
Qed.

(* The same all [Sets]: Instance/Top/Complete.v's [PDisc] has no
 左伴随. The open set now truncation, eliminated 进入
 goal [False]. （已译） *)
Theorem PDisc_no_left_adjoint@{o so +| o < so +}
  (C' : PTopCat@{o so} ⟶ Sets@{o so}) (A : C' ⊣ PDisc@{o so}) : False.
Proof.
  pose (Q := C' PConv).
  pose (eta := to (@adj _ _ _ _ A PConv Q) id).
  assert (Hopen : POpen PConv
            (fun z => inhabited (pmap eta z ≈ pmap eta None))).
  { apply (pcont eta (fun s => inhabited (s ≈ pmap eta None))).
    intros s t e [p]. exact (inhabits (transitivity (symmetry e) p)). }
  destruct (Hopen (inhabits (reflexivity _))) as [N HN].
  pose (f := pconv_ind_mor@{o} N
             : PConv ~{PTopCat@{o so}}~> PDisc bool_setoid_object@{o o}).
  pose (g := from (@adj _ _ _ _ A PConv bool_setoid_object@{o o}) f).
  assert (Hf : ∀ z, pmap f z = g (pmap eta z)).
  { intro z.
    pose proof (iso_to_from (@adj _ _ _ _ A PConv bool_setoid_object) f z)
      as E1.
    pose proof (@to_adj_nat_r _ _ _ _ A PConv Q bool_setoid_object g id z)
      as E2.
    pose proof (proper_morphism (to (@adj _ _ _ _ A PConv bool_setoid_object))
                  _ _ (id_right g) z) as E3.
    simpl in E1, E2, E3.
    exact (eq_trans (eq_sym E1) (eq_trans (eq_sym E3) E2)). }
  destruct (HN N (le_n N)) as [e].
  pose proof (Hf (Some N)) as HN1. pose proof (Hf None) as HN0.
  pose proof (proper_morphism g _ _ e) as Hg.
  simpl in HN1, HN0, Hg.
  rewrite Nat.eqb_refl in HN1.
  rewrite <- HN1, <- HN0 in Hg. discriminate Hg.
Qed.
