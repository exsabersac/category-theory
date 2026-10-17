(* 相关说明。 （已译） *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Rep.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Adjunction.Right.

(*
   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(*
   nLab: https://ncatlab.org/nlab/show/Galois+connection
   nLab: https://ncatlab.org/nlab/show/group+action
   nLab: https://ncatlab.org/nlab/show/closure+operator
   nLab: https://ncatlab.org/nlab/show/stabilizer+group
   nLab: https://ncatlab.org/nlab/show/fixed+point
   Wikipedia: https://en.wikipedia.org/wiki/Galois_connection
   Wikipedia:
   https://en.wikipedia.org/wiki/Fundamental_theorem_of_Galois_theory

   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)

Section GaloisClosure.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (PA : PreOrder RA) (PB : PreOrder RB).
Context (Gc : GaloisConnection RA RB).

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition gal_lrl_below (a : A) :
  RB (gal_l Gc (gal_r Gc (gal_l Gc a))) (gal_l Gc a) :=
  gal_counit Gc PA (gal_l Gc a).

Definition gal_lrl_above (a : A) :
  RB (gal_l Gc a) (gal_l Gc (gal_r Gc (gal_l Gc a))) :=
  gal_mono_l Gc (gal_unit Gc PB a).

(* [R q <= R L R q <= R q], the mirror. *)
Definition gal_rlr_below (b : B) :
  RA (gal_r Gc (gal_l Gc (gal_r Gc b))) (gal_r Gc b) :=
  gal_mono_r Gc (gal_counit Gc PA b).

Definition gal_rlr_above (b : B) :
  RA (gal_r Gc b) (gal_r Gc (gal_l Gc (gal_r Gc b))) :=
  gal_unit Gc PB (gal_r Gc b).

(* 相关说明。 （已译） *)
Definition GalClosed_l (b : B) : Prop := RB b (gal_l Gc (gal_r Gc b)).
Definition GalClosed_r (a : A) : Prop := RA (gal_r Gc (gal_l Gc a)) a.

Definition gal_closed_l_image (a : A) : GalClosed_l (gal_l Gc a) :=
  gal_lrl_above a.

Definition gal_closed_r_image (b : B) : GalClosed_r (gal_r Gc b) :=
  gal_rlr_below b.

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma gal_closed_l_iff (b : B) :
  GalClosed_l b ↔ ∃ a, RB b (gal_l Gc a) ∧ RB (gal_l Gc a) b.
Proof using A B Gc PA PB RA RB.
  split.
  - intro H; exists (gal_r Gc b); exact (H, gal_counit Gc PA b).
  - intros [a [Hba Hab]].
    exact (@transitivity B RB (@PreOrder_Transitive B RB PB) _ _ _ Hba
             (@transitivity B RB (@PreOrder_Transitive B RB PB) _ _ _
                (gal_lrl_above a)
                (gal_mono_l Gc (gal_mono_r Gc Hab)))).
Qed.

Lemma gal_closed_r_iff (a : A) :
  GalClosed_r a ↔ ∃ b, RA a (gal_r Gc b) ∧ RA (gal_r Gc b) a.
Proof using A B Gc PA PB RA RB.
  split.
  - intro H; exists (gal_l Gc a); exact (gal_unit Gc PB a, H).
  - intros [b [Hab Hba]].
    exact (@transitivity A RA (@PreOrder_Transitive A RA PA) _ _ _
             (@transitivity A RA (@PreOrder_Transitive A RA PA) _ _ _
                (gal_mono_r Gc (gal_mono_l Gc Hab))
                (gal_rlr_below b))
             Hba).
Qed.

End GaloisClosure.

(* ------------------------------------------------------------------------ *)
(* * ** (B) Mutual 含入 [equiv] subsets （已译） *)

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition subset_le_antisym@{o} {X : SetoidObject@{o o}}
  {S T : carrier (Powerset_Prop_obj@{o} X)}
  (H1 : subset_le@{o} S T) (H2 : subset_le@{o} T S) : S ≈ T :=
  fun x => conj (H1 x) (H2 x).

(*
   本节说明（余）极限相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example op_rel_is_flip {A : Type} (R : relation A) :
  op_rel R = Basics.flip R := eq_refl.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

Section Action.

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Universe o su gu.
Constraint Set < o.
Constraint o <= gu.

Context (G : GrpObject@{gu o o}).
Context (A : MSetoidAction@{o o gu gu gu o o gu} (grp_mon@{gu o o} G)).

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition fixes (s : carrier (grp_setoid G))
                 (x : carrier (act_setoid A)) : Prop :=
  Powerset_squash@{o} (act A s x ≈ x).

(* [L X], the set of group elements fixing every point of [X].
   Respectfulness in [s] is [act_respects]. *)
Definition stab (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  carrier (Powerset_Prop_obj@{o} (grp_setoid G)).
Proof using A G.
  unshelve refine (@Build_SetoidMorphism@{o o o}
    (carrier (grp_setoid G)) (is_setoid (grp_setoid G))
    Prop (is_setoid Powerset_Prop_truth@{o})
    (fun s => ∀ x, X x → fixes s x) _).
  intros s s' Hss'; split; intros H x Hx; specialize (H x Hx);
    refine (H _ _); intro Hfix; apply Powerset_squash_intro@{o}.
  - rewrite <- Hss'; exact Hfix.
  - rewrite Hss'; exact Hfix.
Defined.

(* [R S], the set of points fixed by every element of [S]. *)
Definition fixed (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  carrier (Powerset_Prop_obj@{o} (act_setoid A)).
Proof using A G.
  unshelve refine (@Build_SetoidMorphism@{o o o}
    (carrier (act_setoid A)) (is_setoid (act_setoid A))
    Prop (is_setoid Powerset_Prop_truth@{o})
    (fun x => ∀ s, S s → fixes s x) _).
  intros x y Hxy; split; intros H s Hs; specialize (H s Hs);
    refine (H _ _); intro Hfix; apply Powerset_squash_intro@{o}.
  - rewrite <- Hxy; exact Hfix.
  - rewrite Hxy; exact Hfix.
Defined.

(* The two memberships, nose. Equations between [Prop]s, i.e.
 between OBJECTS, not between 态射. （已译） *)
Example stab_mem (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  (s : carrier (grp_setoid G)) :
  stab X s = (∀ x, X x → fixes s x) := eq_refl.

Example fixed_mem (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G)))
  (x : carrier (act_setoid A)) :
  fixed S x = (∀ s, S s → fixes s x) := eq_refl.

(* Mac Lane's middle term: "sigma . x = x all sigma S all x in
 X". It SAME TERM [Q]-side 含入. （已译） *)
Definition FixesAll (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
                    (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G)))
  : Prop := ∀ s, S s → ∀ x, X x → fixes s x.

Example stab_transpose_strict
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  subset_le@{o} S (stab X) = FixesAll X S := eq_refl.

(* 相关说明。 （已译） *)
Lemma fixed_transpose_iff
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  subset_le@{o} X (fixed S) <-> FixesAll X S.
Proof using A G. split; intros H a Ha b Hb; exact (H b Hb a Ha). Qed.

(* 相关说明。 （已译） *)
Lemma stab_antitone (X X' : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  subset_le@{o} X X' → subset_le@{o} (stab X') (stab X).
Proof using A G. intros H s Hs x Hx; exact (Hs x (H x Hx)). Qed.

Lemma fixed_antitone (S S' : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  subset_le@{o} S S' → subset_le@{o} (fixed S') (fixed S).
Proof using A G. intros H x Hx s Hs; exact (Hx s (H s Hs)). Qed.

(* THE GALOIS CONNECTION. All six fields name; second 关系 is
 REVERSED 含入 P(G), Mac Lane's [Q^op]. （已译） *)
Definition group_action_galois :
  GaloisConnection (@subset_le@{o} (act_setoid A))
                   (op_rel (@subset_le@{o} (grp_setoid G))) :=
  {| gal_l := stab
   ; gal_r := fixed
   ; gal_mono_l := stab_antitone
   ; gal_mono_r := fun S T H => fixed_antitone T S H
   ; gal_to   := fun X S H => proj2 (fixed_transpose_iff X S) H
   ; gal_from := fun X S H => proj1 (fixed_transpose_iff X S) H |}.

(* 相关说明。 （已译） *)
Definition stab_PreOrder_U : PreOrder (@subset_le@{o} (act_setoid A)) :=
  subset_le_preorder@{o} (act_setoid A).

Definition stab_PreOrder_G :
  PreOrder (op_rel (@subset_le@{o} (grp_setoid G))) :=
  op_PreOrder (subset_le_preorder@{o} (grp_setoid G)).

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition stab_Subgroup
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) : Subgroup G.
Proof using A G.
  unshelve econstructor.
  - exact (fun s => stab X s).
  - intros a b Hab Ha.
    exact (proj1 (@proper_morphism _ _ _ _ (stab X) a b Hab) Ha).
  - intros x Hx; apply Powerset_squash_intro@{o}; exact (act_unit A x).
  - intros a b Ha Hb x Hx.
    refine (Ha x Hx _ _); intro Hax.
    refine (Hb x Hx _ _); intro Hbx.
    apply Powerset_squash_intro@{o}.
    rewrite (act_op A a b x); rewrite Hbx; exact Hax.
  - intros a Ha x Hx.
    refine (Ha x Hx _ _); intro Hax.
    apply Powerset_squash_intro@{o}.
    rewrite <- Hax at 1.
    rewrite <- (act_op A (grp_inv G a) a x).
    rewrite (grp_mul_inv_l G a).
    exact (act_unit A x).
Defined.

Example stab_Subgroup_mem
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  (s : carrier (grp_setoid G)) :
  sub_mem (stab_Subgroup X) s = stab X s := eq_refl.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma stab_fixed_stab
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  stab (fixed (stab X)) ≈ stab X.
Proof using A G.
  apply subset_le_antisym.
  - exact (gal_lrl_above stab_PreOrder_G group_action_galois X).
  - exact (gal_lrl_below stab_PreOrder_U group_action_galois X).
Qed.

Lemma fixed_stab_fixed
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  fixed (stab (fixed S)) ≈ fixed S.
Proof using A G.
  apply subset_le_antisym.
  - exact (gal_rlr_below stab_PreOrder_U group_action_galois S).
  - exact (gal_rlr_above stab_PreOrder_G group_action_galois S).
Qed.

(* Both operators respect [equiv], from antitonicity read both ways. *)
Lemma stab_respects
  (X X' : carrier (Powerset_Prop_obj@{o} (act_setoid A))) (H : X ≈ X') :
  stab X ≈ stab X'.
Proof using A G.
  apply subset_le_antisym.
  - exact (stab_antitone X' X (fun x Hx => proj2 (H x) Hx)).
  - exact (stab_antitone X X' (fun x Hx => proj1 (H x) Hx)).
Qed.

Lemma fixed_respects
  (S S' : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) (H : S ≈ S') :
  fixed S ≈ fixed S'.
Proof using A G.
  apply subset_le_antisym.
  - exact (fixed_antitone S' S (fun x Hx => proj2 (H x) Hx)).
  - exact (fixed_antitone S S' (fun x Hx => proj1 (H x) Hx)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (F) The closed elements *)

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ClosedG (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G)))
  : Prop := subset_le@{o} (stab (fixed S)) S.

Definition ClosedU (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  : Prop := subset_le@{o} (fixed (stab X)) X.

Example ClosedG_is_GalClosed_l
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  ClosedG S = GalClosed_l group_action_galois S := eq_refl.

Example ClosedU_is_GalClosed_r
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  ClosedU X = GalClosed_r group_action_galois X := eq_refl.

Definition closed_G_stab (X : carrier (Powerset_Prop_obj@{o} (act_setoid A)))
  : ClosedG (stab X) :=
  gal_closed_l_image stab_PreOrder_G group_action_galois X.

Definition closed_U_fixed
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) : ClosedU (fixed S) :=
  gal_closed_r_image stab_PreOrder_U group_action_galois S.

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma closed_G_iff (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  ClosedG S ↔ ∃ X, S ≈ stab X.
Proof using A G.
  split.
  - intro H.
    destruct (fst (gal_closed_l_iff stab_PreOrder_U stab_PreOrder_G
                     group_action_galois S) H) as [X [H1 H2]].
    exists X; exact (subset_le_antisym H2 H1).
  - intros [X HX].
    refine (snd (gal_closed_l_iff stab_PreOrder_U stab_PreOrder_G
                   group_action_galois S) _).
    exists X; exact (fun s Hs => proj2 (HX s) Hs,
                     fun s Hs => proj1 (HX s) Hs).
Qed.

Lemma closed_U_iff (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  ClosedU X ↔ ∃ S, X ≈ fixed S.
Proof using A G.
  split.
  - intro H.
    destruct (fst (gal_closed_r_iff stab_PreOrder_U stab_PreOrder_G
                     group_action_galois X) H) as [S [H1 H2]].
    exists S; exact (subset_le_antisym H1 H2).
  - intros [S HS].
    refine (snd (gal_closed_r_iff stab_PreOrder_U stab_PreOrder_G
                   group_action_galois X) _).
    exists S; exact (fun x Hx => proj1 (HS x) Hx,
                     fun x Hx => proj2 (HS x) Hx).
Qed.

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition closed_G_Subgroup
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) (H : ClosedG S)
  : Subgroup G.
Proof using A G.
  unshelve econstructor.
  - exact (fun s => S s).
  - intros a b Hab Ha.
    exact (proj1 (@proper_morphism _ _ _ _ S a b Hab) Ha).
  - exact (H _ (sub_unit (stab_Subgroup (fixed S)))).
  - intros a b Ha Hb.
    refine (H _ (sub_mul (stab_Subgroup (fixed S)) a b _ _)).
    + exact (gal_counit group_action_galois stab_PreOrder_U S a Ha).
    + exact (gal_counit group_action_galois stab_PreOrder_U S b Hb).
  - intros a Ha.
    refine (H _ (sub_inv (stab_Subgroup (fixed S)) a _)).
    exact (gal_counit group_action_galois stab_PreOrder_U S a Ha).
Defined.

Example closed_G_Subgroup_mem
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) (H : ClosedG S)
  (s : carrier (grp_setoid G)) :
  sub_mem (closed_G_Subgroup S H) s = S s := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** (G) The adjunction *)

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition StabFunctor :
  Subsets@{o su} (act_setoid A) ⟶ Proset@{o su} stab_PreOrder_G :=
  GaloisFunctor_l stab_PreOrder_U stab_PreOrder_G group_action_galois.

Definition FixedFunctor :
  Proset@{o su} stab_PreOrder_G ⟶ Subsets@{o su} (act_setoid A) :=
  GaloisFunctor_r stab_PreOrder_U stab_PreOrder_G group_action_galois.

Definition group_action_adjunction : StabFunctor ⊣ FixedFunctor :=
  GaloisAdjunction stab_PreOrder_U stab_PreOrder_G group_action_galois.

Example StabFunctor_obj
  (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  fobj[StabFunctor] X = stab X := eq_refl.

Example FixedFunctor_obj
  (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  fobj[FixedFunctor] S = fixed S := eq_refl.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example galois_PG_obj :
  obj[Proset@{o su} stab_PreOrder_G]
    = obj[(Subsets@{o su} (grp_setoid G))^op] := eq_refl.

Example galois_PG_hom
  (S T : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  (S ~{Proset@{o su} stab_PreOrder_G}~> T)
    = (S ~{(Subsets@{o su} (grp_setoid G))^op}~> T) := eq_refl.


(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明伴随、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := simpl; repeat intro; exact I.

Program Definition StabOp :
  (Subsets@{o su} (act_setoid A))^op ⟶ Subsets@{o su} (grp_setoid G) := {|
  fobj := stab;
  fmap := fun X X' f => stab_antitone X' X f
|}.

Program Definition FixedOp :
  (Subsets@{o su} (grp_setoid G))^op ⟶ Subsets@{o su} (act_setoid A) := {|
  fobj := fixed;
  fmap := fun S S' f => fixed_antitone S' S f
|}.

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition group_action_AdjointOnTheRight :
  AdjointOnTheRight StabOp FixedOp := {|
  aor := fun X S =>
    {| to   := {| morphism := fun h => proj1 (fixed_transpose_iff X S) h |}
     ; from := {| morphism := fun h => proj2 (fixed_transpose_iff X S) h |} |}
|}.

Example StabOp_obj (X : carrier (Powerset_Prop_obj@{o} (act_setoid A))) :
  fobj[StabOp] X = stab X := eq_refl.

Example FixedOp_obj (S : carrier (Powerset_Prop_obj@{o} (grp_setoid G))) :
  fobj[FixedOp] S = fixed S := eq_refl.

End Action.

Arguments fixes {G A} s x.
Arguments stab {G A} X.
Arguments fixed {G A} S.
Arguments FixesAll {G A} X S.
(* [A] stays EXPLICIT [ClosedG]: 论元 [S] subset the
 GROUP, determines [G] but not action. （已译） *)
Arguments ClosedG {G} A S.
Arguments ClosedU {G A} X.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition galois_two@{wo} : SetoidObject@{wo wo} :=
  {| carrier := bool ; is_setoid := eq_Setoid@{wo} bool |}.

(* 相关说明。 （已译） *)
Definition GalZ2@{wo} : GrpObject@{wo wo wo}.
Proof.
  unshelve refine {| grp_setoid := galois_two@{wo}
                   ; grp_unit := false
                   ; grp_mul := xorb
                   ; grp_inv := fun b : bool => b
                   ; grp_prop := eq_PropEquiv@{wo} bool |}.
  - exact (fun x y Hxy u v Huv => f_equal2 xorb Hxy Huv).
  - intros [|] [|] [|]; reflexivity.
  - intros [|]; reflexivity.
  - intros [|]; reflexivity.
Defined.

(* Z/2 acting on two points by the flip.  [act_respects] is supplied by
   hand rather than left to resolution, so that no instance search can pin
   a universe (the hazard Theory/Universal/Element.v records). *)
Definition GalZ2Act@{wo +} : MSetoidAction (grp_mon GalZ2@{wo}).
Proof.
  unshelve refine (@Build_MSetoidAction (grp_mon GalZ2@{wo}) galois_two@{wo}
                     (fun g x => xorb g x)
                     (fun g g' Hg x x' Hx => f_equal2 xorb Hg Hx) _ _).
  - intros [|]; reflexivity.
  - intros [|] [|] [|]; reflexivity.
Defined.

(* 相关说明。 （已译） *)
Example galois_z2_act_moves : act GalZ2Act true true = false := eq_refl.

(* Subsets of the two-point setoid.  [equiv] there is Leibniz equality, so
   respectfulness is a substitution. *)
Definition galois_sub@{wo} (p : bool → Prop) :
  carrier (Powerset_Prop_obj@{wo} galois_two@{wo}).
Proof.
  unshelve refine (@Build_SetoidMorphism@{wo wo wo}
    bool (is_setoid galois_two@{wo})
    Prop (is_setoid Powerset_Prop_truth@{wo}) p _).
  intros x y Hxy; simpl in Hxy; subst; split; exact (fun h => h).
Defined.

Definition galois_true@{wo} : carrier (Powerset_Prop_obj@{wo} galois_two@{wo})
  := galois_sub@{wo} (fun b => b = true).

Definition galois_false@{wo} : carrier (Powerset_Prop_obj@{wo} galois_two@{wo})
  := galois_sub@{wo} (fun b => b = false).

(* 相关说明。 （已译） *)
Lemma galois_z2_stab_forces (s : bool) :
  stab (A := GalZ2Act) galois_true s → s = false.
Proof.
  intro H; refine (H true eq_refl _ _); intro Hfix.
  destruct s; [ discriminate Hfix | reflexivity ].
Qed.

Lemma galois_z2_stab_unit : stab (A := GalZ2Act) galois_true false.
Proof.
  intros x Hx; apply Powerset_squash_intro; reflexivity.
Qed.

Theorem galois_stab_true_trivial :
  stab (A := GalZ2Act) galois_true ≈ galois_false.
Proof.
  apply subset_le_antisym.
  - intros s Hs; exact (galois_z2_stab_forces s Hs).
  - intros s Hs; simpl in Hs; subst s; exact galois_z2_stab_unit.
Qed.

(* 相关说明。 （已译） *)
Theorem galois_fixed_true_empty (x : bool) :
  fixed (A := GalZ2Act) galois_true x → False.
Proof.
  intro H; refine (H true eq_refl _ _); intro Hfix.
  destruct x; discriminate Hfix.
Qed.

(* 相关说明。 （已译） *)
Theorem galois_true_not_ClosedG :
  ClosedG GalZ2Act galois_true → False.
Proof.
  intro H.
  assert (Hfalse : galois_true false).
  { refine (H false _); intros x Hx.
    destruct (galois_fixed_true_empty x Hx). }
  discriminate Hfalse.
Qed.

(* 相关说明。 （已译） *)
Theorem galois_true_not_ClosedU :
  ClosedU (A := GalZ2Act) galois_true → False.
Proof.
  intro H.
  assert (Hfalse : galois_true false).
  { refine (H false _); intros s Hs.
    apply Powerset_squash_intro.
    rewrite (galois_z2_stab_forces s Hs); reflexivity. }
  discriminate Hfalse.
Qed.

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem galois_false_ClosedG : ClosedG GalZ2Act galois_false.
Proof.
  refine (snd (closed_G_iff GalZ2 GalZ2Act galois_false) (galois_true; _)).
  symmetry; exact galois_stab_true_trivial.
Qed.

(* [stab] not 常值: it separates empty subset {true}. （已译） *)
Definition galois_empty@{wo} : carrier (Powerset_Prop_obj@{wo} galois_two@{wo})
  := galois_sub@{wo} (fun _ => False).

Theorem galois_stab_not_constant :
  stab (A := GalZ2Act) galois_empty true
    * (stab (A := GalZ2Act) galois_true true → False).
Proof.
  split.
  - intros x Hx; destruct Hx.
  - intro H; pose proof (galois_z2_stab_forces true H) as Heq.
    discriminate Heq.
Qed.

(* ------------------------------------------------------------------------ *)
(* 相关说明。 （已译） *)

(*
   本节说明 Galois 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition galois_four@{wo} : SetoidObject@{wo wo} :=
  {| carrier := (bool * bool)%type
   ; is_setoid := eq_Setoid@{wo} (bool * bool)%type |}.

Definition galois_v4_mul (g h : bool * bool) : bool * bool :=
  (xorb (fst g) (fst h), xorb (snd g) (snd h)).

Definition GalV4@{wo} : GrpObject@{wo wo wo}.
Proof.
  unshelve refine {| grp_setoid := galois_four@{wo}
                   ; grp_unit := (false, false)
                   ; grp_mul := galois_v4_mul
                   ; grp_inv := fun g : bool * bool => g
                   ; grp_prop := eq_PropEquiv@{wo} (bool * bool)%type |}.
  - exact (fun x y Hxy u v Huv => f_equal2 galois_v4_mul Hxy Huv).
  - intros [[|] [|]] [[|] [|]] [[|] [|]]; reflexivity.
  - intros [[|] [|]]; reflexivity.
  - intros [[|] [|]]; reflexivity.
Defined.

Definition GalV4Act@{wo +} : MSetoidAction (grp_mon GalV4@{wo}).
Proof.
  unshelve refine (@Build_MSetoidAction (grp_mon GalV4@{wo}) galois_two@{wo}
                     (fun g x => xorb (fst g) x)
                     (fun g g' Hg x x' Hx =>
                        f_equal2 xorb (f_equal (@fst bool bool) Hg) Hx) _ _).
  - intros [|]; reflexivity.
  - intros [[|] [|]] [[|] [|]] [|]; reflexivity.
Defined.

(* 相关说明。 （已译） *)
Lemma galois_v4_stab_forces (g : bool * bool) :
  stab (A := GalV4Act) galois_true g → fst g = false.
Proof.
  intro H; refine (H true eq_refl _ _); intro Hfix.
  destruct g as [[|] [|]]; simpl in *; try discriminate Hfix; reflexivity.
Qed.

Lemma galois_v4_stab_holds (g : bool * bool) :
  fst g = false → stab (A := GalV4Act) galois_true g.
Proof.
  intros Hg x Hx; apply Powerset_squash_intro.
  simpl; rewrite Hg; reflexivity.
Qed.

(* 相关说明。 （已译） *)
Theorem galois_v4_stab_nontrivial :
  sub_mem (stab_Subgroup GalV4 GalV4Act galois_true) (false, true)
    * ((false, true) = grp_unit GalV4 → False).
Proof.
  split.
  - exact (galois_v4_stab_holds (false, true) eq_refl).
  - intro Heq; discriminate Heq.
Qed.

(* NOT the whole group: it omits an element. *)
Theorem galois_v4_stab_proper :
  sub_mem (stab_Subgroup GalV4 GalV4Act galois_true) (true, false) → False.
Proof.
  intro H; pose proof (galois_v4_stab_forces (true, false) H) as Heq.
  discriminate Heq.
Qed.
