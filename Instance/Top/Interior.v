Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Algebra.
Require Import Category.Comonad.Core.
Require Import Category.Comonad.Coalgebra.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Monad.
Require Import Category.Instance.Proset.Monad.Interior.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Cocomplete.

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * Interior and closure on the subsets of a space *)

(*
 nLab: https://ncatlab.org/nlab/show/closure
 Book: Riehl, "Category Theory in Context", 2nd ed., SS 5.1,

   本文件给出具体实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The subsets of the points of X: Prop-valued predicates respecting the
   points' ≈ (Instance/Sets/Powerset.v's [Powerset_Prop_obj]). *)
Local Notation PSub X := (carrier (Powerset_Prop_obj (pt_carrier X))).

(** ** The interior: the union of the opens inside S *)

Definition pint_fun@{o} (X : PTop@{o}) (S : PSub X) (x : pt_carrier X) :
  Prop :=
  ex (fun U : pt_carrier X → Prop => (POpen X U /\ ∀ y, U y → S y) /\ U x).

Lemma pint_proper@{o} (X : PTop@{o}) (S : PSub X) (x y : pt_carrier X) :
  x ≈ y → Powerset_Prop_truth_equiv@{o} (pint_fun X S x) (pint_fun X S y).
Proof.
  intros Hxy; split; intros [U [[HU HS] Ux]]; exists U;
    (split; [split; assumption|]).
  - exact (popen_proper X U HU x y Hxy Ux).
  - apply (popen_proper X U HU y x); [|exact Ux]. symmetry; exact Hxy.
Qed.

Definition pinterior@{o} (X : PTop@{o}) (S : PSub X) : PSub X :=
  @Build_SetoidMorphism@{o o o}
    (carrier (pt_carrier X)) (is_setoid (pt_carrier X))
    Prop (is_setoid Powerset_Prop_truth@{o}) (pint_fun X S)
    (pint_proper X S).

(* The interior is open: it is written in exactly the shape that
   Instance/Top/Prop.v's [popen_union] closes. *)
Lemma pint_open@{o} (X : PTop@{o}) (S : PSub X) : POpen X (pinterior X S).
Proof.
  apply (popen_union X (fun U => POpen X U /\ ∀ y, U y → S y)).
  intros U [HU _]; exact HU.
Qed.

Definition pint_mono@{o} (X : PTop@{o}) (S T : PSub X)
  (h : subset_le S T) : subset_le (pinterior X S) (pinterior X T) :=
  fun x '(ex_intro _ U (conj (conj HU HS) Ux)) =>
    ex_intro _ U (conj (conj HU (fun y Uy => h y (HS y Uy))) Ux).

Definition pint_defl@{o} (X : PTop@{o}) (S : PSub X) :
  subset_le (pinterior X S) S :=
  fun x '(ex_intro _ U (conj (conj _ HS) Ux)) => HS x Ux.

Definition pint_comult@{o} (X : PTop@{o}) (S : PSub X) :
  subset_le (pinterior X S) (pinterior X (pinterior X S)) :=
  fun x '(ex_intro _ U (conj (conj HU HS) Ux)) =>
    ex_intro _ U (conj (conj HU (fun y Uy =>
      ex_intro _ U (conj (conj HU HS) Uy))) Ux).

(* The interior operator: a closure operator on the reversed inclusion
   order (Instance/Proset/Monad/Interior.v). *)
Definition pinterior_op@{o} (X : PTop@{o}) :
  InteriorOperator@{o} (subset_le_preorder@{o} (pt_carrier X)) :=
  {| cl_fun  := flip_mono {| mono_map := pinterior X
                           ; mono_pres := pint_mono X |}
   ; cl_ext  := pint_defl X
   ; cl_mult := pint_comult X |}.

Definition pinterior_comonad@{o h} (X : PTop@{o}) :
  @Comonad (Subsets@{o h} (pt_carrier X))
    (interior_functor@{o h} (pinterior_op X)) :=
  interior_comonad@{o h} (pinterior_op X).

(* A subset contained in its interior is open, and an open subset is
   contained in its interior. *)
Lemma open_of_sub_pint@{o} (X : PTop@{o}) (S : PSub X)
  (h : subset_le S (pinterior X S)) : POpen X S.
Proof.
  apply (popen_respects X (pinterior X S)); [|exact (pint_open X S)].
  intro x; split; [exact (pint_defl X S x)|exact (h x)].
Qed.

Definition sub_pint_of_open@{o} (X : PTop@{o}) (S : PSub X)
  (HS : POpen X S) : subset_le S (pinterior X S) :=
  fun x Sx => ex_intro _ (fun y => S y) (conj (conj HS (fun y Sy => Sy)) Sx).

(* Riehl 5.2.6 (iv), coalgebra half: the coalgebras of the interior
   comonad are exactly the open subsets.  Constructive. *)
Definition pint_coalgebra_iff_open@{o h p} (X : PTop@{o}) (S : PSub X) :
  iffT@{h p}
    (@WCoalgebra (Subsets@{o h} (pt_carrier X))
       (interior_functor (pinterior_op X)) (pinterior_comonad X) S)
    (POpen X S) :=
  let (to_sub, of_sub) :=
    wcoalgebra_iff_open@{o h p} (interior_functor (pinterior_op X))
      (H := pinterior_comonad X) S in
  (fun c => open_of_sub_pint X S (to_sub c),
   fun HS => of_sub (sub_pint_of_open X S HS)).

(* Non-vacuity: {true} in the indiscrete two-point space is not open, so
   not a coalgebra. *)
Definition true_sub@{o} : PSub PTwoIndisc@{o} :=
  @Build_SetoidMorphism@{o o o}
    (carrier (pt_carrier PTwoIndisc@{o})) (is_setoid (pt_carrier PTwoIndisc))
    Prop (is_setoid Powerset_Prop_truth@{o}) (fun b => b = true)
    (fun x y (Hxy : x = y) =>
       match Hxy in _ = z return Powerset_Prop_truth_equiv (x = true)
                                   (z = true) with
       | eq_refl => conj (fun H => H) (fun H => H)
       end).

Lemma true_sub_not_coalgebra@{o h} :
  @WCoalgebra (Subsets@{o h} (pt_carrier PTwoIndisc@{o}))
    (interior_functor (pinterior_op PTwoIndisc))
    (pinterior_comonad PTwoIndisc) true_sub → False.
Proof.
  intro c. destruct (pint_coalgebra_iff_open PTwoIndisc true_sub)
    as [to_open _].
  pose proof (to_open c true false eq_refl) as H.
  change (false = true :> bool) in H. discriminate H.
Qed.

(** ** The closure: Riehl's footnote 5 *)

(* A closed subset is one whose complement is open. *)
Definition PClosedSub@{o} (X : PTop@{o}) (C : PSub X) : Prop :=
  POpen X (fun z => ~ C z).

(* "the intersection of all closed sets containing A" *)
Definition pcl_fun@{o} (X : PTop@{o}) (S : PSub X) (x : pt_carrier X) :
  Prop :=
  ∀ C : PSub X, PClosedSub X C → subset_le S C → C x.

Lemma pcl_proper@{o} (X : PTop@{o}) (S : PSub X) (x y : pt_carrier X) :
  x ≈ y → Powerset_Prop_truth_equiv@{o} (pcl_fun X S x) (pcl_fun X S y).
Proof.
  intros Hxy; split; intros H C HC HSC.
  - exact (proj1 (proper_morphism C x y Hxy) (H C HC HSC)).
  - exact (proj2 (proper_morphism C x y Hxy) (H C HC HSC)).
Qed.

Definition pclosure@{o} (X : PTop@{o}) (S : PSub X) : PSub X :=
  @Build_SetoidMorphism@{o o o}
    (carrier (pt_carrier X)) (is_setoid (pt_carrier X))
    Prop (is_setoid Powerset_Prop_truth@{o}) (pcl_fun X S)
    (pcl_proper X S).

Definition pcl_mono@{o} (X : PTop@{o}) (S T : PSub X)
  (h : subset_le S T) : subset_le (pclosure X S) (pclosure X T) :=
  fun x H C HC HTC => H C HC (fun y Sy => HTC y (h y Sy)).

Definition pcl_ext@{o} (X : PTop@{o}) (S : PSub X) :
  subset_le S (pclosure X S) :=
  fun x Sx C _ HSC => HSC x Sx.

Definition pcl_mult@{o} (X : PTop@{o}) (S : PSub X) :
  subset_le (pclosure X (pclosure X S)) (pclosure X S) :=
  fun x H C HC HSC => H C HC (fun y Hy => Hy C HC HSC).

Definition pclosure_op@{o} (X : PTop@{o}) :
  ClosureOperator@{o} (subset_le_preorder@{o} (pt_carrier X)) :=
  {| cl_fun  := {| mono_map := pclosure X; mono_pres := pcl_mono X |}
   ; cl_ext  := pcl_ext X
   ; cl_mult := pcl_mult X |}.

Definition pclosure_monad@{o h} (X : PTop@{o}) :
  @Monad (Subsets@{o h} (pt_carrier X))
    (closure_functor@{o h} (pclosure_op X)) :=
  closure_monad@{o h} (pclosure_op X).

(* A closed subset contains its closure.  Constructive. *)
Definition pcl_sub_of_closed@{o} (X : PTop@{o}) (S : PSub X)
  (HS : PClosedSub X S) : subset_le (pclosure X S) S :=
  fun x H => H S HS (fun y Sy => Sy).

(*
   本节说明 Interior 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma pcl_closed_of_sub@{o} (lem : ∀ P : Prop, P \/ ~ P) (X : PTop@{o})
  (S : PSub X) (h : subset_le (pclosure X S) S) : PClosedSub X S.
Proof.
  unfold PClosedSub.
  apply (popen_respects X (fun z => ex (fun U : pt_carrier X → Prop =>
     ex (fun C : PSub X =>
       (PClosedSub X C /\ subset_le S C) /\ ∀ w, U w <-> ~ C w) /\ U z))).
  - intro z; split.
    + intros [U [[C [[_ HSC] HU]] Uz]] Sz.
      exact (proj1 (HU z) Uz (HSC z Sz)).
    + intro nSz.
      destruct (lem (ex (fun C : PSub X =>
                        (PClosedSub X C /\ subset_le S C) /\ ~ C z)))
        as [[C [[HC HSC] nCz]]|none].
      * exists (fun w => ~ C w). split; [|exact nCz].
        exists C. split; [split; assumption|]. intro w; split; intro H; exact H.
      * exfalso. apply nSz, h. intros C HC HSC.
        destruct (lem (C z)) as [Cz|nCz]; [exact Cz|].
        exfalso; apply none; exists C; split; [split; assumption|exact nCz].
  - apply popen_union. intros U [C [[HC _] HU]].
    apply (popen_respects X (fun w => ~ C w)); [|exact HC].
    intro w; split; intro H; [exact (proj2 (HU w) H)|exact (proj1 (HU w) H)].
Qed.

(* Riehl 5.2.6 (iv), algebra half, through Instance/Proset/Monad.v's
   [talgebra_iff_closed]: a closed subset is an algebra (constructive),
   and an algebra is closed under the hypothesis [lem]. *)
Definition pcl_talgebra_of_closed@{o h} (X : PTop@{o}) (S : PSub X)
  (HS : PClosedSub X S) :
  @TAlgebra (Subsets@{o h} (pt_carrier X))
    (closure_functor (pclosure_op X)) (pclosure_monad X) S :=
  let (_, of_closed) :=
    talgebra_iff_closed@{o h h} (closure_functor (pclosure_op X))
      (MM := pclosure_monad X) S in
  of_closed (pcl_sub_of_closed X S HS).

Definition pcl_closed_of_talgebra@{o h} (lem : ∀ P : Prop, P \/ ~ P)
  (X : PTop@{o}) (S : PSub X)
  (a : @TAlgebra (Subsets@{o h} (pt_carrier X))
         (closure_functor (pclosure_op X)) (pclosure_monad X) S) :
  PClosedSub X S :=
  let (to_closed, _) :=
    talgebra_iff_closed@{o h h} (closure_functor (pclosure_op X))
      (MM := pclosure_monad X) S in
  pcl_closed_of_sub lem X S (to_closed a).

(* Without [lem] the converse costs ¬¬(∀ q, ¬¬q → q).  The subset
   {true} ∪ q of the indiscrete two-point space, closed exactly when
   ¬¬q. *)
Definition true_or_sub@{o} (q : Prop) : PSub PTwoIndisc@{o} :=
  @Build_SetoidMorphism@{o o o}
    (carrier (pt_carrier PTwoIndisc@{o})) (is_setoid (pt_carrier PTwoIndisc))
    Prop (is_setoid Powerset_Prop_truth@{o}) (fun b => b = true \/ q)
    (fun x y (Hxy : x = y) =>
       match Hxy in _ = z return Powerset_Prop_truth_equiv (x = true \/ q)
                                   (z = true \/ q) with
       | eq_refl => conj (fun H => H) (fun H => H)
       end).

(* The point false in the closure of {true} is double-negation
   elimination. *)
Lemma pcl_true_false_dne@{o} :
  pclosure@{o} PTwoIndisc true_sub false → ∀ q : Prop, ~ ~ q → q.
Proof.
  intros H q nnq.
  assert (HC : PClosedSub PTwoIndisc (true_or_sub q)).
  { intros x y nx ny. apply nnq. intro Hq. exact (nx (or_intror Hq)). }
  destruct (H (true_or_sub q) HC (fun y Hy => or_introl Hy)) as [Hf|Hq].
  - change (false = true :> bool) in Hf. discriminate Hf.
  - exact Hq.
Qed.

(* So the converse of [pcl_talgebra_of_closed], with no hypothesis, gives
   ¬¬(∀ q, ¬¬q → q): were that refuted, {true} would be an algebra, and
   {true} is not closed. *)
Lemma pcl_converse_nndne@{o h} :
  (∀ (X : PTop@{o}) (S : PSub X),
     @TAlgebra (Subsets@{o h} (pt_carrier X))
       (closure_functor (pclosure_op X)) (pclosure_monad X) S →
     PClosedSub X S) →
  ~ ~ (∀ q : Prop, ~ ~ q → q).
Proof.
  intros conv ndne.
  assert (alg : subset_le (pclosure PTwoIndisc true_sub) true_sub).
  { intros [|] H.
    - reflexivity.
    - exfalso. exact (ndne (pcl_true_false_dne H)). }
  destruct (talgebra_iff_closed@{o h h}
              (closure_functor (pclosure_op PTwoIndisc))
              (MM := pclosure_monad PTwoIndisc) true_sub) as [_ of_closed].
  pose proof (conv PTwoIndisc true_sub (of_closed alg)) as HC.
  exact (HC false true (fun Hf => ltac:(change (false = true :> bool) in Hf;
                                         discriminate Hf)) eq_refl).
Qed.

(** ** A constructive alternative: the closure as ¬ int (¬ S) *)

(* The pointwise complement of a subset. *)
Lemma pcomp_proper@{o} (X : PTop@{o}) (S : PSub X) (x y : pt_carrier X) :
  x ≈ y → Powerset_Prop_truth_equiv@{o} (~ S x) (~ S y).
Proof.
  intros Hxy; split; intros nS Sy; apply nS.
  - exact (proj2 (proper_morphism S x y Hxy) Sy).
  - exact (proj1 (proper_morphism S x y Hxy) Sy).
Qed.

Definition pcomp@{o} (X : PTop@{o}) (S : PSub X) : PSub X :=
  @Build_SetoidMorphism@{o o o}
    (carrier (pt_carrier X)) (is_setoid (pt_carrier X))
    Prop (is_setoid Powerset_Prop_truth@{o}) (fun x => ~ S x)
    (pcomp_proper X S).

(* The complement of the interior of the complement. *)
Definition ncl@{o} (X : PTop@{o}) (S : PSub X) : PSub X :=
  pcomp X (pinterior X (pcomp X S)).

Definition ncl_mono@{o} (X : PTop@{o}) (S T : PSub X)
  (h : subset_le S T) : subset_le (ncl X S) (ncl X T) :=
  fun x nS '(ex_intro _ U (conj (conj HU HUT) Ux)) =>
    nS (ex_intro _ U (conj (conj HU (fun y Uy Sy => HUT y Uy (h y Sy))) Ux)).

Definition ncl_ext@{o} (X : PTop@{o}) (S : PSub X) :
  subset_le S (ncl X S) :=
  fun x Sx '(ex_intro _ U (conj (conj _ HUS) Ux)) => HUS x Ux Sx.

Definition ncl_mult@{o} (X : PTop@{o}) (S : PSub X) :
  subset_le (ncl X (ncl X S)) (ncl X S) :=
  fun x H Hi =>
    H (pint_mono X (pinterior X (pcomp X S)) (pcomp X (ncl X S))
         (fun y Iy nIy => nIy Iy) x (pint_comult X (pcomp X S) x Hi)).

Definition nclosure_op@{o} (X : PTop@{o}) :
  ClosureOperator@{o} (subset_le_preorder@{o} (pt_carrier X)) :=
  {| cl_fun  := {| mono_map := ncl X; mono_pres := ncl_mono X |}
   ; cl_ext  := ncl_ext X
   ; cl_mult := ncl_mult X |}.

Definition nclosure_monad@{o h} (X : PTop@{o}) :
  @Monad (Subsets@{o h} (pt_carrier X))
    (closure_functor@{o h} (nclosure_op X)) :=
  closure_monad@{o h} (nclosure_op X).

(* Closed in the second sense: the complement of an open subset. *)
Definition PCoOpen@{o} (X : PTop@{o}) (S : PSub X) : Prop :=
  ex (fun U : pt_carrier X → Prop => POpen X U /\ ∀ x, S x <-> ~ U x).

Lemma ncl_sub_iff_coopen@{o} (X : PTop@{o}) (S : PSub X) :
  subset_le (ncl X S) S <-> PCoOpen X S.
Proof.
  split.
  - intro h. exists (pinterior X (pcomp X S)).
    split; [exact (pint_open X (pcomp X S))|].
    intro x; split.
    + intros Sx Hi. exact (pint_defl X (pcomp X S) x Hi Sx).
    + exact (h x).
  - intros [U [HU HS]] x nI. apply (proj2 (HS x)). intro Ux.
    apply (nI : ~ pinterior X (pcomp X S) x).
    exists U. split; [|exact Ux]. split; [exact HU|].
    intros y Uy Sy. exact (proj1 (HS y) Sy Uy).
Qed.

(* The algebras of the ¬ int ¬ closure are exactly the complements of
   opens, in both directions with no hypothesis. *)
Definition ncl_talgebra_iff_coopen@{o h p} (X : PTop@{o}) (S : PSub X) :
  iffT@{h p}
    (@TAlgebra (Subsets@{o h} (pt_carrier X))
       (closure_functor (nclosure_op X)) (nclosure_monad X) S)
    (PCoOpen X S) :=
  let (to_closed, of_closed) :=
    talgebra_iff_closed@{o h p} (closure_functor (nclosure_op X))
      (MM := nclosure_monad X) S in
  (fun a => proj1 (ncl_sub_iff_coopen X S) (to_closed a),
   fun H => of_closed (proj2 (ncl_sub_iff_coopen X S) H)).

(* Non-vacuity, constructively: {true} in the indiscrete two-point space
   is not the complement of an open. *)
Lemma true_sub_not_nclosed@{o h} :
  @TAlgebra (Subsets@{o h} (pt_carrier PTwoIndisc@{o}))
    (closure_functor (nclosure_op PTwoIndisc))
    (nclosure_monad PTwoIndisc) true_sub → False.
Proof.
  intro a. destruct (ncl_talgebra_iff_coopen PTwoIndisc true_sub)
    as [to_coopen _].
  destruct (to_coopen a) as [U [HU HS]].
  pose proof (proj1 (HS true) eq_refl) as nUt.
  assert (nUf : ~ U false) by (intro Uf; exact (nUt (HU false true Uf))).
  pose proof (proj2 (HS false) nUf) as H.
  change (false = true :> bool) in H. discriminate H.
Qed.

(** ** The two routes agree under excluded middle *)

(* A complement of an open is ¬¬-stable. *)
Lemma coopen_stable@{o} (X : PTop@{o}) (S : PSub X) (H : PCoOpen X S)
  (x : pt_carrier X) : ~ ~ S x → S x.
Proof.
  destruct H as [U [_ HS]]. intro nnS. apply (proj2 (HS x)). intro Ux.
  apply nnS. intro Sx. exact (proj1 (HS x) Sx Ux).
Qed.

Lemma coopen_of_closed_stable@{o} (X : PTop@{o}) (S : PSub X)
  (HS : PClosedSub X S) (stable : ∀ x, ~ ~ S x → S x) : PCoOpen X S.
Proof.
  exists (fun z => ~ S z). split; [exact HS|].
  intro x; split; [intros Sx nSx; exact (nSx Sx)|exact (stable x)].
Qed.

Lemma closed_of_coopen_lem@{o} (lem : ∀ P : Prop, P \/ ~ P)
  (X : PTop@{o}) (S : PSub X) (H : PCoOpen X S) : PClosedSub X S.
Proof.
  destruct H as [U [HU HS]]. unfold PClosedSub.
  apply (popen_respects X U); [|exact HU].
  intro x; split.
  - intros Ux Sx. exact (proj1 (HS x) Sx Ux).
  - intro nSx. destruct (lem (U x)) as [Ux|nUx]; [exact Ux|].
    exfalso. exact (nSx (proj2 (HS x) nUx)).
Qed.

Lemma pclosure_ncl_lem@{o} (lem : ∀ P : Prop, P \/ ~ P) (X : PTop@{o})
  (S : PSub X) (x : pt_carrier X) : pclosure X S x <-> ncl X S x.
Proof.
  split.
  - intro H.
    assert (HC : PClosedSub X (ncl X S)).
    { unfold PClosedSub.
      apply (popen_respects X (pinterior X (pcomp X S)));
        [|exact (pint_open X (pcomp X S))].
      intro z; split.
      - intros Hi nI. exact (nI Hi).
      - intro nnI.
        destruct (lem (pinterior X (pcomp X S) z)) as [Hi|nI]; [exact Hi|].
        exfalso; exact (nnI nI). }
    exact (H (ncl X S) HC (ncl_ext X S)).
  - intros N C HC HSC. destruct (lem (C x)) as [Cx|nCx]; [exact Cx|].
    exfalso. apply (N : ~ pinterior X (pcomp X S) x).
    exists (fun z => ~ C z). split; [|exact nCx].
    split; [exact HC|]. intros y nCy Sy. exact (nCy (HSC y Sy)).
Qed.
