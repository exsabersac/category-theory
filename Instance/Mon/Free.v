Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Mon.Coproduct.

Generalizable All Variables.

(** * The free monoid on a SETOID, and its adjunction at Mon(Sets) *)

(*
 nLab:      https://ncatlab.org/nlab/show/universal+morphism
 Wikipedia: https://en.wikipedia.org/wiki/Free_monoid
 Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,

   本文件给出自由构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[local] Obligation Tactic := idtac.

Local Notation MonS := (@Mon Sets Sets_Product_Monoidal).
Local Notation UMonS := (@Mon_Forget Sets Sets_Product_Monoidal).

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fixpoint wapp {X : SetoidObject} (u v : list (carrier X))
  : list (carrier X) :=
  match u with
  | Datatypes.nil        => v
  | Datatypes.cons a u'  => Datatypes.cons a (wapp u' v)
  end.

Lemma wapp_assoc {X : SetoidObject} (u v w : list (carrier X)) :
  wapp (wapp u v) w = wapp u (wapp v w).
Proof.
  induction u as [|a u IH]; simpl; [ reflexivity | now rewrite IH ].
Qed.

Lemma wapp_nil_r {X : SetoidObject} (u : list (carrier X)) :
  wapp u Datatypes.nil = u.
Proof.
  induction u as [|a u IH]; simpl; [ reflexivity | now rewrite IH ].
Qed.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive word_eq {X : SetoidObject}
  : list (carrier X) → list (carrier X) → Type :=
  | we_nil : word_eq Datatypes.nil Datatypes.nil
  | we_cons (a b : carrier X) (u v : list (carrier X)) :
      a ≈ b → word_eq u v →
      word_eq (Datatypes.cons a u) (Datatypes.cons b v).

Lemma word_eq_refl {X : SetoidObject} (u : list (carrier X)) :
  word_eq u u.
Proof.
  induction u as [|a u IH].
  - exact we_nil.
  - exact (we_cons a a u u (reflexivity a) IH).
Qed.

Lemma word_eq_sym {X : SetoidObject} (u v : list (carrier X)) :
  word_eq u v → word_eq v u.
Proof.
  intro H; induction H as [|a b u v Hab Huv IH].
  - exact we_nil.
  - exact (we_cons b a v u (symmetry Hab) IH).
Qed.

Lemma word_eq_trans {X : SetoidObject} (u v w : list (carrier X)) :
  word_eq u v → word_eq v w → word_eq u w.
Proof.
  intros H; revert w.
  induction H as [|a b u v Hab Huv IH]; intros w K.
  - exact K.
  - inversion K as [|b' c v' w' Hbc Hvw].
    subst.
    exact (we_cons a c u w' (transitivity Hab Hbc) (IH w' Hvw)).
Qed.

Definition word_eq_Equivalence (X : SetoidObject)
  : Equivalence (@word_eq X) :=
  {| Equivalence_Reflexive  := @word_eq_refl X
   ; Equivalence_Symmetric  := @word_eq_sym X
   ; Equivalence_Transitive := @word_eq_trans X |}.

Definition Word_Setoid (X : SetoidObject) : Setoid (list (carrier X)) :=
  {| equiv := @word_eq X ; setoid_equiv := word_eq_Equivalence X |}.

Definition WordObj (X : SetoidObject) : SetoidObject :=
  {| carrier := list (carrier X) ; is_setoid := Word_Setoid X |}.

Lemma wapp_respects {X : SetoidObject} (u u' v v' : list (carrier X)) :
  word_eq u u' → word_eq v v' → word_eq (wapp u v) (wapp u' v').
Proof.
  intros Hu Hv; induction Hu as [|a b u u' Hab Huu' IH]; simpl.
  - exact Hv.
  - exact (we_cons a b _ _ Hab IH).
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition FreeMonSetsObject (X : SetoidObject) : MonS.
Proof.
  unshelve refine
    (mk_mon_obj (WordObj X) Datatypes.nil (@wapp X) _ _ _ _).
  - intros u u' Hu v v' Hv; exact (wapp_respects u u' v v' Hu Hv).
  - intros u v w; rewrite wapp_assoc; exact (word_eq_refl _).
  - intro u; exact (word_eq_refl u).
  - intro u; rewrite wapp_nil_r; exact (word_eq_refl u).
Defined.

(* The four data readings hold on the nose. *)
Example free_mon_carrier (X : SetoidObject) :
  mon_ob (FreeMonSetsObject X) = WordObj X := eq_refl.

Example free_mon_forget (X : SetoidObject) :
  UMonS (FreeMonSetsObject X) = WordObj X := eq_refl.

Example free_mon_mul_is_wapp (X : SetoidObject)
        (u v : list (carrier X)) :
  mon_mul (FreeMonSetsObject X) u v = wapp u v := eq_refl.

Example free_mon_one_is_nil (X : SetoidObject) :
  mon_one (FreeMonSetsObject X) = @Datatypes.nil (carrier X) := eq_refl.

(*
   本节说明（余）端、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition free_mon_insert (X : SetoidObject)
  : X ~{Sets}~> UMonS (FreeMonSetsObject X) := {|
  morphism := fun a => Datatypes.cons a Datatypes.nil
|}.
Next Obligation.
  intros X a b Hab.
  exact (we_cons a b Datatypes.nil Datatypes.nil Hab we_nil).
Qed.

(** ** The extension of a map into a monoid: the fold

    The extension of h replaces concatenation by the multiplication of L
    and the empty word by its unit, so it is the right fold of h. *)

Fixpoint free_mon_extend {X : SetoidObject} {L : MonS}
         (h : carrier X → carrier (mon_ob L)) (l : list (carrier X))
  : carrier (mon_ob L) :=
  match l with
  | Datatypes.nil       => mon_one L
  | Datatypes.cons a l' => mon_mul L (h a) (free_mon_extend h l')
  end.

(* The fold respects `≈` on words as soon as h respects `≈` on letters —
   which is exactly the hypothesis a Sets-morphism carries. *)
Lemma free_mon_extend_respects {X : SetoidObject} {L : MonS}
      (h : carrier X → carrier (mon_ob L))
      (hp : Proper (equiv ==> equiv) h)
      (u v : list (carrier X)) :
  word_eq u v → free_mon_extend h u ≈ free_mon_extend h v.
Proof.
  intro H; induction H as [|a b u v Hab Huv IH]; simpl.
  - reflexivity.
  - exact (mon_mul_resp L _ _ (hp a b Hab) _ _ IH).
Qed.

(* It carries concatenation to multiplication: induction on the left
   word, using the left unit law at the empty word and associativity at
   a [cons]. *)
Lemma free_mon_extend_wapp {X : SetoidObject} {L : MonS}
      (h : carrier X → carrier (mon_ob L)) (u v : list (carrier X)) :
  free_mon_extend h (wapp u v)
    ≈ mon_mul L (free_mon_extend h u) (free_mon_extend h v).
Proof.
  induction u as [|a u IH]; simpl.
  - symmetry; exact (mon_one_l L (free_mon_extend h v)).
  - transitivity
      (mon_mul L (h a)
         (mon_mul L (free_mon_extend h u) (free_mon_extend h v))).
    + exact (mon_mul_resp L _ _ (reflexivity (h a)) _ _ IH).
    + symmetry; exact (mon_mul_assoc L (h a) _ _).
Qed.

(* ...and it agrees with h on the generators, by the right unit law. *)
Lemma free_mon_extend_generator {X : SetoidObject} {L : MonS}
      (h : carrier X → carrier (mon_ob L)) (a : carrier X) :
  free_mon_extend h (free_mon_insert X a) ≈ h a.
Proof. exact (mon_one_r L (h a)). Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition free_mon_hom {X : SetoidObject} {L : MonS}
      (h : carrier X → carrier (mon_ob L))
      (hp : Proper (equiv ==> equiv) h)
  : FreeMonSetsObject X ~{MonS}~> L :=
  @mk_mon_hom (FreeMonSetsObject X) L (free_mon_extend h)
    (fun u v Huv => free_mon_extend_respects h hp u v Huv)
    (fun u v => free_mon_extend_wapp h u v)
    (reflexivity (mon_one L)).

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma free_mon_extend_unique {X : SetoidObject} {L : MonS}
      (h : carrier X → carrier (mon_ob L))
      (g : FreeMonSetsObject X ~{MonS}~> L)
      (Hg : ∀ a : carrier X, mon_fun g (free_mon_insert X a) ≈ h a)
      (l : list (carrier X)) :
  mon_fun g l ≈ free_mon_extend h l.
Proof.
  induction l as [|a l IH]; simpl.
  - exact (mon_fun_one g).
  - transitivity
      (mon_mul L (mon_fun g (free_mon_insert X a)) (mon_fun g l)).
    + exact (mon_fun_mul g (free_mon_insert X a) l).
    + exact (mon_mul_resp L _ _ (Hg a) _ _ IH).
Qed.

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Theorem free_mon_universal (X : Sets) :
  ∀ (L : MonS) (h : X ~{Sets}~> UMonS L),
    ∃! g : FreeMonSetsObject X ~{MonS}~> L,
      h ≈ fmap[UMonS] g ∘ free_mon_insert X.
Proof.
  intros L h.
  unshelve eexists.
  - exact (free_mon_hom (h : carrier X → carrier (mon_ob L))
             (proper_morphism h)).
  - intro a; simpl.
    symmetry; exact (free_mon_extend_generator _ a).
  - intros g Hg l; simpl.
    symmetry.
    apply (free_mon_extend_unique
             (h : carrier X → carrier (mon_ob L)) g).
    intro b; symmetry; exact (Hg b).
Qed.

(* The free monoid packaged as a universal arrow from X to [Mon_Forget].
   By Theory/Universal/Arrow.v this IS an initial object of the comma
   category =(X) ↓ Mon_Forget. *)
Definition free_mon_universal_arrow (X : Sets) : UniversalArrow X UMonS :=
  universal_arrow_from_UMP X UMonS (FreeMonSetsObject X)
                           (free_mon_insert X) (free_mon_universal X).

(* The same content in the direct encoding, where the universal object is
   named rather than projected. *)
Program Definition free_mon_AUniversalArrow (X : Sets)
  : AUniversalArrow X UMonS (FreeMonSetsObject X) := {|
  universal_arrow := free_mon_insert X
|}.
Next Obligation.
  intros X L h.
  unshelve eexists.
  - exact (free_mon_hom (h : carrier X → carrier (mon_ob L))
             (proper_morphism h)).
  - intro a; simpl; exact (free_mon_extend_generator _ a).
  - intros g Hg l; simpl.
    symmetry.
    apply (free_mon_extend_unique
             (h : carrier X → carrier (mon_ob L)) g).
    intro b; exact (Hg b).
Qed.

(*
   本节说明伴随、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition FreeMonSets : Sets ⟶ MonS :=
  LeftAdjointFunctorFromUniversalArrows UMonS free_mon_universal_arrow.

Definition free_mon_sets_adjunction : FreeMonSets ⊣ UMonS :=
  AdjunctionFromUniversalArrows UMonS free_mon_universal_arrow.

(** * Strengths achieved, and two rejected *)

(* The free functor's object part is the word monoid, definitionally. *)
Example FreeMonSets_obj (X : Sets) :
  FreeMonSets X = FreeMonSetsObject X := eq_refl.

(* The universal arrow is the insertion on the nose:
   [universal_arrow_from_UMP] stores the supplied morphism as the second
   projection of the comma object it builds, so no proof is involved. *)
Example free_mon_arrow_is_insert (X : Sets) :
  @arrow _ _ X UMonS (free_mon_universal_arrow X) = free_mon_insert X
  := eq_refl.

(* Hence so is the unit of the adjunction: the transpose of the identity
   is [fmap[U] id ∘ arrow], and [fmap[U] id] is the identity setoid map,
   whose action is [Datatypes.id]. *)
Example free_mon_unit_is_insert (X : Sets) (a : carrier X) :
  @Category.Theory.Adjunction.unit _ _ _ _ free_mon_sets_adjunction X a
    = free_mon_insert X a := eq_refl.

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example free_mon_counit_is_not_strict
  (L : MonS) (l : list (carrier (mon_ob L))) :
  mon_fun (@counit _ _ _ _ free_mon_sets_adjunction L) l
    = free_mon_extend (fun x => x) l := eq_refl.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma free_mon_counit_evaluates (L : MonS)
      (l : list (carrier (mon_ob L))) :
  mon_fun (@counit _ _ _ _ free_mon_sets_adjunction L) l
    ≈ free_mon_extend (fun x => x) l.
Proof.
  apply (free_mon_extend_unique (fun x : carrier (mon_ob L) => x)).
  intro a.
  exact (@fmap_counit_unit _ _ _ _ free_mon_sets_adjunction L a).
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Fixpoint wmap {X Y : SetoidObject} (f : carrier X → carrier Y)
         (l : list (carrier X)) : list (carrier Y) :=
  match l with
  | Datatypes.nil       => Datatypes.nil
  | Datatypes.cons a l' => Datatypes.cons (f a) (wmap f l')
  end.

Lemma free_mon_fmap_generators {X Y : Sets} (f : X ~{Sets}~> Y)
      (a : carrier X) :
  mon_fun (fmap[FreeMonSets] f) (free_mon_insert X a)
    ≈ free_mon_insert Y (f a).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_mon_universal_arrow X)
              (@arrow _ _ Y UMonS (free_mon_universal_arrow Y) ∘ f)) a).
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example free_mon_extend_insert_is_not_strict
  {X Y : Sets} (f : X ~{Sets}~> Y) (l : list (carrier X)) :
  free_mon_extend (L:=FreeMonSetsObject Y)
    (fun a => free_mon_insert Y (f a)) l = wmap f l := eq_refl.

Example free_mon_extend_insert_at_letter
  {X Y : Sets} (f : X ~{Sets}~> Y) (a : carrier X) :
  free_mon_extend (L:=FreeMonSetsObject Y)
    (fun b => free_mon_insert Y (f b))
    (Datatypes.cons a Datatypes.nil)
    = wmap f (Datatypes.cons a Datatypes.nil) := eq_refl.

(* Each step of the induction closes by [reflexivity] with no monoid law
   spent, which is why this is stated at Leibniz `=`. *)
Lemma free_mon_extend_insert {X Y : Sets} (f : X ~{Sets}~> Y)
      (l : list (carrier X)) :
  free_mon_extend (L:=FreeMonSetsObject Y)
    (fun a => free_mon_insert Y (f a)) l = wmap f l.
Proof.
  induction l as [|a l IH]; simpl in *;
    [ reflexivity | rewrite IH; reflexivity ].
Qed.

Theorem free_mon_fmap_is_wmap {X Y : Sets} (f : X ~{Sets}~> Y)
        (l : list (carrier X)) :
  mon_fun (fmap[FreeMonSets] f) l ≈ wmap f l.
Proof.
  transitivity (free_mon_extend (L:=FreeMonSetsObject Y)
                  (fun a => free_mon_insert Y (f a)) l).
  - apply (free_mon_extend_unique
             (fun a => free_mon_insert Y (f a)) (fmap[FreeMonSets] f)).
    intro a; exact (free_mon_fmap_generators f a).
  - rewrite free_mon_extend_insert; reflexivity.
Qed.

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The fold respects pointwise-`≈` letter maps. *)
Lemma free_mon_extend_pointwise {X : SetoidObject} {L : MonS}
      (h h' : carrier X → carrier (mon_ob L))
      (H : ∀ a, h a ≈ h' a) (l : list (carrier X)) :
  free_mon_extend h l ≈ free_mon_extend h' l.
Proof.
  induction l as [|a l IH]; simpl; [ reflexivity | ].
  exact (mon_mul_resp L _ _ (H a) _ _ IH).
Qed.

(* The natural bijection Mon(F X, L) ≅ Sets(X, U L): forward g ↦ U g ∘
   insert, backward the fold. *)
Definition free_mon_hom_iso@{o so +} (X : Sets@{o so}) (L : MonS) :
  @Isomorphism Sets@{o so}
    {| carrier := @hom MonS (FreeMonSets X) L
     ; is_setoid := @homset MonS (FreeMonSets X) L |}
    {| carrier := @hom Sets@{o so} X (UMonS L)
     ; is_setoid := @homset Sets@{o so} X (UMonS L) |}.
Proof.
  unshelve refine
    (@Build_Isomorphism Sets
       {| carrier := @hom MonS (FreeMonSets X) L
        ; is_setoid := @homset MonS (FreeMonSets X) L |}
       {| carrier := @hom Sets X (UMonS L)
        ; is_setoid := @homset Sets X (UMonS L) |}
       (@Build_SetoidMorphism
          (@hom MonS (FreeMonSets X) L) (@homset MonS (FreeMonSets X) L)
          (@hom Sets X (UMonS L)) (@homset Sets X (UMonS L))
          (fun g => fmap[UMonS] g ∘ free_mon_insert X) _)
       (@Build_SetoidMorphism
          (@hom Sets X (UMonS L)) (@homset Sets X (UMonS L))
          (@hom MonS (FreeMonSets X) L) (@homset MonS (FreeMonSets X) L)
          (fun h => free_mon_hom (h : carrier X → carrier (mon_ob L))
                      (proper_morphism h)) _) _ _).
  - intros g g' H a. exact (H (Datatypes.cons a Datatypes.nil)).
  - intros h h' H l. exact (free_mon_extend_pointwise h h' H l).
  - intros h a. exact (free_mon_extend_generator (L := L) h a).
  - intros g l. simpl. symmetry.
    apply (free_mon_extend_unique _ g). intro a. reflexivity.
Defined.

Definition free_mon_sets_adjunction_hom@{o so +} :
  @Adjunction@{so o o so o o o o so o so} MonS Sets@{o so}
    FreeMonSets UMonS.
Proof.
  unshelve refine
    (@Build_Adjunction' MonS Sets FreeMonSets UMonS free_mon_hom_iso _ _).
  - intros X Y L f g a. simpl.
    apply (proper_morphism (`1 f)).
    exact (free_mon_fmap_generators g a).
  - intros X L L' f g a. reflexivity.
Defined.

(* Its counit is the fold of the identity, by conversion. *)
Example free_mon_hom_counit (L : MonS) (l : list (carrier (mon_ob L))) :
  mon_fun (@counit _ _ _ _ free_mon_sets_adjunction_hom L) l
    = free_mon_extend (fun x => x) l := eq_refl.

(* Its unit and its forward transpose ARE those of
   [free_mon_sets_adjunction]. *)
Example free_mon_hom_unit (X : Sets) :
  @Category.Theory.Adjunction.unit _ _ _ _ free_mon_sets_adjunction_hom X
    = @Category.Theory.Adjunction.unit _ _ _ _ free_mon_sets_adjunction X
  := eq_refl.

Example free_mon_hom_to (X : Sets) (L : MonS)
        (g : FreeMonSets X ~{MonS}~> L) :
  to (@adj _ _ _ _ free_mon_sets_adjunction_hom X L) g
    = to (@adj _ _ _ _ free_mon_sets_adjunction X L) g := eq_refl.

(** * Non-vacuity

    [word_eq] is a STRUCTURAL congruence, not a generated one, so unlike
    Instance/Mon/Coproduct.v's [fp_eq] it is open to inversion and
    negatives are reachable directly.  Both routes are given below;
    they share no proof text. *)

(* The insertion reflects `≈`: it is injective on generators up to the
   source setoid, for EVERY X, with no hypothesis. *)
Lemma free_mon_insert_reflects {X : SetoidObject} (a b : carrier X) :
  word_eq (Datatypes.cons a Datatypes.nil)
          (Datatypes.cons b Datatypes.nil) → a ≈ b.
Proof. intro H; inversion H; assumption. Qed.

(* Two setoids on ONE carrier, [bool]: the discrete one, and the
   coarsest one, which identifies everything. *)
Definition MonTwoObj : SetoidObject :=
  {| carrier := bool ; is_setoid := eq_Setoid bool |}.

Program Definition Blur_Setoid : Setoid bool :=
  {| equiv := fun _ _ => True |}.
Next Obligation. constructor; repeat intro; exact Logic.I. Qed.

Definition BlurObj : SetoidObject :=
  {| carrier := bool ; is_setoid := Blur_Setoid |}.

(* Over the discrete setoid the two generators stay apart... *)
Theorem free_mon_two_generators_distinct : @word_eq MonTwoObj
  (Datatypes.cons true Datatypes.nil)
  (Datatypes.cons false Datatypes.nil) → False.
Proof.
  intro H.
  assert (K : true = false)
    by exact (free_mon_insert_reflects (X:=MonTwoObj) true false H).
  discriminate K.
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition free_mon_blur_identifies : @word_eq BlurObj
  (Datatypes.cons true Datatypes.nil)
  (Datatypes.cons false Datatypes.nil) :=
  @we_cons BlurObj true false Datatypes.nil Datatypes.nil Logic.I
    (@we_nil BlurObj).

(*
   本节说明幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition two_letter : carrier MonTwoObj → carrier (mon_ob ListBoolMon) :=
  fun x => Datatypes.cons x Datatypes.nil.

Definition two_probe : FreeMonSetsObject MonTwoObj ~{MonS}~> ListBoolMon :=
  free_mon_hom two_letter (fun a b H => f_equal two_letter H).

(* The probe's value at a two-letter word COMPUTES. *)
Example two_probe_word2 :
  mon_fun two_probe
    (Datatypes.cons true (Datatypes.cons false Datatypes.nil))
    = bword2 true false := eq_refl.

Theorem free_mon_two_generators_distinct_via_probe : @word_eq MonTwoObj
  (Datatypes.cons true Datatypes.nil)
  (Datatypes.cons false Datatypes.nil) → False.
Proof.
  intro H.
  assert (K : mon_fun two_probe (Datatypes.cons true Datatypes.nil)
                = mon_fun two_probe (Datatypes.cons false Datatypes.nil)).
  { exact (free_mon_extend_respects two_letter
             (fun a b E => f_equal two_letter E) _ _ H). }
  cbn in K; discriminate K.
Qed.

(* A two-letter word is not equivalent to any one-letter word, so the
   free monoid is not collapsed by length either. *)
Theorem free_mon_word2_not_letter (c : bool) : @word_eq MonTwoObj
  (Datatypes.cons true (Datatypes.cons false Datatypes.nil))
  (Datatypes.cons c Datatypes.nil) → False.
Proof.
  intro H.
  assert (K : mon_fun two_probe
                (Datatypes.cons true (Datatypes.cons false Datatypes.nil))
                = mon_fun two_probe (Datatypes.cons c Datatypes.nil)).
  { exact (free_mon_extend_respects two_letter
             (fun a b E => f_equal two_letter E) _ _ H). }
  cbn in K; discriminate K.
Qed.

(*
   本节说明 Free 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section FreeAboveSet.

  Universe uo uso.
  Constraint Set < uo.
  Constraint uo < uso.

  Check FreeMonSetsObject@{uso uo}.
  (*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  Check (FreeMonSets : Sets@{uo uso} ⟶ _).
  Check (free_mon_sets_adjunction : @Adjunction _ Sets@{uo uso} _ _).
  Check (free_mon_sets_adjunction_hom : @Adjunction _ Sets@{uo uso} _ _).

End FreeAboveSet.

(* Instrument check: [Fail] does report failures in this file. *)
Fail Definition free_mon_instrument_check : False := Logic.I.
