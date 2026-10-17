Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pushout.Split.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Coproduct.

Generalizable All Variables.

(* * * Pushouts Top: quotient topology, 伴随 spaces （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/pushout
 Wikipedia: https://en.wikipedia.org/wiki/Adjunction_space

   本文件给出推出实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** The glued point set *)

Section TopPushout.

Context {A B C : TopSpace}.
Context (f : A ~{Top}~> B) (g : A ~{Top}~> C).

Definition tp_point : Type :=
  (carrier (top_carrier B) + carrier (top_carrier C))%type.

(*
   本节说明拉回/推出、等价、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Inductive tp_rel : tp_point → tp_point → Type :=
  | tpr_inl : ∀ b b' : carrier (top_carrier B),
      b ≈ b' → tp_rel (Datatypes.inl b) (Datatypes.inl b')
  | tpr_inr : ∀ c c' : carrier (top_carrier C),
      c ≈ c' → tp_rel (Datatypes.inr c) (Datatypes.inr c')
  | tpr_glue : ∀ a : carrier (top_carrier A),
      tp_rel (Datatypes.inl (f a)) (Datatypes.inr (g a))
  | tpr_sym : ∀ u v, tp_rel u v → tp_rel v u
  | tpr_trans : ∀ u v w, tp_rel u v → tp_rel v w → tp_rel u w.

Lemma tp_rel_refl : Reflexive tp_rel.
Proof using All.
  intros [b | c].
  - apply tpr_inl; reflexivity.
  - apply tpr_inr; reflexivity.
Qed.

Definition tp_setoid : Setoid tp_point := {|
  equiv := tp_rel;
  setoid_equiv :=
    Build_Equivalence tp_rel tp_rel_refl tpr_sym tpr_trans
|}.

Definition tp_carrier : SetoidObject := {|
  carrier := tp_point;
  is_setoid := tp_setoid
|}.

(** ** The quotient topology *)

(*
   本节说明 Pushout 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition tp_open (W : tp_carrier → Type) : Type :=
  ((∀ u v : tp_carrier, tp_rel u v → W u → W v)
     ∧ IsOpen B (fun b => W (Datatypes.inl b))
     ∧ IsOpen C (fun c => W (Datatypes.inr c)))%type.

Lemma tp_respects (U V : tp_carrier → Type) :
  (∀ u, U u ↔ V u) → tp_open U → tp_open V.
Proof using All.
  intros H [HR [HB HC]].
  split; [| split ].
  - intros u v Huv Vu.
    exact (fst (H v) (HR u v Huv (snd (H u) Vu))).
  - exact (open_respects B _ _ (fun b => H (Datatypes.inl b)) HB).
  - exact (open_respects C _ _ (fun c => H (Datatypes.inr c)) HC).
Qed.

Lemma tp_proper (W : tp_carrier → Type) :
  tp_open W → ∀ u v : tp_carrier, u ≈ v → W u → W v.
Proof using All. intros [HR _] u v Huv Wu; exact (HR u v Huv Wu). Qed.

Lemma tp_union (I : Type) (U : I → (tp_carrier → Type)) :
  (∀ i, tp_open (U i)) → tp_open (fun u => { i : I & U i u }).
Proof using All.
  intro H.
  split; [| split ].
  - intros u v Huv [i Hi].
    exact (i; fst (H i) u v Huv Hi).
  - exact (open_union B I (fun i b => U i (Datatypes.inl b))
             (fun i => fst (snd (H i)))).
  - exact (open_union C I (fun i c => U i (Datatypes.inr c))
             (fun i => snd (snd (H i)))).
Qed.

Lemma tp_whole : tp_open (fun _ => poly_unit).
Proof using All.
  split; [| split ].
  - intros u v _ _; exact ttt.
  - exact (open_whole B).
  - exact (open_whole C).
Qed.

Lemma tp_inter (U V : tp_carrier → Type) :
  tp_open U → tp_open V → tp_open (fun u => U u ∧ V u).
Proof using All.
  intros [HRU [HBU HCU]] [HRV [HBV HCV]].
  split; [| split ].
  - intros u v Huv [Uu Vu].
    exact (HRU u v Huv Uu, HRV u v Huv Vu).
  - exact (open_inter B _ _ HBU HBV).
  - exact (open_inter C _ _ HCU HCV).
Qed.

Definition Pushout_Top : TopSpace := {|
  top_carrier   := tp_carrier;
  IsOpen        := tp_open;
  open_respects := tp_respects;
  open_proper   := tp_proper;
  open_union    := tp_union;
  open_whole    := tp_whole;
  open_inter    := tp_inter
|}.

(** ** The injections *)

Definition tp_inl_map : SetoidMorphism (top_carrier B) tp_carrier.
Proof using All.
  unshelve notypeclasses refine {| morphism := Datatypes.inl |}.
  intros b b' Hb; exact (tpr_inl b b' Hb).
Defined.

Definition tp_inr_map : SetoidMorphism (top_carrier C) tp_carrier.
Proof using All.
  unshelve notypeclasses refine {| morphism := Datatypes.inr |}.
  intros c c' Hc; exact (tpr_inr c c' Hc).
Defined.

Definition Top_po_in1 : B ~{Top}~> Pushout_Top :=
  Build_ContinuousMorphism B Pushout_Top tp_inl_map
    (fun W HW => fst (snd HW)).

Definition Top_po_in2 : C ~{Top}~> Pushout_Top :=
  Build_ContinuousMorphism C Pushout_Top tp_inr_map
    (fun W HW => snd (snd HW)).

(* 相关说明。 （已译） *)
Lemma Top_po_square : Top_po_in1 ∘[Top] f ≈ Top_po_in2 ∘[Top] g.
Proof using All. intro a; exact (tpr_glue a). Qed.

End TopPushout.

Arguments tp_point {B C}.
Arguments tp_rel {A B C} f g u v.
Arguments tp_open {A B C} f g W.
Arguments Pushout_Top {A B C} f g.
Arguments Top_po_in1 {A B C} f g.
Arguments Top_po_in2 {A B C} f g.

(** ** The mediating continuous map *)

Section TopPushoutMediator.

Context {A B C : TopSpace}.
Context (f : A ~{Top}~> B) (g : A ~{Top}~> C).
Context {Q : TopSpace}.
Context (q1 : B ~{Top}~> Q) (q2 : C ~{Top}~> Q).

Definition tp_med_fun (u : @tp_point B C) : carrier (top_carrier Q) :=
  match u with
  | Datatypes.inl b => q1 b
  | Datatypes.inr c => q2 c
  end.

Context (Hcomm : q1 ∘[Top] f ≈ q2 ∘[Top] g).

(* Well-definedness quotient, induction derivation. The
 glue case ONLY one 所消耗 [Hcomm]. （已译） *)
Lemma tp_med_respects (u v : @tp_point B C) (H : tp_rel f g u v) :
  tp_med_fun u ≈ tp_med_fun v.
Proof using All.
  induction H; simpl.
  - now apply proper_morphism.
  - now apply proper_morphism.
  - exact (Hcomm a).
  - now symmetry.
  - now transitivity (tp_med_fun v).
Qed.

Definition tp_med_map
  : SetoidMorphism (top_carrier (Pushout_Top f g)) (top_carrier Q).
Proof using All.
  unshelve notypeclasses refine {| morphism := tp_med_fun |}.
  intros u v Huv; exact (tp_med_respects u v Huv).
Defined.

(*
   本节说明 Pushout 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma tp_med_continuous : Continuous (Pushout_Top f g) Q tp_med_map.
Proof using All.
  intros W HW.
  split; [| split ].
  - intros u v Huv Wu.
    exact (open_proper Q W HW (tp_med_fun u) (tp_med_fun v)
             (tp_med_respects u v Huv) Wu).
  - exact (continuity q1 W HW).
  - exact (continuity q2 W HW).
Qed.

Definition Top_po_med : Pushout_Top f g ~{Top}~> Q :=
  Build_ContinuousMorphism (Pushout_Top f g) Q tp_med_map tp_med_continuous.

Lemma Top_po_med_in1 : Top_po_med ∘[Top] Top_po_in1 f g ≈ q1.
Proof using All. intro b; reflexivity. Qed.

Lemma Top_po_med_in2 : Top_po_med ∘[Top] Top_po_in2 f g ≈ q2.
Proof using All. intro c; reflexivity. Qed.

Lemma Top_po_med_unique (v : Pushout_Top f g ~{Top}~> Q)
      (H1 : v ∘[Top] Top_po_in1 f g ≈ q1)
      (H2 : v ∘[Top] Top_po_in2 f g ≈ q2) :
  Top_po_med ≈ v.
Proof using All.
  intros [b | c]; simpl.
  - symmetry; exact (H1 b).
  - symmetry; exact (H2 c).
Qed.

End TopPushoutMediator.

Arguments Top_po_med {A B C} f g {Q} q1 q2 Hcomm.

(* * ** The 普遍性质, packaged （已译） *)

Local Obligation Tactic := idtac.

#[export] Program Instance Top_HasPushouts : HasPushouts Top := {|
  pushout := fun A B C f g =>
    {| Pull         := Pushout_Top f g;
       pullback_fst := Top_po_in1 f g;
       pullback_snd := Top_po_in2 f g
    |}
|}.
Next Obligation.
  intros A B C f g.
  exact (Top_po_square f g).
Defined.
Next Obligation.
  intros A B C f g Q q1 q2 Hcomm.
  unshelve refine {| unique_obj := Top_po_med f g q1 q2 Hcomm |}.
  - split.
    + exact (Top_po_med_in1 f g q1 q2 Hcomm).
    + exact (Top_po_med_in2 f g q1 q2 Hcomm).
  - intros v [Hv1 Hv2].
    exact (Top_po_med_unique f g q1 q2 Hcomm v Hv1 Hv2).
Defined.

(* 相关说明。 （已译） *)

Definition Top_pushout {A B C : TopSpace}
           (f : A ~{Top}~> B) (g : A ~{Top}~> C) : IsPushout f g :=
  @pushout Top Top_HasPushouts A B C f g.

Example Top_pushout_apex_is_Pushout_Top {A B C : TopSpace}
        (f : A ~{Top}~> B) (g : A ~{Top}~> C) :
  pushout_apex (Top_pushout f g) = Pushout_Top f g := eq_refl.

Example Top_pushout_in1_is_Top_po_in1 {A B C : TopSpace}
        (f : A ~{Top}~> B) (g : A ~{Top}~> C) :
  pushout_in1 (Top_pushout f g) = Top_po_in1 f g := eq_refl.

Example Top_pushout_in2_is_Top_po_in2 {A B C : TopSpace}
        (f : A ~{Top}~> B) (g : A ~{Top}~> C) :
  pushout_in2 (Top_pushout f g) = Top_po_in2 f g := eq_refl.

(* 相关说明。 （已译） *)
Example Top_pushout_carrier {A B C : TopSpace}
        (f : A ~{Top}~> B) (g : A ~{Top}~> C) :
  carrier (top_carrier (Pushout_Top f g))
    = carrier (sum_carrier B C) := eq_refl.

(*
   本节说明伴随、拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Definition AdjunctionSpace {A X Y : TopSpace}
           (i : A ~{Top}~> X) (f : A ~{Top}~> Y) : TopSpace :=
  Pushout_Top i f.

Definition adjunction_in_base {A X Y : TopSpace}
           (i : A ~{Top}~> X) (f : A ~{Top}~> Y)
  : X ~{Top}~> AdjunctionSpace i f := Top_po_in1 i f.

Definition adjunction_in_attached {A X Y : TopSpace}
           (i : A ~{Top}~> X) (f : A ~{Top}~> Y)
  : Y ~{Top}~> AdjunctionSpace i f := Top_po_in2 i f.

(* 相关说明。 （已译） *)
Lemma adjunction_glues {A X Y : TopSpace}
      (i : A ~{Top}~> X) (f : A ~{Top}~> Y) (a : carrier (top_carrier A)) :
  adjunction_in_base i f (i a) ≈ adjunction_in_attached i f (f a).
Proof. exact (@tpr_glue A X Y i f a). Qed.

(* 相关说明。 （已译） *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition tp_side {B C : TopSpace} (u : @tp_point B C) : bool :=
  match u with
  | Datatypes.inl _ => true
  | Datatypes.inr _ => false
  end.

Lemma tp_side_invariant {B C : TopSpace}
      (f : Empty_Top ~{Top}~> B) (g : Empty_Top ~{Top}~> C)
      (u v : @tp_point B C) (H : tp_rel f g u v) :
  tp_side u = tp_side v.
Proof.
  induction H; simpl; try reflexivity.
  - contradiction.
  - now symmetry.
  - now transitivity (tp_side v).
Qed.

(* Over EMPTY span two summands stay apart: glue constructor
 unusable, 论元 being point empty space. （已译） *)
Theorem empty_span_keeps_summands_apart {B C : TopSpace}
        (f : Empty_Top ~{Top}~> B) (g : Empty_Top ~{Top}~> C)
        (b : carrier (top_carrier B)) (c : carrier (top_carrier C)) :
  tp_rel f g (Datatypes.inl b) (Datatypes.inr c) → False.
Proof.
  intro H.
  pose proof (tp_side_invariant f g _ _ H) as Hs.
  simpl in Hs.
  discriminate Hs.
Qed.

(*
   本节说明拉回/推出相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem point_span_merges :
  @tp_rel Point_Top Point_Top Point_Top
    (@id Top Point_Top) (@id Top Point_Top)
    (Datatypes.inl ttt) (Datatypes.inr ttt).
Proof.
  exact (@tpr_glue Point_Top Point_Top Point_Top
           (@id Top Point_Top) (@id Top Point_Top) ttt).
Qed.

(*
   本节说明拉回/推出、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section EmptySpanIsCoproduct.

Context (B C : TopSpace).

Notation Ef := (top_zero B).
Notation Eg := (top_zero C).

(*
   本节说明 Pushout 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma tp_rel_to_sum (u v : sum_carrier B C) (H : tp_rel Ef Eg u v) :
  u ≈ v.
Proof using All.
  induction H.
  - now apply inl_respects.
  - now apply inr_respects.
  - contradiction.
  - now symmetry.
  - now transitivity v.
Qed.

Lemma sum_rel_to_tp (u v : sum_carrier B C) (H : u ≈ v) :
  tp_rel Ef Eg u v.
Proof using All.
  destruct u as [b | c], v as [b' | c']; simpl in H.
  - exact (@tpr_inl Empty_Top B C Ef Eg b b' H).
  - contradiction.
  - contradiction.
  - exact (@tpr_inr Empty_Top B C Ef Eg c c' H).
Qed.

Definition tp_to_sum_map
  : SetoidMorphism (top_carrier (Pushout_Top Ef Eg)) (sum_carrier B C).
Proof using All.
  unshelve notypeclasses refine {| morphism := fun u => u |}.
  intros u v Huv; exact (tp_rel_to_sum u v Huv).
Defined.

Definition tp_from_sum_map
  : SetoidMorphism (sum_carrier B C) (top_carrier (Pushout_Top Ef Eg)).
Proof using All.
  unshelve notypeclasses refine {| morphism := fun u => u |}.
  intros u v Huv; exact (sum_rel_to_tp u v Huv).
Defined.

Definition tp_to_sum : Pushout_Top Ef Eg ~{Top}~> Sum_Top B C.
Proof using All.
  unshelve refine (Build_ContinuousMorphism
                     (Pushout_Top Ef Eg) (Sum_Top B C) tp_to_sum_map _).
  intros W HW.
  split; [| split ]; [| exact (fst HW) | exact (snd HW) ].
  intros u v Huv Wu.
  exact (sum_proper B C W HW u v (tp_rel_to_sum u v Huv) Wu).
Defined.

Definition tp_from_sum : Sum_Top B C ~{Top}~> Pushout_Top Ef Eg.
Proof using All.
  unshelve refine (Build_ContinuousMorphism
                     (Sum_Top B C) (Pushout_Top Ef Eg) tp_from_sum_map _).
  intros W HW.
  exact (fst (snd HW), snd (snd HW)).
Defined.

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Top_pushout_empty_iso : Pushout_Top Ef Eg ≅[Top] Sum_Top B C.
Proof using All.
  unshelve refine {| to := tp_to_sum; from := tp_from_sum |}.
  - intro u; apply Equivalence_Reflexive.
  - intro u; apply Equivalence_Reflexive.
Defined.

End EmptySpanIsCoproduct.
