Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.CopyDiscard.
Require Import Category.Structure.Monoidal.CopyDiscard.Deterministic.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.CommutativeComonoid.
Require Import Category.Theory.Algebra.Comonoid.Hom.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Presentation.
Require Import Category.Construction.ColouredPROP.Linear.
Require Import Category.Construction.ColouredPROP.Supply.
Require Import Category.Construction.ColouredPROP.Supply.Instance.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
   nLab: https://ncatlab.org/nlab/show/copy-discard+category
   nLab: https://ncatlab.org/nlab/show/comonoid
   Reference: Benton, "A mixed linear and non-linear logic: proofs,
   Reference: Cho & Jacobs, "Disintegration and Bayesian inversion via
   Reference: Fong & Spivak, "Supplying bells and whistles in

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* ------------------------------------------------------------------ *)

(* * ** The bridge: supplied 对象 deterministic maps （已译） *)

Section LNLBridge.

Context {Colour : Type}.
Context (P : ColouredPROP Colour).
Context (copyable : Colour -> bool).
Context `{SS : @SelectiveSupply Colour P copyable}.

(** The coloured-PROP-对象 [⟦cs⟧c], in
 [Construction/ColouredPROP.v] (whose notation section-local
 there must re-declared per file). （已译） *)
Notation "⟦ cs ⟧c" := (@cprop_of_list Colour P cs)
  (at level 0, format "⟦ cs ⟧c").

(*
   本节说明 LNL 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SupplyDeterministic {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) : Type :=
  @ComonoidHom P (MBc P) ⟦cs⟧c ⟦ds⟧c
    (@ccomon_comonoid P (@cprop_symmetric Colour P) ⟦cs⟧c
       (supply_list cs Hc))
    (@ccomon_comonoid P (@cprop_symmetric Colour P) ⟦ds⟧c
       (supply_list ds Hd))
    f.

(** 本节：The bridge predicate IS Linear.v's determinism predicate, the
 nose. （已译） *)
Example SupplyDeterministic_is_sel_deterministic
  {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) :
  SupplyDeterministic Hc Hd f = sel_deterministic Hc Hd f := eq_refl.

(*
   本节说明幺半结构、幺半群、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition supplied_obj (cs : list Colour)
  (H : all_copyable copyable cs) : @Comon (cprop_cat P) (MBc P) :=
  (⟦cs⟧c;
   @ccomon_comonoid P (@cprop_symmetric Colour P) ⟦cs⟧c
     (supply_list cs H)).

(** A supply-deterministic map lifts [Comon]-hom between the
 supplied 对象: sigma-pack map determinism
 witness. （已译） *)
Definition LNL_lift {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) (Hf : SupplyDeterministic Hc Hd f) :
  supplied_obj cs Hc ~{@Comon (cprop_cat P) (MBc P)}~> supplied_obj ds Hd :=
  (f; Hf).

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example LNL_hom_is_deterministic (cs ds : list Colour)
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds) :
  (supplied_obj cs Hc ~{@Comon (cprop_cat P) (MBc P)}~> supplied_obj ds Hd)
  = { f : ⟦cs⟧c ~{P}~> ⟦ds⟧c & SupplyDeterministic Hc Hd f }
  := eq_refl.

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma LNL_forget_lift {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) (Hf : SupplyDeterministic Hc Hd f) :
  fmap[@Comon_Forget (cprop_cat P) (MBc P)] (LNL_lift Hc Hd f Hf) ≈ f.
Proof. reflexivity. Qed.

Lemma LNL_lift_unique {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c) (Hf : SupplyDeterministic Hc Hd f)
  (u : supplied_obj cs Hc
         ~{@Comon (cprop_cat P) (MBc P)}~> supplied_obj ds Hd) :
  fmap[@Comon_Forget (cprop_cat P) (MBc P)] u ≈ f ->
  u ≈[@Comon (cprop_cat P) (MBc P)] LNL_lift Hc Hd f Hf.
Proof.
  intros Hu.
  apply (@fmap_inj _ _ _ (@Comon_Forget_Faithful (cprop_cat P) (MBc P)) _ _).
  rewrite LNL_forget_lift.
  exact Hu.
Qed.

(** The eta-form uniqueness: every [Comon]-hom between supplied
 对象 lift own underlying map, determinism
 witness being own second projection. （已译） *)
Corollary LNL_lift_eta {cs ds : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (u : supplied_obj cs Hc
         ~{@Comon (cprop_cat P) (MBc P)}~> supplied_obj ds Hd) :
  u ≈[@Comon (cprop_cat P) (MBc P)]
  LNL_lift Hc Hd (fmap[@Comon_Forget (cprop_cat P) (MBc P)] u) `2 u.
Proof.
  apply LNL_lift_unique.
  reflexivity.
Qed.

(*
   本节说明函子、hom、等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma LNL_lift_id (cs : list Colour) (Hc : all_copyable copyable cs)
  (Hid : SupplyDeterministic Hc Hc (@id P ⟦cs⟧c)) :
  LNL_lift Hc Hc id Hid ≈[@Comon (cprop_cat P) (MBc P)] id.
Proof.
  change (@id P ⟦cs⟧c ≈ @id P ⟦cs⟧c).
  reflexivity.
Qed.

Lemma LNL_lift_comp {cs ds es : list Colour}
  (Hc : all_copyable copyable cs) (Hd : all_copyable copyable ds)
  (He : all_copyable copyable es)
  (g : ⟦ds⟧c ~{P}~> ⟦es⟧c) (f : ⟦cs⟧c ~{P}~> ⟦ds⟧c)
  (Hg : SupplyDeterministic Hd He g) (Hf : SupplyDeterministic Hc Hd f)
  (Hgf : SupplyDeterministic Hc He (g ∘ f)) :
  LNL_lift Hc He (g ∘ f) Hgf
    ≈[@Comon (cprop_cat P) (MBc P)]
  LNL_lift Hd He g Hg ∘[@Comon (cprop_cat P) (MBc P)] LNL_lift Hc Hd f Hf.
Proof.
  change (g ∘ f ≈ g ∘ f).
  reflexivity.
Qed.

End LNLBridge.

(* ------------------------------------------------------------------ *)

(*
   本节说明幺半结构、幺半群相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section TotalSupply.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (S : CSignature Colour).

(** 本节：Every colour word all-copyable total predicate: a
 computing fixpoint ([forallb (fun _ => true)] peels cons cells
 definitionally). （已译） *)
Fixpoint all_true (cs : list Colour) :
  all_copyable (fun _ : Colour => true) cs :=
  match cs with
  | [] => eq_refl
  | _ :: cs' => all_true cs'
  end.

Notation TotalPROP := (SupplyPROP Cdec S (fun _ : Colour => true)).
Notation TotalSS :=
  (SupplyPROP_SelectiveSupply Cdec S (fun _ : Colour => true)).

(** Decidable 对象 equality presented supply PROP: 对象
 colour words (per D2 discipline 这是 定义 fed
 one canonical [Cdec], not instance). （已译） *)
Definition TotalPROP_ObjDecEq : @ObjDecEq (cprop_cat TotalPROP) :=
  CFreeCat_ObjDecEq (SupplyExtSig S (fun _ : Colour => true)) Cdec.

(*
   本节说明 LNL 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := intros.

Program Definition CopyDiscard_of_total_supply :
  @CopyDiscard (cprop_cat TotalPROP)
    (@cprop_symmetric Colour TotalPROP) := {|
  cd_comonoid := fun X : cprop_cat TotalPROP =>
    supply_list (P := TotalPROP) (SS := TotalSS) X (all_true X)
|}.
Next Obligation.
  (* 相关说明。 （已译） *)
  exact (@supply_app_delta Colour TotalPROP TotalPROP_ObjDecEq
           (fun _ : Colour => true) TotalSS
           X Y (all_true X) (all_true Y) (all_true ((X ++ Y)%list))).
Qed.
Next Obligation.
  (* cd_tensor_epsilon: mirror. *)
  exact (@supply_app_epsilon Colour TotalPROP TotalPROP_ObjDecEq
           (fun _ : Colour => true) TotalSS
           X Y (all_true X) (all_true Y) (all_true ((X ++ Y)%list))).
Qed.
Next Obligation.
  (* 相关说明。 （已译） *)
  reflexivity.
Qed.
Next Obligation.
  (* cd_unit_epsilon: ε 恒等 nose. （已译） *)
  reflexivity.
Qed.

(** The copy discard 态射 degenerate instance the
 derived supply's, definitionally. （已译） *)
Example CopyDiscard_of_total_supply_copy (X : list Colour) :
  @copy (cprop_cat TotalPROP) (@cprop_symmetric Colour TotalPROP)
    CopyDiscard_of_total_supply X
  = scopy (P := TotalPROP) (SS := TotalSS) X (all_true X) := eq_refl.

Example CopyDiscard_of_total_supply_discard (X : list Colour) :
  @discard (cprop_cat TotalPROP) (@cprop_symmetric Colour TotalPROP)
    CopyDiscard_of_total_supply X
  = sdiscard (P := TotalPROP) (SS := TotalSS) X (all_true X) := eq_refl.

(*
   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example SupplyDeterministic_is_deterministic (X Y : list Colour)
  (f : X ~{TotalPROP}~> Y) :
  SupplyDeterministic TotalPROP (fun _ : Colour => true)
    (SS := TotalSS) (all_true X) (all_true Y) f
  = @deterministic _ _ CopyDiscard_of_total_supply X Y f
  := eq_refl.

End TotalSupply.

(* ------------------------------------------------------------------ *)

(*
   本节说明hom、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Characterization.

Context {Colour : Type}.
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (copyable : Colour -> bool).

Notation PurePROP := (SupplyPROP Cdec Empty_CSig copyable).

Theorem linear_cartesian_characterization (c : Colour) :
  (LinearColour copyable c
     <-> ((@CommutativeComonoid (cprop_cat PurePROP)
             (@cprop_symmetric Colour PurePROP)
             (wire (P := PurePROP) c) -> False)
          /\ ((([c] : list Colour) ~{PurePROP}~> [c; c]) -> False)))
  /\ (copyable c = true
     <-> (inhabited (@CommutativeComonoid (cprop_cat PurePROP)
                       (@cprop_symmetric Colour PurePROP)
                       (wire (P := PurePROP) c))
          /\ inhabited (([c] : list Colour) ~{PurePROP}~> [c; c]))).
Proof.
  split.
  - (* linear <-> neither supply nor fan-out *)
    split.
    + intros Hlin.
      split.
      * (* no supply: its comultiplication would BE a fan-out *)
        intros M.
        exact (SupplyPROP_no_fanout Cdec Empty_CSig copyable c Hlin
                 (pure_base_conservative Cdec c)
                 (@ccomon_delta (cprop_cat PurePROP)
                    (@cprop_symmetric Colour PurePROP)
                    (wire (P := PurePROP) c) M)).
      * (* no fan-out *)
        exact (SupplyPROP_no_fanout Cdec Empty_CSig copyable c Hlin
                 (pure_base_conservative Cdec c)).
    + intros [HnoM _].
      destruct (copyable c) eqn:Hc.
      * exfalso.
        exact (HnoM (supply_wire_comonoid Cdec Empty_CSig copyable c Hc)).
      * exact Hc.
  - (* copyable <-> both supply and fan-out *)
    split.
    + intros Hc.
      split.
      * exact (inhabits
                 (supply_wire_comonoid Cdec Empty_CSig copyable c Hc)).
      * exact (inhabits (SupplyPROP_fanout Cdec Empty_CSig copyable c Hc)).
    + intros [_ [t]].
      destruct (copyable c) eqn:Hc.
      * reflexivity.
      * exfalso.
        exact (SupplyPROP_no_fanout Cdec Empty_CSig copyable c Hc
                 (pure_base_conservative Cdec c) t).
Qed.

End Characterization.
