Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

(*
   本文件给出 Quotient 相关定义与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

(* * * The quotient setoid 等价 关系 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/setoid
 Wikipedia: https://en.wikipedia.org/wiki/Equivalence_class
 Wikipedia: https://en.wikipedia.org/wiki/Quotient_set

   本文件给出商相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   Paper: Barthe, Capretta, Pons, "Setoids in type theory", JFP 13(2) 2003

   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明等价、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** The two forms 假设 （已译） *)

Section Hypotheses.

Context {A : SetoidObject}.
Context (R : crelation (carrier A)).

(* Seven Sketches' form: R is COARSER than the carrier's own equality,
   i.e. `≈` is contained in R. *)
Definition SetoidCoarser : Type := ∀ x y : carrier A, x ≈ y → R x y.

(* Mac Lane's form: R RESPECTS carrier's equality, i.e. R may be
 transported along `≈` either 论元. Stated one-directionally;
 symmetry `≈` gives other direction. （已译） *)
Definition SetoidRespectsRel : Type :=
  ∀ x x' y y' : carrier A, x ≈ x' → y ≈ y' → R x y → R x' y'.

(* Forward: coarseness gives respect, law R it 所消耗 is
 TRANSITIVITY. （已译） *)
Lemma coarser_respects (HR : Transitive R) : SetoidCoarser → SetoidRespectsRel.
Proof.
  intros Hc x x' y y' Hx Hy Hxy.
  transitivity y.
  - transitivity x; [ apply Hc; now symmetry | exact Hxy ].
  - now apply Hc.
Qed.

(* Back: respect gives coarseness, law R it 所消耗 is
 REFLEXIVITY. Given x ≈ y, transport R x x along `≈` second
 论元. （已译） *)
Lemma respects_coarser (HR : Reflexive R) : SetoidRespectsRel → SetoidCoarser.
Proof.
  intros Hr x y Hxy.
  exact (Hr x x x y (reflexivity x) Hxy (HR x)).
Qed.

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem coarser_iff_respects (HR : Equivalence R) :
  SetoidCoarser ↔ SetoidRespectsRel.
Proof.
  split.
  - apply coarser_respects; apply HR.
  - apply respects_coarser; apply HR.
Qed.

End Hypotheses.

Arguments SetoidCoarser {A} R.
Arguments SetoidRespectsRel {A} R.

(* * ** The quotient 对象 projection （已译） *)

(*
   本节说明等价相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition SetsQuotient (A : SetoidObject) (R : crelation (carrier A))
  (HR : Equivalence R) : SetoidObject :=
  {| carrier := carrier A ; is_setoid := {| equiv := R ; setoid_equiv := HR |} |}.

(* 相关说明。 （已译） *)
Example sets_quot_carrier (A : SetoidObject) (R : crelation (carrier A))
  (HR : Equivalence R) : carrier (SetsQuotient A R HR) = carrier A.
Proof. reflexivity. Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sets_quot_proj (A : SetoidObject) (R : crelation (carrier A))
  (HR : Equivalence R) (HC : SetoidCoarser R) :
  A ~{Sets}~> SetsQuotient A R HR.
Proof.
  unshelve refine {| morphism := fun a : carrier A => a |}.
  intros x y Hxy; exact (HC x y Hxy).
Defined.

(* ... action 恒等, conversion. （已译） *)
Example sets_quot_proj_at (A : SetoidObject) (R : crelation (carrier A))
  (HR : Equivalence R) (HC : SetoidCoarser R) (a : carrier A) :
  sets_quot_proj A R HR HC a = a.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Example sets_quot_equiv (A : SetoidObject) (R : crelation (carrier A))
  (HR : Equivalence R) (x y : carrier A) :
  @equiv _ (SetsQuotient A R HR) x y = R x y.
Proof. reflexivity. Qed.

(* * ** The 函子 R-respecting maps （已译） *)

Section RespFunctor.

Context {A : SetoidObject}.
Context (R : crelation (carrier A)).

(* 相关说明。 （已译） *)
Definition SetsRespects (X : SetoidObject) (h : A ~{Sets}~> X) : Type :=
  ∀ x y : carrier A, R x y → h x ≈ h y.

Definition RespMap (X : SetoidObject) : Type :=
  { h : A ~{Sets}~> X & SetsRespects X h }.

(* 相关说明。 （已译） *)
Program Definition RespMap_Setoid (X : SetoidObject) : Setoid (RespMap X) :=
  {| equiv := fun p q => `1 p ≈ `1 q |}.
Next Obligation.
  intros.
  constructor.
  - intros p x; reflexivity.
  - intros p q Hpq x; now symmetry.
  - intros p q r Hpq Hqr x; now transitivity (`1 q x).
Qed.

(* Postcomposition preserves respectfulness. *)
Lemma RespMap_post {X Y : SetoidObject} (k : X ~{Sets}~> Y) (p : RespMap X) :
  SetsRespects Y (k ∘ `1 p).
Proof.
  intros x y Hxy; simpl; unfold Basics.compose.
  apply proper_morphism.
  exact (`2 p x y Hxy).
Qed.

(* The functor.  It is COVARIANT -- postcomposition, not precomposition --
   which is what makes ⟨A/R, p⟩ a universal element in Mac Lane's sense
   rather than a representing object of a presheaf.  Nothing in this
   definition uses any law of R. *)
Program Definition RespFunctor : Sets ⟶ Sets := {|
  fobj := fun X => {| carrier := RespMap X ; is_setoid := RespMap_Setoid X |};
  fmap := fun X Y k =>
    {| morphism := fun p : RespMap X =>
         existT (SetsRespects Y) (k ∘ `1 p) (RespMap_post k p) |}
|}.
Next Obligation. intros X Y k p q Hpq a; simpl; now rewrite (Hpq a). Qed.
Next Obligation. intros X Y k k' Hk p a; simpl; exact (Hk _). Qed.
Next Obligation. intros X p a; simpl; reflexivity. Qed.
Next Obligation. intros X Y Z k k' p a; simpl; reflexivity. Qed.

End RespFunctor.

Arguments SetsRespects {A} R X h.
Arguments RespMap {A} R X.
Arguments RespFunctor {A} R.

(** ** The mediator *)

Section Mediator.

Context {A : SetoidObject}.
Context (R : crelation (carrier A)).
Context (HR : Equivalence R).

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sets_quot_med {X : SetoidObject} (p : RespMap R X) :
  SetsQuotient A R HR ~{Sets}~> X.
Proof.
  unshelve refine
    {| morphism := fun a : carrier (SetsQuotient A R HR) => `1 p a |}.
  intros x y Hxy; exact (`2 p x y Hxy).
Defined.

(* The defining triangle, pointwise [reflexivity]: projection is
 恒等 function, so there nothing compute. （已译） *)
Lemma sets_quot_med_commutes (HC : SetoidCoarser R) {X : SetoidObject}
  (p : RespMap R X) : sets_quot_med p ∘ sets_quot_proj A R HR HC ≈ `1 p.
Proof. intro a; simpl; reflexivity. Qed.

Lemma sets_quot_med_unique (HC : SetoidCoarser R) {X : SetoidObject}
  (p : RespMap R X) (v : SetsQuotient A R HR ~{Sets}~> X)
  (Hv : v ∘ sets_quot_proj A R HR HC ≈ `1 p) : sets_quot_med p ≈ v.
Proof. intro a; simpl; symmetry; exact (Hv a). Qed.

End Mediator.

Arguments sets_quot_med {A} R HR {X} p.

(* 相关说明。 （已译） *)

Section Universal.

Context {A : SetoidObject}.
Context (R : crelation (carrier A)).
Context (HR : Equivalence R).
Context (HC : SetoidCoarser R).

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sets_quot_elem : RespMap R (SetsQuotient A R HR) :=
  existT (SetsRespects R (SetsQuotient A R HR))
    (sets_quot_proj A R HR HC) (fun x y (h : R x y) => h).

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition sets_quot_universal_element :
  AUniversalElement (RespFunctor R) (SetsQuotient A R HR) := {|
  aue_elem := sets_quot_elem
|}.
Next Obligation.
  intros X x.
  unshelve refine {| unique_obj := sets_quot_med R HR x |}.
  - exact (sets_quot_med_commutes R HR HC x).
  - intros v Hv; simpl in *.
    exact (sets_quot_med_unique R HR HC x v Hv).
Defined.

(* 相关说明。 （已译） *)
Example sets_quot_universal_elem_is_proj :
  `1 (@aue_elem _ (RespFunctor R) (SetsQuotient A R HR)
        sets_quot_universal_element)
    = sets_quot_proj A R HR HC.
Proof. reflexivity. Qed.

Example sets_quot_universal_med_is_med {X : SetoidObject} (x : RespMap R X) :
  unique_obj (@aue_universal _ (RespFunctor R) (SetsQuotient A R HR)
                sets_quot_universal_element X x)
    = sets_quot_med R HR x.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sets_quot_Representable : Representable (RespFunctor R) :=
  @Build_Representable Sets (RespFunctor R) (SetsQuotient A R HR)
    (ue_representation (RespFunctor R) (SetsQuotient A R HR)
       sets_quot_universal_element).

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition sets_quot_representation :=
  @represented _ (RespFunctor R) sets_quot_Representable.

(* The 表示 对象 quotient nose. （已译） *)
Example sets_quot_repr_obj :
  @repr_obj _ (RespFunctor R) sets_quot_Representable = SetsQuotient A R HR.
Proof. reflexivity. Qed.

End Universal.

Arguments sets_quot_elem {A} R HR HC.
Arguments sets_quot_universal_element {A} R HR HC.

(* 相关说明。 （已译） *)

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example sets_quot_finest_eq (A : SetoidObject) :
  SetsQuotient A (@equiv _ A) (@setoid_equiv _ A) = A.
Proof. reflexivity. Qed.

Definition sets_quot_finest_coarser (A : SetoidObject) :
  SetoidCoarser (@equiv _ A) := fun _ _ h => h.

(* THE COARSEST: R := total 关系, identifies everything. （已译） *)
Definition TotalRelT (A : SetoidObject) : crelation (carrier A) :=
  fun _ _ => poly_unit.

Lemma TotalRelT_Equivalence (A : SetoidObject) : Equivalence (TotalRelT A).
Proof.
  constructor.
  - intro x; exact ttt.
  - intros x y _; exact ttt.
  - intros x y z _ _; exact ttt.
Qed.

Definition TotalRelT_coarser (A : SetoidObject) : SetoidCoarser (TotalRelT A) :=
  fun _ _ _ => ttt.

Lemma sets_quot_total_collapses (A : SetoidObject) (x y : carrier A) :
  @equiv _ (SetsQuotient A (TotalRelT A) (TotalRelT_Equivalence A)) x y.
Proof. exact ttt. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition NatDiscrete : SetoidObject :=
  {| carrier := nat ; is_setoid := eq_Setoid nat |}.

Definition nat_parity : crelation (carrier NatDiscrete) :=
  fun m n => Nat.even m = Nat.even n.

Lemma nat_parity_Equivalence : Equivalence nat_parity.
Proof.
  constructor.
  - intro m; reflexivity.
  - intros m n H; now symmetry.
  - intros m n k H1 H2; now transitivity (Nat.even n).
Qed.

Definition nat_parity_coarser : SetoidCoarser nat_parity :=
  fun m n (H : m = n) => f_equal Nat.even H.

Definition NatParity : SetoidObject :=
  SetsQuotient NatDiscrete nat_parity nat_parity_Equivalence.

(* 相关说明。 （已译） *)
Example nat_parity_merges : @equiv _ NatParity 0%nat 2%nat.
Proof. reflexivity. Qed.

(* The quotient SEPARATES: 0 1 not. This where decidable
 invariant earns keep -- 关系 unfolds [true = false]. （已译） *)
Lemma nat_parity_separates : @equiv _ NatParity 0%nat 1%nat → False.
Proof. intro H; discriminate H. Qed.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma nat_parity_not_finest :
  (∀ m n : carrier NatDiscrete, nat_parity m n → @equiv _ NatDiscrete m n) → False.
Proof.
  intro H.
  pose proof (H 0%nat 2%nat eq_refl) as E; discriminate E.
Qed.

Lemma nat_parity_not_coarsest :
  (∀ m n : carrier NatDiscrete, TotalRelT NatDiscrete m n → nat_parity m n) → False.
Proof. intro H; exact (nat_parity_separates (H 0%nat 1%nat ttt)). Qed.

(* And 普遍性质 inhabited at it: parity map itself
 respecting map, so mediator out quotient exists and
 computes closed input. （已译） *)
Definition BoolSet : SetoidObject :=
  {| carrier := bool ; is_setoid := eq_Setoid bool |}.

(*
   本节说明 Quotient 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition nat_even_map : NatDiscrete ~{Sets}~> BoolSet.
Proof.
  unshelve refine {| morphism := Nat.even |}.
Defined.

Definition nat_even_resp : RespMap nat_parity BoolSet :=
  existT (SetsRespects nat_parity BoolSet)
    nat_even_map (fun m n (H : nat_parity m n) => H).

(* 相关说明。 （已译） *)
Example nat_parity_med_at_4 :
  sets_quot_med nat_parity nat_parity_Equivalence nat_even_resp 4%nat = true.
Proof. reflexivity. Qed.

Example nat_parity_med_at_7 :
  sets_quot_med nat_parity nat_parity_Equivalence nat_even_resp 7%nat = false.
Proof. reflexivity. Qed.
