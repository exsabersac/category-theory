Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Theory.Lambek.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Coq.
Require Import Category.Theory.Adamek.Corollaries.

Generalizable All Variables.

(* 相关说明。 （已译） *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Initial_algebra

   本文件给出自然数相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   关于the statement的来源与用途

   nLab:      https://ncatlab.org/nlab/show/natural+numbers+object
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:      Awodey, "Category Theory" (1st ed., Carnegie Mellon
   Book:      Riehl, "Category Theory in Context" (2nd ed. numbering,
   Paper:     Lawvere, "An elementary theory of the category of sets",
   Paper:     Lambek, "A Fixpoint Theorem for Complete Categories",

   本节说明来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[local] Obligation Tactic := idtac.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition alg_pt {X : Type} (α : FAlgebra NatF X) : X := α None.

(* 相关说明。 （已译） *)
Definition alg_step {X : Type} (α : FAlgebra NatF X) : X ~{Coq}~> X :=
  fun x => α (Some x).

(* Conversely, a point and an endomap assemble into an algebra. *)
Definition alg_of_triple {X : Type} (x0 : X) (f : X ~{Coq}~> X)
  : FAlgebra NatF X :=
  fun o => match o with
           | None   => x0
           | Some x => f x
           end.

(*
   本节说明 Nat 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma alg_pt_of_triple {X : Type} (x0 : X) (f : X ~{Coq}~> X) :
  alg_pt (alg_of_triple x0 f) = x0.
Proof. reflexivity. Qed.

Lemma alg_step_of_triple {X : Type} (x0 : X) (f : X ~{Coq}~> X) :
  alg_step (alg_of_triple x0 f) ≈ f.
Proof. intro x; reflexivity. Qed.

Lemma alg_of_triple_eta {X : Type} (α : FAlgebra NatF X) :
  alg_of_triple (alg_pt α) (alg_step α) ≈ α.
Proof. intro o; destruct o as [x|]; reflexivity. Qed.

(* At level arrows, 交换方块 algebra map exactly
 Riehl's pair clauses: map carries point point intertwines the
 two endomaps. （已译） *)

Lemma alg_hom_clauses {X Y : Type}
      (α : FAlgebra NatF X) (β : FAlgebra NatF Y) (h : X ~{Coq}~> Y) :
  h ∘ α ≈ β ∘ fmap[NatF] h ->
  (h (alg_pt α) = alg_pt β) * (∀ x, h (alg_step α x) = alg_step β (h x)).
Proof.
  intro Hh; split.
  - exact (Hh None).
  - intro x; exact (Hh (Some x)).
Qed.

Lemma clauses_alg_hom {X Y : Type}
      (α : FAlgebra NatF X) (β : FAlgebra NatF Y) (h : X ~{Coq}~> Y) :
  h (alg_pt α) = alg_pt β ->
  (∀ x, h (alg_step α x) = alg_step β (h x)) ->
  h ∘ α ≈ β ∘ fmap[NatF] h.
Proof.
  intros H0 HS o; destruct o as [x|].
  - exact (HS x).
  - exact H0.
Qed.

(* 相关说明。 （已译） *)

(* 相关说明。 （已译） *)
Definition nat_alg : FAlgebra NatF nat := alg_of_triple O S.

(* 相关说明。 （已译） *)
Fixpoint nat_fold {Y : Type} (beta : FAlgebra NatF Y) (n : nat) : Y :=
  match n with
  | O   => alg_pt beta
  | S k => alg_step beta (nat_fold beta k)
  end.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma hom_is_nat_fold {Y : Type} (beta : FAlgebra NatF Y)
      (h : nat ~{Coq}~> Y)
      (Hh : h ∘ nat_alg ≈ beta ∘ fmap[NatF] h)
      (n : nat) : h n = nat_fold beta n.
Proof.
  induction n as [|k IH].
  - exact (Hh None).
  - simpl.
    rewrite <- IH.
    exact (Hh (Some k)).
Qed.

(* The unique algebra map [(nat, nat_alg)] arbitrary algebra [y],
 packaging fold together 交换方块. （已译） *)
Program Definition nat_alg_hom (y : FAlg NatF)
  : (nat; nat_alg) ~{FAlg NatF}~> y :=
  {| falg_hom := nat_fold (`2 y) |}.
Next Obligation.
  (* fold ∘ nat_alg ≈ β ∘ fmap fold, checked shape by shape *)
  intros y o; destruct o as [k|]; reflexivity.
Qed.

(* [nat] together [nat_alg] initial [NatF]-algebra: it the
 终对象 opposite algebra 范畴. （已译） *)
Program Definition nat_initial : @Initial (FAlg NatF) := {|
  terminal_obj := (nat; nat_alg);
  one := fun y => nat_alg_hom y
|}.
Next Obligation.
  (* 相关说明。 （已译） *)
  intros x f g.
  destruct f as [hf Hf], g as [hg Hg].
  intro n; simpl.
  rewrite (hom_is_nat_fold (`2 x) hf Hf n).
  rewrite (hom_is_nat_fold (`2 x) hg Hg n).
  reflexivity.
Qed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary nat_recursion {Y : Type} (y0 : Y) (f : Y ~{Coq}~> Y) :
  ∃! h : nat ~{Coq}~> Y, (h O = y0) * (∀ n, h (S n) = f (h n)).
Proof.
  exists (nat_fold (alg_of_triple y0 f)).
  - split; [ reflexivity | intro n; reflexivity ].
  - intros v [Hz Hs] n.
    symmetry.
    exact (hom_is_nat_fold (alg_of_triple y0 f) v
             (clauses_alg_hom nat_alg (alg_of_triple y0 f) v Hz Hs) n).
Qed.

(** ** Lambek's lemma at [nat] *)

(* The initial structure map invertible, so [nat] fixed point of
 [1 + (-)]: 同构 [option nat ≅ nat] whose forward direction is
 [nat_alg] itself. （已译） *)
Corollary nat_lambek : NatF nat ≅ nat.
Proof. exact (lambek NatF nat_initial). Qed.

(* The same 同构 orientation [nat ≅ 1 + nat]. （已译） *)
Corollary nat_lambek_sym : nat ≅ NatF nat.
Proof. exact (iso_sym nat_lambek). Qed.

(* * ** Awodey Ex 10.6.1(c): characterisation up 同构 （已译） *)

(*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem nat_initial_unique (I : @Initial (FAlg NatF)) :
  @initial_obj (FAlg NatF) I ≅[FAlg NatF] (nat; nat_alg).
Proof.
  unshelve refine {| to   := @zero (FAlg NatF) I (nat; nat_alg)
                   ; from := @zero (FAlg NatF) nat_initial
                               (@initial_obj (FAlg NatF) I) |}.
  - exact (@zero_unique (FAlg NatF) nat_initial (nat; nat_alg) _ id).
  - exact (@zero_unique (FAlg NatF) I (@initial_obj (FAlg NatF) I) _ id).
Qed.

(*
   本节说明同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary nat_initial_carrier_unique (I : @Initial (FAlg NatF)) :
  `1 (@initial_obj (FAlg NatF) I) ≅[Coq] nat.
Proof.
  pose proof (nat_initial_unique I) as iso.
  unshelve refine {| to   := falg_hom[to iso]
                   ; from := falg_hom[from iso] |}.
  - exact (iso_to_from iso).
  - exact (iso_from_to iso).
Qed.

(* 相关说明。 （已译） *)

(*
   本节说明 Nat 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Endos : Category := FAlg (Id[Coq]).

(*
   本节说明函子、hom、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Endos_Forget : Endos ⟶ Sets := {|
  fobj := fun x => {| carrier := ``x ; is_setoid := eq_Setoid ``x |};
  fmap := fun x y f => {| morphism := falg_hom[f] |}
|}.
Next Obligation. intros x y f a b Hab; now rewrite Hab. Qed.
Next Obligation. intros x y f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros x a; reflexivity. Qed.
Next Obligation. intros x y z f g a; reflexivity. Qed.

(* The candidate 表示 对象: naturals successor, no point. （已译） *)
Definition nat_succ : FAlgebra Id[Coq] nat := S.

Definition NatSucc : Endos := (nat; nat_succ).

#[local] Notation HomNS := (@Curried_Hom Endos NatSucc).

(* 相关说明。 （已译） *)
Fixpoint nat_iter {X : Type} (x0 : X) (f : X ~{Coq}~> X) (n : nat) : X :=
  match n with
  | O   => x0
  | S k => f (nat_iter x0 f k)
  end.

(* Iteration natural 对象 [Endos]: endomorphism-preserving
 map carries iterate point iterate image. （已译） *)
Lemma nat_iter_natural {y z : Endos} (g : y ~{Endos}~> z) (y0 : ``y) (n : nat) :
  falg_hom[g] (nat_iter y0 (`2 y) n) = nat_iter (falg_hom[g] y0) (`2 z) n.
Proof.
  induction n as [|k IH]; simpl.
  - reflexivity.
  - transitivity ((`2 z) (falg_hom[g] (nat_iter y0 (`2 y) k))).
    + exact (@falg_commutes _ _ _ _ _ _ g (nat_iter y0 (`2 y) k)).
    + f_equal; exact IH.
Qed.

(* 相关说明。 （已译） *)
Lemma nat_iter_eval {y : Endos} (h : NatSucc ~{Endos}~> y) (n : nat) :
  nat_iter (falg_hom[h] O) (`2 y) n = falg_hom[h] n.
Proof.
  induction n as [|k IH]; simpl.
  - reflexivity.
  - transitivity ((`2 y) (falg_hom[h] k)).
    + f_equal; exact IH.
    + symmetry; exact (@falg_commutes _ _ _ _ _ _ h k).
Qed.

(* Φ: evaluate an endomorphism-preserving map at zero. *)
Program Definition nat_eval_at_zero (y : Endos)
  : HomNS y ~{Sets}~> Endos_Forget y :=
  {| morphism := fun h => falg_hom[h] O |}.
Next Obligation. intros y h k Hhk; exact (Hhk O). Qed.

(* Ψ: send point iterate along endomap, automatically an
 endomorphism-preserving map because [nat_iter x0 f (S n)] [f] applied to
 [nat_iter x0 f n] 定义. （已译） *)
Program Definition nat_iterate (y : Endos)
  : Endos_Forget y ~{Sets}~> HomNS y :=
  {| morphism := fun y0 => {| falg_hom := nat_iter y0 (`2 y) |} |}.
Next Obligation. intros y y0 n; reflexivity. Qed.

Program Definition nat_eval_transform : HomNS ⟹ Endos_Forget :=
  Build_Transform' nat_eval_at_zero _.
Next Obligation. intros y z g h; reflexivity. Qed.

Program Definition nat_iterate_transform : Endos_Forget ⟹ HomNS :=
  Build_Transform' nat_iterate _.
Next Obligation. intros y z g y0 n; exact (nat_iter_natural g y0 n). Qed.

(* The representation: [Hom((nat, S), ─) ≅ Endos_Forget] [[Endos, Sets]].
 Evaluation at zero iteration mutually inverse, naturally the
 对象 [Endos]. （已译） *)
Program Definition nat_succ_represents
  : HomNS ≅[[Endos, Sets]] Endos_Forget :=
  {| to := nat_eval_transform; from := nat_iterate_transform |}.
Next Obligation. intros y y0; reflexivity. Qed.
Next Obligation. intros y h n; exact (nat_iter_eval h n). Qed.

#[export] Program Instance nat_succ_Representable
  : Representable Endos_Forget := {|
  repr_obj := NatSucc;
  represented := nat_succ_represents
|}.

(* The universal element representation, sense Yoneda
 引理: image 恒等 under 表示 同构. It is
 zero, nose. （已译） *)
Lemma nat_universal_element :
  transform (to nat_succ_represents) NatSucc (id{Endos}) = O.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明函子、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section UniversalElement.

Context (Repr : Representable Endos_Forget).

(*
   本节说明同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Notation RObj := (@repr_obj _ _ Repr).
Notation RIso := (@represented _ _ Repr).

(* The universal element: image 恒等. （已译） *)
Definition repr_element : ``RObj := transform (to RIso) RObj (id{Endos}).

(* The algebra 表示 对象 pointed at universal element. （已译） *)
Definition repr_alg : FAlg NatF :=
  (``RObj ; alg_of_triple repr_element (`2 RObj)).

(*
   本节说明Yoneda、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma repr_eval {y : Endos} (h : RObj ~{Endos}~> y) :
  falg_hom[h] repr_element = transform (to RIso) y h.
Proof.
  transitivity (transform (to RIso) y (h ∘ id{Endos})).
  - exact (naturality (to RIso) RObj y h (id{Endos})).
  - apply (@proper_morphism _ _ _ _ (transform (to RIso) y)).
    apply id_right.
Qed.

(* Each [NatF]-algebra gives an object of [Endos] by forgetting the point. *)
Definition endo_of (y : FAlg NatF) : Endos :=
  (``y ; (alg_step (`2 y) : FAlgebra Id[Coq] ``y)).

(* 相关说明。 （已译） *)
Definition repr_med (y : FAlg NatF) : RObj ~{Endos}~> endo_of y :=
  transform (from RIso) (endo_of y) (alg_pt (`2 y)).

(* 相关说明。 （已译） *)
Lemma repr_med_pt (y : FAlg NatF) :
  falg_hom[repr_med y] repr_element = alg_pt (`2 y).
Proof.
  transitivity (transform (to RIso) (endo_of y) (repr_med y)).
  - exact (repr_eval (repr_med y)).
  - exact (iso_to_from RIso (endo_of y) (alg_pt (`2 y))).
Qed.

(* 相关说明。 （已译） *)
Program Definition repr_alg_hom (y : FAlg NatF)
  : repr_alg ~{FAlg NatF}~> y :=
  {| falg_hom := falg_hom[repr_med y] |}.
Next Obligation.
  intro y.
  apply clauses_alg_hom.
  - exact (repr_med_pt y).
  - exact (@falg_commutes _ _ _ _ _ _ (repr_med y)).
Qed.

(* 相关说明。 （已译） *)
Program Definition endo_of_alg_hom {y : FAlg NatF}
        (f : repr_alg ~{FAlg NatF}~> y) : RObj ~{Endos}~> endo_of y :=
  {| falg_hom := falg_hom[f] |}.
Next Obligation.
  intros y f.
  exact (snd (alg_hom_clauses _ _ _ (@falg_commutes _ _ _ _ _ _ f))).
Qed.

(* An arrow out 表示 对象 determined image under
 representation, since 同构 at every 对象. （已译） *)
Lemma repr_hom_determined {y : Endos} (k l : RObj ~{Endos}~> y)
      (H : transform (to RIso) y k = transform (to RIso) y l) : k ≈ l.
Proof.
  transitivity (transform (from RIso) y (transform (to RIso) y k)).
  - symmetry; exact (iso_from_to RIso y k).
  - transitivity (transform (from RIso) y (transform (to RIso) y l)).
    + apply (@proper_morphism _ _ _ _ (transform (from RIso) y)); exact H.
    + exact (iso_from_to RIso y l).
Qed.

(* Every algebra map out [repr_alg] sends universal element the
 point target: point clause 交换方块,
 transported along [repr_eval]. （已译） *)
Lemma repr_alg_hom_pt {y : FAlg NatF} (f : repr_alg ~{FAlg NatF}~> y) :
  transform (to RIso) (endo_of y) (endo_of_alg_hom f) = alg_pt (`2 y).
Proof.
  transitivity (falg_hom[endo_of_alg_hom f] repr_element).
  - symmetry; exact (repr_eval (endo_of_alg_hom f)).
  - exact (fst (alg_hom_clauses _ _ _ (@falg_commutes _ _ _ _ _ _ f))).
Qed.

(* ... so any two of them agree. *)
Lemma repr_alg_hom_unique {y : FAlg NatF}
      (f g : repr_alg ~{FAlg NatF}~> y) : f ≈ g.
Proof.
  refine (repr_hom_determined (endo_of_alg_hom f) (endo_of_alg_hom g) _).
  transitivity (alg_pt (`2 y)).
  - exact (repr_alg_hom_pt f).
  - symmetry; exact (repr_alg_hom_pt g).
Qed.

(* The criterion itself. *)
Program Definition repr_initial : @Initial (FAlg NatF) := {|
  terminal_obj := repr_alg;
  one := fun y => repr_alg_hom y
|}.
Next Obligation. intros y f g; exact (repr_alg_hom_unique f g). Qed.

End UniversalElement.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition nat_initial_via_universal_element : @Initial (FAlg NatF) :=
  repr_initial nat_succ_Representable.

Lemma nat_initial_agree :
  @initial_obj (FAlg NatF) nat_initial_via_universal_element
    = @initial_obj (FAlg NatF) nat_initial.
Proof. reflexivity. Qed.
