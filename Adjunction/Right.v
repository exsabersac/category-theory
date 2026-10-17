(** * Adjoint on the right: pairs of contravariant functors *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.

(*
   本文件给出伴随相关构造与性质。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Open Scope category_scope.

Generalizable All Variables.

(*
   Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Book:  Riehl, "Category Theory in Context", §4.4
   nLab:  https://ncatlab.org/nlab/show/mutually+left+adjoint+functors
   nLab:  https://ncatlab.org/nlab/show/adjoint+functor
   nLab:  https://ncatlab.org/nlab/show/opposite+category

   本节说明伴随、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明伴随相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Example obj_op_is_obj (X : Category) : obj[X^op] = obj[X] := eq_refl.

Example hom_op_is_hom (A : Category) (a b : A) :
  (a ~{A}~> b) = (b ~{A^op}~> a) := eq_refl.

Section AdjointOnTheRight.

Universes o1 h1 p1 o2 h2 p2.
Context {A : Category@{o1 h1 p1}}.
Context {X : Category@{o2 h2 p2}}.
Context (S : (A^op) ⟶ X).
Context (T : (X^op) ⟶ A).

Class AdjointOnTheRight@{o3 so sh sp} := {
  aor {a x} :
    @Isomorphism@{so sh sp} Sets@{o3 so}
      {| carrier := @hom A a (T x); is_setoid := @homset A a (T x) |}
      {| carrier := @hom X x (S a); is_setoid := @homset X x (S a) |};

  to_aor_nat_a {a a' x} (f : a ~{A}~> T x) (g : a' ~{A}~> a) :
    to aor (f ∘ g) ≈ fmap[S] g ∘ to aor f;
  to_aor_nat_x {a x x'} (f : a ~{A}~> T x') (k : x ~{X}~> x') :
    to aor (fmap[T] k ∘ f) ≈ to aor f ∘ k;

  from_aor_nat_a {a a' x} (p : x ~{X}~> S a) (g : a' ~{A}~> a) :
    from aor (fmap[S] g ∘ p) ≈ from aor p ∘ g;
  from_aor_nat_x {a x x'} (p : x' ~{X}~> S a) (k : x ~{X}~> x') :
    from aor (p ∘ k) ≈ fmap[T] k ∘ from aor p
}.

Class AdjointOnTheLeft@{o3 so sh sp} := {
  aol {x a} :
    @Isomorphism@{so sh sp} Sets@{o3 so}
      {| carrier := @hom A (T x) a; is_setoid := @homset A (T x) a |}
      {| carrier := @hom X (S a) x; is_setoid := @homset X (S a) x |};

  to_aol_nat_a {x a a'} (f : T x ~{A}~> a) (g : a ~{A}~> a') :
    to aol (g ∘ f) ≈ to aol f ∘ fmap[S] g;
  to_aol_nat_x {x x' a} (f : T x ~{A}~> a) (k : x ~{X}~> x') :
    to aol (f ∘ fmap[T] k) ≈ k ∘ to aol f;

  from_aol_nat_a {x a a'} (p : S a ~{X}~> x) (g : a ~{A}~> a') :
    from aol (p ∘ fmap[S] g) ≈ g ∘ from aol p;
  from_aol_nat_x {x x' a} (p : S a ~{X}~> x) (k : x ~{X}~> x') :
    from aol (k ∘ p) ≈ from aol p ∘ fmap[T] k
}.

End AdjointOnTheRight.

Arguments AdjointOnTheRight {A X} S T.
Arguments AdjointOnTheLeft {A X} S T.

(* ---------------- reduction to ordinary adjunctions ---------------- *)

Definition Adjunction_of_AdjointOnTheRight
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheRight S T) :
  @Adjunction (A^op) X (Opposite_Functor T) S :=
  @Build_Adjunction (A^op) X (Opposite_Functor T) S
    (fun x a => @aor A X S T H a x)
    (fun x y z f g => @to_aor_nat_x   A X S T H z x y f g)
    (fun x y z f g => @to_aor_nat_a   A X S T H y z x g f)
    (fun x y z f g => @from_aor_nat_x A X S T H z x y f g)
    (fun x y z f g => @from_aor_nat_a A X S T H y z x g f).

Definition AdjointOnTheRight_of_Adjunction
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : @Adjunction (A^op) X (Opposite_Functor T) S) :
  AdjointOnTheRight S T :=
  @Build_AdjointOnTheRight A X S T
    (fun a x => @adj (A^op) X (Opposite_Functor T) S H x a)
    (fun a a2 x f g => @to_adj_nat_r   (A^op) X _ S H x a a2 g f)
    (fun a x x2 f k => @to_adj_nat_l   (A^op) X _ S H x x2 a f k)
    (fun a a2 x p g => @from_adj_nat_r (A^op) X _ S H x a a2 g p)
    (fun a x x2 p k => @from_adj_nat_l (A^op) X _ S H x x2 a p k).

Definition Adjunction_of_AdjointOnTheLeft
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheLeft S T) :
  @Adjunction A (X^op) T (Opposite_Functor S) :=
  @Build_Adjunction A (X^op) T (Opposite_Functor S)
    (fun x a => @aol A X S T H x a)
    (fun x y z f g => @to_aol_nat_x   A X S T H y x z f g)
    (fun x y z f g => @to_aol_nat_a   A X S T H x y z g f)
    (fun x y z f g => @from_aol_nat_x A X S T H y x z f g)
    (fun x y z f g => @from_aol_nat_a A X S T H x y z g f).

Definition AdjointOnTheLeft_of_Adjunction
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : @Adjunction A (X^op) T (Opposite_Functor S)) :
  AdjointOnTheLeft S T :=
  @Build_AdjointOnTheLeft A X S T
    (fun x a => @adj A (X^op) T (Opposite_Functor S) H x a)
    (fun x a a2 f g => @to_adj_nat_r   A (X^op) T _ H x a a2 g f)
    (fun x x2 a f k => @to_adj_nat_l   A (X^op) T _ H x2 x a f k)
    (fun x a a2 p g => @from_adj_nat_r A (X^op) T _ H x a a2 g p)
    (fun x x2 a p k => @from_adj_nat_l A (X^op) T _ H x2 x a p k).

(* ---------------- round trips: all four at eq_refl ---------------- *)

Example aor_adjunction_round
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheRight S T) :
  AdjointOnTheRight_of_Adjunction (Adjunction_of_AdjointOnTheRight H) = H
  := eq_refl.

Example adjunction_aor_round
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : @Adjunction (A^op) X (Opposite_Functor T) S) :
  Adjunction_of_AdjointOnTheRight (AdjointOnTheRight_of_Adjunction H) = H
  := eq_refl.

Example aol_adjunction_round
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheLeft S T) :
  AdjointOnTheLeft_of_Adjunction (Adjunction_of_AdjointOnTheLeft H) = H
  := eq_refl.

Example adjunction_aol_round
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : @Adjunction A (X^op) T (Opposite_Functor S)) :
  Adjunction_of_AdjointOnTheLeft (AdjointOnTheLeft_of_Adjunction H) = H
  := eq_refl.

(* ---------------- symmetry ---------------- *)

Definition AdjointOnTheRight_sym
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheRight S T) : @AdjointOnTheRight X A T S :=
  @Build_AdjointOnTheRight X A T S
    (fun x a => iso_sym (@aor A X S T H a x))
    (fun x x2 a p k => @from_aor_nat_x A X S T H a x2 x p k)
    (fun x a a2 p g => @from_aor_nat_a A X S T H a2 a x p g)
    (fun x x2 a f k => @to_aor_nat_x   A X S T H a x2 x f k)
    (fun x a a2 f g => @to_aor_nat_a   A X S T H a2 a x f g).

Definition AdjointOnTheLeft_sym
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheLeft S T) : @AdjointOnTheLeft X A T S :=
  @Build_AdjointOnTheLeft X A T S
    (fun x a => iso_sym (@aol A X S T H a x))
    (fun x a a' f g => @from_aol_nat_x A X S T H a a' x f g)
    (fun x x' a f k => @from_aol_nat_a A X S T H a x x' f k)
    (fun x a a' p g => @to_aol_nat_x   A X S T H a a' x p g)
    (fun x x' a p k => @to_aol_nat_a   A X S T H a x x' p k).

Example aor_sym_invol {A X : Category} {S : (A^op) ⟶ X}
  {T : (X^op) ⟶ A} (H : AdjointOnTheRight S T) :
  AdjointOnTheRight_sym (AdjointOnTheRight_sym H) = H := eq_refl.

Example aol_sym_invol {A X : Category} {S : (A^op) ⟶ X}
  {T : (X^op) ⟶ A} (H : AdjointOnTheLeft S T) :
  AdjointOnTheLeft_sym (AdjointOnTheLeft_sym H) = H := eq_refl.

(* ---------------- the second orientation ---------------- *)

Definition Adjunction_of_AdjointOnTheRight'
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheRight S T) :
  @Adjunction (X^op) A (Opposite_Functor S) T :=
  @Build_Adjunction (X^op) A (Opposite_Functor S) T
    (fun a x => iso_sym (@aor A X S T H a x))
    (fun x y z f g => @from_aor_nat_a A X S T H y x z f g)
    (fun x y z f g => @from_aor_nat_x A X S T H x z y g f)
    (fun x y z f g => @to_aor_nat_a   A X S T H y x z f g)
    (fun x y z f g => @to_aor_nat_x   A X S T H x z y g f).

Definition AdjointOnTheRight_of_Adjunction'
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : @Adjunction (X^op) A (Opposite_Functor S) T) :
  AdjointOnTheRight S T :=
  @Build_AdjointOnTheRight A X S T
    (fun a x => iso_sym (@adj (X^op) A (Opposite_Functor S) T H a x))
    (fun a a2 x f g => @from_adj_nat_l (X^op) A _ T H a2 a x f g)
    (fun a x x2 f k => @from_adj_nat_r (X^op) A _ T H a x2 x k f)
    (fun a a2 x p g => @to_adj_nat_l   (X^op) A _ T H a2 a x p g)
    (fun a x x2 p k => @to_adj_nat_r   (X^op) A _ T H a x2 x k p).

Example aor_adjunction_round'
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheRight S T) :
  AdjointOnTheRight_of_Adjunction' (Adjunction_of_AdjointOnTheRight' H) = H
  := eq_refl.

Example adjunction_aor_round'
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : @Adjunction (X^op) A (Opposite_Functor S) T) :
  Adjunction_of_AdjointOnTheRight' (AdjointOnTheRight_of_Adjunction' H) = H
  := eq_refl.

Example sym_swaps_orientation {A X : Category} {S : (A^op) ⟶ X}
  {T : (X^op) ⟶ A} (H : AdjointOnTheRight S T) :
  Adjunction_of_AdjointOnTheRight (AdjointOnTheRight_sym H)
    = Adjunction_of_AdjointOnTheRight' H := eq_refl.

Example aor_second_orientation_is_opposite
  {A X : Category} {S : (A^op) ⟶ X} {T : (X^op) ⟶ A}
  (H : AdjointOnTheRight S T) :
  Adjunction_of_AdjointOnTheRight' H
    = Opposite_Adjunction _ _ (Adjunction_of_AdjointOnTheRight H) := eq_refl.

(* ---------------- two-sided dualization EXCHANGES ---------------- *)

Definition AdjointOnTheLeft_of_AdjointOnTheRight_op
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : @AdjointOnTheRight (A^op) (X^op)
         (Opposite_Functor S) (Opposite_Functor T)) :
  @AdjointOnTheLeft A X S T :=
  @Build_AdjointOnTheLeft A X S T
    (fun x a => @aor _ _ _ _ H a x)
    (fun x a a' f g => @to_aor_nat_a   _ _ _ _ H _ _ _ f g)
    (fun x x' a f k => @to_aor_nat_x   _ _ _ _ H _ _ _ f k)
    (fun x a a' p g => @from_aor_nat_a _ _ _ _ H _ _ _ p g)
    (fun x x' a p k => @from_aor_nat_x _ _ _ _ H _ _ _ p k).

Definition AdjointOnTheRight_op_of_AdjointOnTheLeft
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : @AdjointOnTheLeft A X S T) :
  @AdjointOnTheRight (A^op) (X^op)
    (Opposite_Functor S) (Opposite_Functor T) :=
  @Build_AdjointOnTheRight (A^op) (X^op)
    (Opposite_Functor S) (Opposite_Functor T)
    (fun a x => @aol _ _ _ _ H x a)
    (fun a a' x f g => @to_aol_nat_a   _ _ _ _ H _ _ _ f g)
    (fun a x x' f k => @to_aol_nat_x   _ _ _ _ H _ _ _ f k)
    (fun a a' x p g => @from_aol_nat_a _ _ _ _ H _ _ _ p g)
    (fun a x x' p k => @from_aol_nat_x _ _ _ _ H _ _ _ p k).

Example two_sided_round_left {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A) (H : @AdjointOnTheLeft A X S T) :
  AdjointOnTheLeft_of_AdjointOnTheRight_op S T
    (AdjointOnTheRight_op_of_AdjointOnTheLeft S T H) = H := eq_refl.

Example two_sided_round_right {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : @AdjointOnTheRight (A^op) (X^op)
         (Opposite_Functor S) (Opposite_Functor T)) :
  AdjointOnTheRight_op_of_AdjointOnTheLeft S T
    (AdjointOnTheLeft_of_AdjointOnTheRight_op S T H) = H := eq_refl.

Example ordinary_two_sided_collapses {C D : Category}
  (F : D ⟶ C) (U : C ⟶ D) :
  F ⊣ U -> Opposite_Functor U ⊣ Opposite_Functor F :=
  Opposite_Adjunction F U.

(* ---------------- both classes are inhabited ---------------- *)

(*
   本节说明伴随、函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition Id_AdjointOnTheRight (C : Category) :
  @AdjointOnTheRight C (C^op) (Id[C^op]) (Id[C]) :=
  {| aor := fun a x => iso_id |}.

Example id_aor_is_id (C : Category) (a x : C) (f : a ~{C}~> x) :
  to (@aor C (C^op) _ _ (Id_AdjointOnTheRight C) a x) f = f := eq_refl.

Program Definition Id_AdjointOnTheLeft (C : Category) :
  @AdjointOnTheLeft (C^op) C (Id[C]) (Id[C^op]) :=
  {| aol := fun x a => iso_id |}.

Example id_aol_is_id (C : Category) (x a : C) (f : a ~{C}~> x) :
  to (@aol (C^op) C _ _ (Id_AdjointOnTheLeft C) x a) f = f := eq_refl.

(* ---------------- Mac Lane's warning, witnessed ---------------- *)

Inductive Chain3 : Set := C3bot | C3mid | C3top.

Definition chain3_le (x y : Chain3) : Prop :=
  match x with
  | C3bot => True
  | C3mid => match y with C3bot => False | _ => True end
  | C3top => match y with C3top => True | _ => False end
  end.

Definition chain3_PreOrder : RelationClasses.PreOrder chain3_le.
Proof.
  constructor.
  - intro x; destruct x; exact I.
  - intros x y z Hxy Hyz; destruct x, y, z; simpl in *; tauto.
Defined.

Definition Chain3Cat : Category := Proset chain3_PreOrder.

Definition chain3_s (a : Chain3) : Chain3 :=
  match a with C3bot => C3top | C3mid => C3top | C3top => C3bot end.

Definition chain3_t (x : Chain3) : Chain3 :=
  match x with C3bot => C3top | C3mid => C3mid | C3top => C3mid end.

Lemma chain3_s_anti (x y : Chain3) :
  chain3_le y x -> chain3_le (chain3_s x) (chain3_s y).
Proof. destruct x, y; simpl; tauto. Qed.

Lemma chain3_t_anti (x y : Chain3) :
  chain3_le y x -> chain3_le (chain3_t x) (chain3_t y).
Proof. destruct x, y; simpl; tauto. Qed.

Lemma chain3_galois_to (a x : Chain3) :
  chain3_le a (chain3_t x) -> chain3_le x (chain3_s a).
Proof. destruct a, x; simpl; tauto. Qed.

Lemma chain3_galois_from (a x : Chain3) :
  chain3_le x (chain3_s a) -> chain3_le a (chain3_t x).
Proof. destruct a, x; simpl; tauto. Qed.

#[local] Obligation Tactic := simpl; repeat intro; exact I.

Program Definition chain3_S : Chain3Cat^op ⟶ Chain3Cat := {|
  fobj := chain3_s;
  fmap := fun x y f => chain3_s_anti x y f
|}.

Program Definition chain3_T : Chain3Cat^op ⟶ Chain3Cat := {|
  fobj := chain3_t;
  fmap := fun x y f => chain3_t_anti x y f
|}.

Program Definition Chain3_AdjointOnTheRight :
  AdjointOnTheRight chain3_S chain3_T := {|
  aor := fun a x =>
    {| to   := {| morphism := chain3_galois_to a x |}
     ; from := {| morphism := chain3_galois_from a x |} |}
|}.

Theorem Chain3_not_AdjointOnTheLeft :
  AdjointOnTheLeft chain3_S chain3_T -> False.
Proof.
  intro H.
  exact (@to Sets _ _ (@aol _ _ _ _ H C3mid C3mid) (@id Chain3Cat C3mid)).
Qed.

Theorem right_does_not_imply_left :
  (forall (A X : Category) (S : (A^op) ⟶ X) (T : (X^op) ⟶ A),
      AdjointOnTheRight S T -> AdjointOnTheLeft S T) -> False.
Proof.
  intro H.
  exact (Chain3_not_AdjointOnTheLeft
           (H Chain3Cat Chain3Cat chain3_S chain3_T
              Chain3_AdjointOnTheRight)).
Qed.

Example chain3_s_not_monotone :
  chain3_le C3mid C3top /\ (chain3_le (chain3_s C3mid) (chain3_s C3top)
                              -> False).
Proof. split; simpl; tauto. Qed.

Example chain3_t_not_monotone :
  chain3_le C3bot C3mid /\ (chain3_le (chain3_t C3bot) (chain3_t C3mid)
                              -> False).
Proof. split; simpl; tauto. Qed.

Example chain3_s_not_constant :
  chain3_s C3bot = C3top /\ chain3_s C3top = C3bot.
Proof. split; reflexivity. Qed.

Example chain3_t_not_constant :
  chain3_t C3bot = C3top /\ chain3_t C3top = C3mid.
Proof. split; reflexivity. Qed.

Example chain3_S_neq_T : chain3_s C3mid = C3top /\ chain3_t C3mid = C3mid.
Proof. split; reflexivity. Qed.

(* ---------------- Mac Lane's own example: the power set ------------ *)

Definition aor_pflip@{o} {a x : SetoidObject@{o o}}
  (f : SetoidMorphism@{o o o} a (Powerset_Prop_obj@{o} x)) :
  SetoidMorphism@{o o o} x (Powerset_Prop_obj@{o} a).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (carrier x) (is_setoid x)
       (carrier (Powerset_Prop_obj@{o} a))
       (is_setoid (Powerset_Prop_obj@{o} a))
       (fun e => @Build_SetoidMorphism@{o o o}
                   (carrier a) (is_setoid a) Prop
                   (is_setoid Powerset_Prop_truth@{o})
                   (fun v => f v e) _) _).
  - intros v v' Hv; exact (proper_morphism f v v' Hv e).
  - intros e e' He v; exact (proper_morphism (f v) e e' He).
Defined.

#[local] Obligation Tactic := idtac.

Program Definition Powerset_AdjointOnTheRight@{o so} :
  @AdjointOnTheRight Sets@{o so} Sets@{o so}
    Powerset_Prop_op@{o so} Powerset_Prop_op@{o so} := {|
  aor := fun a x =>
    {| to   := {| morphism := fun f => aor_pflip@{o} f |}
     ; from := {| morphism := fun f => aor_pflip@{o} f |} |}
|}.
Next Obligation. intros a x f g H e v; exact (H v e). Qed.
Next Obligation. intros a x f g H e v; exact (H v e). Qed.
Next Obligation. repeat intro; reflexivity. Qed.
Next Obligation. repeat intro; reflexivity. Qed.
Next Obligation. repeat intro; reflexivity. Qed.
Next Obligation. repeat intro; reflexivity. Qed.
Next Obligation. repeat intro; reflexivity. Qed.
Next Obligation. repeat intro; reflexivity. Qed.

Example powerset_aor_is_flip@{o so} (a x : SetoidObject@{o o})
  (f : a ~{Sets@{o so}}~> Powerset_Prop_obj@{o} x)
  (e : carrier x) (v : carrier a) :
  @to Sets@{o so} _ _
     (@aor _ _ _ _ Powerset_AdjointOnTheRight@{o so} a x) f e v = f v e
  := eq_refl.

Definition aor_SetsEmpty@{o} : SetoidObject@{o o} :=
  {| carrier := False ; is_setoid := False_Setoid@{o} |}.

Definition aor_const_true@{o} (Z : SetoidObject@{o o}) :
  SetoidMorphism@{o o o} Z Powerset_Prop_truth@{o}.
Proof.
  unshelve refine (@Build_SetoidMorphism@{o o o} (carrier Z) (is_setoid Z)
    Prop (is_setoid Powerset_Prop_truth@{o}) (fun _ => True) _).
  intros z z' _; split; intro; exact I.
Defined.

Definition aor_const_false@{o} (Z : SetoidObject@{o o}) :
  SetoidMorphism@{o o o} Z Powerset_Prop_truth@{o}.
Proof.
  unshelve refine (@Build_SetoidMorphism@{o o o} (carrier Z) (is_setoid Z)
    Prop (is_setoid Powerset_Prop_truth@{o}) (fun _ => False) _).
  intros z z' _; split; intro K; destruct K.
Defined.

Theorem Powerset_not_AdjointOnTheLeft@{o so} :
  @AdjointOnTheLeft Sets@{o so} Sets@{o so}
     Powerset_Prop_op@{o so} Powerset_Prop_op@{o so} -> False.
Proof.
  intro H.
  exact (@to Sets@{o so} _ _
           (@aol _ _ _ _ H aor_SetsEmpty@{o} Powerset_Omega@{o})
           (aor_const_true@{o} (Powerset_Prop_obj@{o} aor_SetsEmpty@{o}))
           (@setoid_morphism_id@{o o o} Powerset_Omega@{o})).
Qed.

Theorem right_does_not_imply_left_in_Sets :
  (forall (A X : Category) (S : (A^op) ⟶ X) (T : (X^op) ⟶ A),
      AdjointOnTheRight S T -> AdjointOnTheLeft S T) -> False.
Proof.
  intro H.
  exact (Powerset_not_AdjointOnTheLeft
           (H Sets Sets Powerset_Prop_op Powerset_Prop_op
              Powerset_AdjointOnTheRight)).
Qed.

Example powerset_Omega_two_subsets@{o} :
  (@equiv _ (is_setoid (Powerset_Prop_obj@{o} Powerset_Omega@{o}))
     (aor_const_true@{o} Powerset_Omega@{o})
     (aor_const_false@{o} Powerset_Omega@{o})) -> False.
Proof. intro H; exact (proj1 (H True) I). Qed.

(* ---------------- Riehl §4.4: the unit/counit presentations -------- *)

Section MutualTransforms.
Context {A X : Category}.
Context {S : (A^op) ⟶ X}.
Context {T : (X^op) ⟶ A}.

Class MutuallyRightAdjoint := {
  runit  : Id[X] ⟹ S ◯ Opposite_Functor T;
  runit' : Id[A] ⟹ T ◯ Opposite_Functor S;

  right_triangle_S {a : A} :
    fmap[S] (transform[runit'] a) ∘ transform[runit] (S a) ≈ id;
  right_triangle_T {x : X} :
    fmap[T] (transform[runit] x) ∘ transform[runit'] (T x) ≈ id
}.

Class MutuallyLeftAdjoint := {
  lcounit  : S ◯ Opposite_Functor T ⟹ Id[X];
  lcounit' : T ◯ Opposite_Functor S ⟹ Id[A];

  left_triangle_S {a : A} :
    transform[lcounit] (S a) ∘ fmap[S] (transform[lcounit'] a) ≈ id;
  left_triangle_T {x : X} :
    transform[lcounit'] (T x) ∘ fmap[T] (transform[lcounit] x) ≈ id
}.

End MutualTransforms.

Arguments MutuallyRightAdjoint {A X} S T.
Arguments MutuallyLeftAdjoint {A X} S T.

Definition aor_transform_counit {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (n : Id[A] ⟹ T ◯ Opposite_Functor S) :
  (Opposite_Functor T ◯ S) ⟹ Id[A^op] :=
  @Build_Transform (A^op) (A^op) (Opposite_Functor T ◯ S) (Id[A^op])
    (fun a => transform[n] a)
    (fun a a' f => @naturality_sym _ _ _ _ n a' a f)
    (fun a a' f => @naturality     _ _ _ _ n a' a f).

Definition aor_counit_transform {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (n : (Opposite_Functor T ◯ S) ⟹ Id[A^op]) :
  Id[A] ⟹ T ◯ Opposite_Functor S :=
  @Build_Transform A A (Id[A]) (T ◯ Opposite_Functor S)
    (fun a => transform[n] a)
    (fun a a' f => @naturality_sym _ _ _ _ n a' a f)
    (fun a a' f => @naturality     _ _ _ _ n a' a f).

Example aor_transform_counit_round {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (n : Id[A] ⟹ T ◯ Opposite_Functor S) :
  aor_counit_transform S T (aor_transform_counit S T n) = n := eq_refl.

Definition Adjunction_Transform_of_MutuallyRightAdjoint
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : MutuallyRightAdjoint S T) :
  @Adjunction_Transform (A^op) X (Opposite_Functor T) S :=
  @Build_Adjunction_Transform (A^op) X (Opposite_Functor T) S
    (@runit _ _ _ _ H)
    (aor_transform_counit S T (@runit' _ _ _ _ H))
    (fun x => @right_triangle_T _ _ _ _ H x)
    (fun a => @right_triangle_S _ _ _ _ H a).

Definition MutuallyRightAdjoint_of_Adjunction_Transform
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : @Adjunction_Transform (A^op) X (Opposite_Functor T) S) :
  MutuallyRightAdjoint S T :=
  @Build_MutuallyRightAdjoint A X S T
    (@unit _ _ _ _ H)
    (aor_counit_transform S T (@counit _ _ _ _ H))
    (fun a => @fmap_counit_unit _ _ _ _ H a)
    (fun x => @counit_fmap_unit _ _ _ _ H x).

Example MRA_transform_round {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A) (H : MutuallyRightAdjoint S T) :
  MutuallyRightAdjoint_of_Adjunction_Transform S T
    (Adjunction_Transform_of_MutuallyRightAdjoint S T H) = H := eq_refl.

Example transform_MRA_round {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : @Adjunction_Transform (A^op) X (Opposite_Functor T) S) :
  Adjunction_Transform_of_MutuallyRightAdjoint S T
    (MutuallyRightAdjoint_of_Adjunction_Transform S T H) = H := eq_refl.

Definition AdjointOnTheRight_of_MutuallyRightAdjoint
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : MutuallyRightAdjoint S T) : AdjointOnTheRight S T :=
  AdjointOnTheRight_of_Adjunction
    (@Adjunction_from_Transform (A^op) X (Opposite_Functor T) S
       (Adjunction_Transform_of_MutuallyRightAdjoint S T H)).

Definition MutuallyRightAdjoint_of_AdjointOnTheRight
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : AdjointOnTheRight S T) : MutuallyRightAdjoint S T :=
  MutuallyRightAdjoint_of_Adjunction_Transform S T
    (@Adjunction_to_Transform (A^op) X (Opposite_Functor T) S
       (Adjunction_of_AdjointOnTheRight H)).

Definition aol_transform_unit {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (n : S ◯ Opposite_Functor T ⟹ Id[X]) :
  Id[X^op] ⟹ Opposite_Functor S ◯ T :=
  @Build_Transform (X^op) (X^op) (Id[X^op]) (Opposite_Functor S ◯ T)
    (fun x => transform[n] x)
    (fun x x' f => @naturality_sym _ _ _ _ n x' x f)
    (fun x x' f => @naturality     _ _ _ _ n x' x f).

Definition aol_unit_transform {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (n : Id[X^op] ⟹ Opposite_Functor S ◯ T) :
  S ◯ Opposite_Functor T ⟹ Id[X] :=
  @Build_Transform X X (S ◯ Opposite_Functor T) (Id[X])
    (fun x => transform[n] x)
    (fun x x' f => @naturality_sym _ _ _ _ n x' x f)
    (fun x x' f => @naturality     _ _ _ _ n x' x f).

Definition Adjunction_Transform_of_MutuallyLeftAdjoint
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : MutuallyLeftAdjoint S T) :
  @Adjunction_Transform A (X^op) T (Opposite_Functor S) :=
  @Build_Adjunction_Transform A (X^op) T (Opposite_Functor S)
    (aol_transform_unit S T (@lcounit _ _ _ _ H))
    (@lcounit' _ _ _ _ H)
    (fun x => @left_triangle_T _ _ _ _ H x)
    (fun a => @left_triangle_S _ _ _ _ H a).

Definition MutuallyLeftAdjoint_of_Adjunction_Transform
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : @Adjunction_Transform A (X^op) T (Opposite_Functor S)) :
  MutuallyLeftAdjoint S T :=
  @Build_MutuallyLeftAdjoint A X S T
    (aol_unit_transform S T (@unit _ _ _ _ H))
    (@counit _ _ _ _ H)
    (fun a => @fmap_counit_unit _ _ _ _ H a)
    (fun x => @counit_fmap_unit _ _ _ _ H x).

Example MLA_transform_round {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A) (H : MutuallyLeftAdjoint S T) :
  MutuallyLeftAdjoint_of_Adjunction_Transform S T
    (Adjunction_Transform_of_MutuallyLeftAdjoint S T H) = H := eq_refl.

Definition AdjointOnTheLeft_of_MutuallyLeftAdjoint
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : MutuallyLeftAdjoint S T) : AdjointOnTheLeft S T :=
  AdjointOnTheLeft_of_Adjunction
    (@Adjunction_from_Transform A (X^op) T (Opposite_Functor S)
       (Adjunction_Transform_of_MutuallyLeftAdjoint S T H)).

Definition MutuallyLeftAdjoint_of_AdjointOnTheLeft
  {A X : Category} (S : (A^op) ⟶ X) (T : (X^op) ⟶ A)
  (H : AdjointOnTheLeft S T) : MutuallyLeftAdjoint S T :=
  MutuallyLeftAdjoint_of_Adjunction_Transform S T
    (@Adjunction_to_Transform A (X^op) T (Opposite_Functor S)
       (Adjunction_of_AdjointOnTheLeft H)).

(* ---------------- strict-first readbacks ---------------- *)

Example runit_is_transpose_of_id {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A) (H : AdjointOnTheRight S T) (x : X) :
  transform[@runit _ _ _ _ (MutuallyRightAdjoint_of_AdjointOnTheRight S T H)] x
    = @to Sets _ _ (@aor _ _ _ _ H (T x) x) (id[T x]) := eq_refl.

Example runit'_is_transpose_of_id {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A) (H : AdjointOnTheRight S T) (a : A) :
  transform[@runit' _ _ _ _ (MutuallyRightAdjoint_of_AdjointOnTheRight S T H)] a
    = @from Sets _ _ (@aor _ _ _ _ H a (S a)) (id[S a]) := eq_refl.

Example aor_of_MRA_computes {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A) (H : MutuallyRightAdjoint S T)
  (a : A) (x : X) (g : a ~{A}~> T x) :
  @to Sets _ _
     (@aor _ _ _ _ (AdjointOnTheRight_of_MutuallyRightAdjoint S T H) a x) g
    = fmap[S] g ∘ transform[@runit _ _ _ _ H] x := eq_refl.

Example lcounit_is_transpose_of_id {A X : Category}
  (S : (A^op) ⟶ X) (T : (X^op) ⟶ A) (H : AdjointOnTheLeft S T) (x : X) :
  transform[@lcounit _ _ _ _ (MutuallyLeftAdjoint_of_AdjointOnTheLeft S T H)] x
    = @to Sets _ _ (@aol _ _ _ _ H x (T x)) (id[T x]) := eq_refl.


(* ---------------- probes ---------------- *)

(*
   本节说明伴随、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Probes.
Context {A X : Category}.
Context {S : (A^op) ⟶ X}.
Context {T : (X^op) ⟶ A}.

(*
   本节说明 Right 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Check (AdjointOnTheRight S T).
Check (AdjointOnTheLeft S T).
Check (@Adjunction (A^op) X (Opposite_Functor T) S).
Check @AdjointOnTheRight_of_Adjunction.
Check @Adjunction_of_AdjointOnTheRight.
Check (MutuallyRightAdjoint S T).
Check (fun H : AdjointOnTheRight S T =>
         MutuallyRightAdjoint_of_AdjointOnTheRight S T H).
Check (fun H : MutuallyRightAdjoint S T =>
         AdjointOnTheRight_of_MutuallyRightAdjoint S T H).

Fail Definition probe_not_an_abbreviation
  (H : @Adjunction (A^op) X (Opposite_Functor T) S) :
  AdjointOnTheRight S T := H.

Fail Definition probe_not_an_abbreviation_rev
  (H : AdjointOnTheRight S T) :
  @Adjunction (A^op) X (Opposite_Functor T) S := H.

Fail Definition probe_right_is_not_left (H : AdjointOnTheRight S T) :
  AdjointOnTheLeft S T := H.

Fail Example probe_MRA_round_strict (H : MutuallyRightAdjoint S T) :
  MutuallyRightAdjoint_of_AdjointOnTheRight S T
    (AdjointOnTheRight_of_MutuallyRightAdjoint S T H) = H := eq_refl.

Fail Example probe_aor_MRA_round_strict (H : AdjointOnTheRight S T) :
  AdjointOnTheRight_of_MutuallyRightAdjoint S T
    (MutuallyRightAdjoint_of_AdjointOnTheRight S T H) = H := eq_refl.

End Probes.

(*
   本节说明 Right 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example probe_358_instrument : (true = false) := eq_refl.

(* Negatives 6-7: hom = proof has TWO INDEPENDENT donors.  Section-local
   [Universes]/[Constraint] declarations are measured not to leak (the
   Instance/Fun/Group.v precedent). *)
Section ProbeHomProof.
Universes uo uh up.
Constraint uh < up.
Context (C : Category@{uo uh up}).
Context (x y : C).

Check (x ~{C}~> y).
Check (id[x]).

Fail Check (Opposite C).

Fail Check ({| carrier := @hom C x y; is_setoid := @homset C x y |}
            : obj[Sets]).

End ProbeHomProof.

(* Negatives 8-9: A's hom = X's hom likewise has TWO INDEPENDENT donors
   -- the contravariant PAIR itself, and [Sets] with no functor in the
   command at all. *)
Section ProbeCrossHom.
Universes ao ah ap xo xh xp.
Constraint ah < xh.
Context (A2 : Category@{ao ah ap}).
Context (X2 : Category@{xo xh xp}).
Context (a2 b2 : A2).
Context (x2 y2 : X2).

Check ((A2^op) ⟶ X2).
Check (a2 ~{A2}~> b2).
Check (x2 ~{X2}~> y2).

Fail Check ((X2^op) ⟶ A2).

Fail Check (@Isomorphism Sets
   {| carrier := @hom A2 a2 b2; is_setoid := @homset A2 a2 b2 |}
   {| carrier := @hom X2 x2 y2; is_setoid := @homset X2 x2 y2 |}).

End ProbeCrossHom.
