(* * * Functor 范畴 over discrete shapes （已译） *)

Require Import Coq.Vectors.Fin.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Cartesian.
Require Import Category.Instance.One.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Discrete.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
 Book:      Fong & Spivak, "Seven Sketches in Compositionality" (CUP,
 nLab:      https://ncatlab.org/nlab/show/functor+category
 Wikipedia: https://en.wikipedia.org/wiki/Functor_category

   本文件给出离散范畴实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Discrete_Transform {A : Type} {B : Category}
        {F G : DiscreteCat A ⟶ B} (η : ∀ a : A, F a ~> G a) : F ⟹ G := {|
  transform := η
|}.
Next Obligation.
  intros A B F G η x y e; destruct e; simpl.
  assert (HF : fmap[F] (@eq_refl _ x) ≈ id) by apply (@fmap_id _ _ F x).
  assert (HG : fmap[G] (@eq_refl _ x) ≈ id) by apply (@fmap_id _ _ G x).
  rewrite HF, HG; cat.
Qed.
Next Obligation.
  intros A B F G η x y e; destruct e; simpl.
  assert (HF : fmap[F] (@eq_refl _ x) ≈ id) by apply (@fmap_id _ _ F x).
  assert (HG : fmap[G] (@eq_refl _ x) ≈ id) by apply (@fmap_id _ _ G x).
  rewrite HF, HG; cat.
Qed.

(*
   本节说明hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Discrete_hom_iso {A : Type} {B : Category}
        (F G : DiscreteCat A ⟶ B) :
  ({| carrier := F ⟹ G;
      is_setoid := @Transform_Setoid (DiscreteCat A) B F G |} : SetoidObject)
    ≅[Sets]
  {| carrier := ∀ a : A, F a ~> G a;
     is_setoid := {| equiv := fun η θ => ∀ a : A, η a ≈ θ a |} |} := {|
  to   := {| morphism := fun η a => η a |};
  from := {| morphism := fun η => Discrete_Transform η |}
|}.
Next Obligation.
  intros A B F G; constructor.
  - intros η a; reflexivity.
  - intros η θ Hηθ a; symmetry; exact (Hηθ a).
  - intros η θ ρ H1 H2 a; transitivity (θ a); [ exact (H1 a) | exact (H2 a) ].
Qed.
Next Obligation.
  intros A B F G η θ Hηθ a; exact (Hηθ a).
Qed.
Next Obligation.
  intros A B F G η θ Hηθ a; exact (Hηθ a).
Qed.
Next Obligation.
  intros A B F G η a; reflexivity.
Qed.
Next Obligation.
  intros A B F G η a; reflexivity.
Qed.

(* * ** The 函子 范畴 over discrete shape indexed product （已译） *)

Program Definition Fun_Discrete_to {A : Type} {B : Category} :
  [DiscreteCat A, B] ⟶ PiCat (fun _ : A => B) := {|
  fobj := fun F a => F a;
  fmap := fun F G η a => η a
|}.
Next Obligation.
  intros A B F G η θ Hηθ a; exact (Hηθ a).
Qed.
Next Obligation.
  (* the Fun identity's component at a is [fmap[F] eq_refl] *)
  intros A B F a; exact (@fmap_id _ _ F a).
Qed.
Next Obligation.
  intros A B F G H η θ a; reflexivity.
Qed.

Program Definition Fun_Discrete_from {A : Type} {B : Category} :
  PiCat (fun _ : A => B) ⟶ [DiscreteCat A, B] := {|
  fobj := fun f => DiscreteCat_Functor f;
  fmap := fun f g η => Discrete_Transform (F:=DiscreteCat_Functor f)
                                          (G:=DiscreteCat_Functor g) η
|}.
Next Obligation.
  intros A B f g η θ Hηθ a; exact (Hηθ a).
Qed.
Next Obligation.
  intros A B f a; reflexivity.
Qed.
Next Obligation.
  intros A B f g h η θ a; reflexivity.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition DiscreteCat_Functor_iso {A : Type} {B : Category}
        (F : DiscreteCat A ⟶ B) :
  @Isomorphism ([DiscreteCat A, B]) (DiscreteCat_Functor (fobj[F])) F := {|
  to   := Discrete_Transform (F:=DiscreteCat_Functor (fobj[F])) (G:=F)
                             (fun a => id);
  from := Discrete_Transform (F:=F) (G:=DiscreteCat_Functor (fobj[F]))
                             (fun a => id)
|}.
Next Obligation.
  intros A B F a; simpl; cat.
Qed.
Next Obligation.
  intros A B F a; simpl; cat.
Qed.

Program Definition Fun_Discrete_PiCat {A : Type} {B : Category} :
  [DiscreteCat A, B] ≅[Cat] PiCat (fun _ : A => B) := {|
  to   := Fun_Discrete_to;
  from := Fun_Discrete_from
|}.
Next Obligation.
  intros A B.
  exists (fun f => iso_id).
  intros f g η a; simpl; cat.
Qed.
Next Obligation.
  intros A B.
  exists (fun F => DiscreteCat_Functor_iso F).
  intros F G η x; simpl; cat.
Qed.

(** ** Finite powers *)

(* The n-fold power 范畴, iterated binary product the
 terminal 范畴 empty product. （已译） *)
Fixpoint Pow (B : Category) (n : nat) : Category :=
  match n with
  | O => _1
  | S m => B ∏ Pow B m
  end.

(* [Cartesian]'s [second] calculus makes [z × −] carry isomorphisms; at
 [Cat] transports induction 假设 across [B ∏ −]. （已译） *)
Program Definition second_iso {C : Category} `{@Cartesian C}
        {z x y : C} (f : x ≅ y) : z × x ≅ z × y := {|
  to   := second (to f);
  from := second (from f)
|}.
Next Obligation.
  intros C H z x y f.
  rewrite <- second_comp.
  rewrite iso_to_from.
  apply second_id.
Qed.
Next Obligation.
  intros C H z x y f.
  rewrite <- second_comp.
  rewrite iso_from_to.
  apply second_id.
Qed.

(* 相关说明。 （已译） *)
Program Definition PiCat_Fin_zero_component (B : Category)
        (f : obj[PiCat (fun _ : Fin.t 0 => B)]) :
  @Isomorphism (PiCat (fun _ : Fin.t 0 => B))
               (fun i => Fin.case0 (fun _ => B) i) f := {|
  to   := fun i =>
    Fin.case0 (fun i' => Fin.case0 (fun _ => B) i' ~> f i') i;
  from := fun i =>
    Fin.case0 (fun i' => f i' ~> Fin.case0 (fun _ => B) i') i
|}.
Next Obligation.
  intros B f i; inversion i.
Qed.
Next Obligation.
  intros B f i; inversion i.
Qed.

(* 相关说明。 （已译） *)
Program Definition PiCat_Fin_zero (B : Category) :
  PiCat (fun _ : Fin.t 0 => B) ≅[Cat] _1 := {|
  to   := Erase _;
  from := {| fobj := fun _ i => Fin.case0 (fun _ => B) i;
             fmap := fun _ _ _ i =>
               Fin.case0 (fun i' => Fin.case0 (fun _ => B) i'
                                      ~> Fin.case0 (fun _ => B) i') i |}
|}.
Next Obligation.
  intros B x i; inversion i.
Qed.
Next Obligation.
  intros B x y z f g i; inversion i.
Qed.
Next Obligation.
  intros B.
  unshelve eexists.
  - intro x; destruct x; exact iso_id.
  - intros x y f; destruct x, y, f; simpl; reflexivity.
Qed.
Next Obligation.
  intros B.
  exists (fun f => PiCat_Fin_zero_component B f).
  intros f g η i; inversion i.
Qed.

(* Splitting pair components repairing 恒等 up
 恒等-component 同构 (pair eta not definitional). （已译） *)
Program Definition PiCat_Fin_succ_component (B : Category) (n : nat)
        (p : obj[B ∏ PiCat (fun _ : Fin.t n => B)]) :
  @Isomorphism (B ∏ PiCat (fun _ : Fin.t n => B))
               (fst p, fun i => snd p i) p := {|
  to   := (id, fun i => id);
  from := (id, fun i => id)
|}.
Next Obligation.
  intros B n p; split; [ simpl; cat | intro i; simpl; cat ].
Qed.
Next Obligation.
  intros B n p; split; [ simpl; cat | intro i; simpl; cat ].
Qed.

(* Rebuilding choice function [Fin.t (S n)] head tail
 恒等 componentwise. （已译） *)
Program Definition PiCat_Fin_succ_rebuild (B : Category) (n : nat)
        (f : obj[PiCat (fun _ : Fin.t (S n) => B)]) :
  @Isomorphism (PiCat (fun _ : Fin.t (S n) => B))
               (fun i => Fin.caseS' i (fun _ => B) (f Fin.F1)
                           (fun j => f (Fin.FS j))) f := {|
  to   := fun i => Fin.caseS' i
            (fun i' => Fin.caseS' i' (fun _ => B) (f Fin.F1)
                         (fun j => f (Fin.FS j)) ~> f i')
            id (fun j => id);
  from := fun i => Fin.caseS' i
            (fun i' => f i' ~> Fin.caseS' i' (fun _ => B) (f Fin.F1)
                                (fun j => f (Fin.FS j)))
            id (fun j => id)
|}.
Next Obligation.
  intros B n f i.
  pattern i; apply (Fin.caseS' i); simpl.
  - cat.
  - intro j; cat.
Qed.
Next Obligation.
  intros B n f i.
  pattern i; apply (Fin.caseS' i); simpl.
  - cat.
  - intro j; cat.
Qed.

(* Peeling one component off a finite power. *)
Program Definition PiCat_Fin_succ (B : Category) (n : nat) :
  PiCat (fun _ : Fin.t (S n) => B) ≅[Cat]
  B ∏ PiCat (fun _ : Fin.t n => B) := {|
  to   := {| fobj := fun f => (f Fin.F1, fun i => f (Fin.FS i));
             fmap := fun f g η => (η Fin.F1, fun i => η (Fin.FS i)) |};
  from := {| fobj := fun p i => Fin.caseS' i (fun _ => B) (fst p) (snd p);
             fmap := fun p q h i =>
               Fin.caseS' i (fun i' =>
                 Fin.caseS' i' (fun _ => B) (fst p) (snd p)
                   ~> Fin.caseS' i' (fun _ => B) (fst q) (snd q))
                 (fst h) (fun j => snd h j) |}
|}.
Next Obligation.
  intros B n f g η θ Hηθ; split.
  - exact (Hηθ Fin.F1).
  - intro i; exact (Hηθ (Fin.FS i)).
Qed.
Next Obligation.
  intros B n f; split; [ reflexivity | intro i; reflexivity ].
Qed.
Next Obligation.
  intros B n f g h η θ; split; [ reflexivity | intro i; reflexivity ].
Qed.
Next Obligation.
  intros B n p q h h' Hh i.
  pattern i; apply (Fin.caseS' i); simpl.
  - exact (fst Hh).
  - intro j; exact (snd Hh j).
Qed.
Next Obligation.
  intros B n p i.
  pattern i; apply (Fin.caseS' i); simpl.
  - reflexivity.
  - intro j; reflexivity.
Qed.
Next Obligation.
  intros B n p q r h h' i.
  pattern i; apply (Fin.caseS' i); simpl.
  - reflexivity.
  - intro j; reflexivity.
Qed.
Next Obligation.
  intros B n.
  exists (fun p => PiCat_Fin_succ_component B n p).
  intros p q h; split.
  - simpl; cat.
  - intro i; simpl; cat.
Qed.
Next Obligation.
  intros B n.
  exists (fun f => PiCat_Fin_succ_rebuild B n f).
  intros f g η i; simpl.
  pattern i; apply (Fin.caseS' i); simpl.
  - cat.
  - intro j; cat.
Qed.

(* 相关说明。 （已译） *)
Fixpoint PiCat_Fin_power (B : Category) (n : nat) :
  PiCat (fun _ : Fin.t n => B) ≅[Cat] Pow B n :=
  match n with
  | O => PiCat_Fin_zero B
  | S m => iso_compose (second_iso (PiCat_Fin_power B m)) (PiCat_Fin_succ B m)
  end.

(* Mac Lane Exercise II.4.2: finite discrete shape, 函子
 范畴 finite power target. （已译） *)
Definition Fun_Discrete_power (B : Category) (n : nat) :
  [DiscreteCat (Fin.t n), B] ≅[Cat] Pow B n :=
  iso_compose (PiCat_Fin_power B n) Fun_Discrete_PiCat.

(* 相关说明。 （已译） *)
Example Fun_Discrete_power_two (B : Category) :
  [DiscreteCat (Fin.t 2), B] ≅[Cat] B ∏ (B ∏ _1) :=
  Fun_Discrete_power B 2.

(* 相关说明。 （已译） *)
Example Fun_Discrete_power_two_flat (B : Category) :
  [DiscreteCat (Fin.t 2), B] ≅[Cat] B ∏ B :=
  iso_compose (second_iso prod_one_r) (Fun_Discrete_power B 2).

(** ** The power-set computation *)

(* An equality of objects of a discrete category, as an isomorphism. *)
Program Definition Discrete_iso_of_eq {A : Type} {x y : A} (e : x = y) :
  @Isomorphism (DiscreteCat A) x y := {|
  to := e; from := eq_sym e
|}.
Next Obligation.
  intros A x y e; destruct e; reflexivity.
Qed.
Next Obligation.
  intros A x y e; destruct e; reflexivity.
Qed.

(* The setoid 对象 函子 范畴 — 函子 up the
 ambient natural 同构 — packaged 对象 Sets. （已译） *)
Definition Fun_objects_setoid (C D : Category) : SetoidObject := {|
  carrier := C ⟶ D;
  is_setoid := @Functor_Setoid C D
|}.

(* Characteristic functions X → bool under pointwise equality. *)
Program Definition CharFun_setoid (X : Type) : SetoidObject := {|
  carrier := X → bool;
  is_setoid := {| equiv := fun f g => ∀ x : X, f x = g x |}
|}.
Next Obligation.
  intro X; equivalence.
  now rewrite H, H0.
Qed.

(*
   本节说明函子、等价、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Fun_Discrete_bool_subsets (X : Type) :
  Fun_objects_setoid (DiscreteCat X) (DiscreteCat bool) ≅[Sets]
  CharFun_setoid X := {|
  to   := {| morphism := fun F x => F x |};
  from := {| morphism := fun f : X → bool =>
               @DiscreteCat_Functor X (DiscreteCat bool) f |}
|}.
Next Obligation.
  intros X F G HFG x.
  exact (to (`1 HFG x)).
Qed.
Next Obligation.
  intros X f g Hfg.
  exists (fun x => Discrete_iso_of_eq (Hfg x)).
  intros x y e; destruct e; simpl.
  now destruct (Hfg x).
Qed.
Next Obligation.
  intros X f x; reflexivity.
Qed.
Next Obligation.
  intros X F.
  exists (fun x => iso_id).
  intros x y e; destruct e; simpl.
  assert (E : fmap[F] (@eq_refl X x) = @eq_refl bool (F x))
    by apply (@fmap_id _ _ F x).
  rewrite E; reflexivity.
Qed.

(** ** The diagonal argument *)

(*
   本节说明 Discrete 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem cantor_predicates {A : Type} (f : A → A → Prop) :
  ¬ (∀ P : A → Prop, ∃ a : A, ∀ x : A, f a x ↔ P x).
Proof.
  intro H.
  destruct (H (fun x => ¬ f x x)) as [a Ha].
  specialize (Ha a).
  destruct Ha as [Hto Hfrom].
  assert (Hn : ¬ f a a) by (intro h; exact (Hto h h)).
  exact (Hn (Hfrom Hn)).
Qed.

(* 相关说明。 （已译） *)
Theorem cantor_bool {A : Type} (f : A → A → bool) :
  ¬ (∀ g : A → bool, ∃ a : A, ∀ x : A, f a x = g x).
Proof.
  intro H.
  destruct (H (fun x => negb (f x x))) as [a Ha].
  specialize (Ha a).
  destruct (f a a); discriminate.
Qed.

(*
   本节说明函子、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Fun_Discrete_no_surjection {X : Type}
        (Φ : X → (DiscreteCat X ⟶ DiscreteCat bool)) :
  ¬ (∀ G : DiscreteCat X ⟶ DiscreteCat bool,
       ∃ a : X, Φ a ≈ G).
Proof.
  intro H.
  apply (cantor_bool (fun a x => Φ a x)).
  intro g.
  destruct (H (@DiscreteCat_Functor X (DiscreteCat bool) g)) as [a Ha].
  exists a.
  intro x.
  exact (to (`1 Ha x)).
Qed.

(* * ** The 态射 half [1, B] ≅ B (Seven Sketches, Example 3.53) （已译） *)

(*
   本节说明自然变换、函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition One_hom_iso {B : Category} (F G : _1 ⟶ B) :
  ({| carrier := F ⟹ G; is_setoid := @Transform_Setoid _1 B F G |} : SetoidObject)
    ≅[Sets]
  {| carrier := F ttt ~> G ttt; is_setoid := @homset B (F ttt) (G ttt) |} := {|
  to   := {| morphism := fun η => η ttt |};
  from := {| morphism := fun h =>
    {| transform := fun a => match a with ttt => h end |} |}
|}.
Next Obligation.
  intros B F G η θ Hηθ; exact (Hηθ ttt).
Qed.
Next Obligation.
  intros B F G h x y f; destruct x, y, f; simpl.
  assert (HF : fmap[F] ttt ≈ id) by apply (@fmap_id _ _ F ttt).
  assert (HG : fmap[G] ttt ≈ id) by apply (@fmap_id _ _ G ttt).
  rewrite HF, HG; cat.
Qed.
Next Obligation.
  intros B F G h x y f; destruct x, y, f; simpl.
  assert (HF : fmap[F] ttt ≈ id) by apply (@fmap_id _ _ F ttt).
  assert (HG : fmap[G] ttt ≈ id) by apply (@fmap_id _ _ G ttt).
  rewrite HF, HG; cat.
Qed.
Next Obligation.
  intros B F G h h' Hh a; destruct a; exact Hh.
Qed.
Next Obligation.
  intros B F G h; reflexivity.
Qed.
Next Obligation.
  intros B F G η a; destruct a; reflexivity.
Qed.

(* Seven Sketches states Example 3.53 at B := Sets: a natural
   transformation between two functors [1 ⟶ Sets] is just a function
   between their value setoids. *)
Example One_hom_iso_Sets (F G : _1 ⟶ Sets) :
  ({| carrier := F ⟹ G;
      is_setoid := @Transform_Setoid _1 Sets F G |} : SetoidObject)
    ≅[Sets]
  {| carrier := F ttt ~> G ttt;
     is_setoid := @homset Sets (F ttt) (G ttt) |} :=
  One_hom_iso F G.
