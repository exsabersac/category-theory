Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Two.

Generalizable All Variables.

(* * * Pointwise 终对象 indexed products 函子 范畴 （已译） *)

(*
 nLab:      https://ncatlab.org/nlab/show/terminal+object
 nLab:      https://ncatlab.org/nlab/show/product
 Wikipedia: https://en.wikipedia.org/wiki/Product_(category_theory)
 Book:      Mac Lane, CWM 2nd ed., §III.5 Exercise 5, p. 74

   本文件给出终对象实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* 相关说明。 （已译） *)

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma iprod_jointly_monic {C : Category} {A : Type} (f : A → C)
  (p : C) (proj : ∀ a : A, p ~> f a)
  (HP : IsIndexedProduct f p proj)
  {c : C} (u v : c ~> p) :
  (∀ a : A, proj a ∘ u ≈ proj a ∘ v) → u ≈ v.
Proof.
  intros Heq.
  pose proof (iprod_desc HP (fun a => proj a ∘ u)) as U.
  transitivity (unique_obj U).
  - symmetry.
    apply (uniqueness U).
    intros a; reflexivity.
  - apply (uniqueness U).
    intros a; symmetry; apply Heq.
Qed.

(* * ** The 常值 函子, terminal 函子 （已译） *)

(*
   本节说明函子、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Constant_Functor@{co ch cp dro dh dp}
  {C : Category@{co ch cp}} {D : Category@{dro dh dp}} (d : D) : C ⟶ D :=
  {| fobj          := fun _ => d
   ; fmap          := fun _ _ _ => id
   ; fmap_respects := fun _ _ _ _ _ => reflexivity _
   ; fmap_id       := fun _ => reflexivity _
   ; fmap_comp     := fun _ _ _ _ _ => symmetry (id_left id) |}.

(* The 终对象 [C, D]: 常值 函子 at 1. D's hom and
 证明 universes identified here, [Terminal]'s doing. （已译） *)
Definition Constant_Terminal_Functor@{co ch cp dro dh}
  {C : Category@{co ch cp}} {D : Category@{dro dh dh}}
  (T : @Terminal D) : C ⟶ D :=
  Constant_Functor@{co ch cp dro dh dh} (@terminal_obj D T).

(*
   本节说明 Terminal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Program Instance Functor_Category_Terminal {C D : Category}
  (T : @Terminal D) : @Terminal ([C, D]) := {|
  terminal_obj := Constant_Terminal_Functor T;
  one := fun F => {| transform := fun _ => one |}
|}.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.
Next Obligation. apply one_unique. Qed.

(** ** Pointwise indexed products *)

Section FunIndexedProducts.

Context {C : Category}.
Context {D : Category}.
Context (HP : @HasIndexedProducts D).
Context {A : Type}.
Context (F : A → (C ⟶ D)).

Definition fun_iprod_fam (c : C) : A → D := fun a => fobj[F a] c.

Definition fun_iprod_obj (c : C) : D := indexed_product (fun_iprod_fam c).

Definition fun_iprod_pr (c : C) (a : A) : fun_iprod_obj c ~> F a c :=
  indexed_product_proj (fun_iprod_fam c) a.

Definition fun_iprod_ump (c : C) :
  IsIndexedProduct (fun_iprod_fam c) (fun_iprod_obj c) (fun_iprod_pr c) :=
  indexed_product_ump (fun_iprod_fam c).

(* The arrow action: unique map 进入 product at [c'] induced the
 family whose [a]th leg [fmap[F a] g] after [a]th projection. （已译） *)
Definition fun_iprod_fmap {c c' : C} (g : c ~> c') :
  fun_iprod_obj c ~> fun_iprod_obj c' :=
  unique_obj (iprod_desc (fun_iprod_ump c')
                (fun a => fmap[F a] g ∘ fun_iprod_pr c a)).

Lemma fun_iprod_fmap_commutes {c c' : C} (g : c ~> c') (a : A) :
  fun_iprod_pr c' a ∘ fun_iprod_fmap g
    ≈ fmap[F a] g ∘ fun_iprod_pr c a.
Proof.
  exact (unique_property
           (iprod_desc (fun_iprod_ump c')
              (fun a => fmap[F a] g ∘ fun_iprod_pr c a)) a).
Qed.

(* The pointwise product 函子. Each three laws proved by
 composing projections appealing [iprod_jointly_monic]. （已译） *)
Program Definition Fun_iprod : C ⟶ D := {|
  fobj := fun_iprod_obj;
  fmap := fun c c' g => fun_iprod_fmap g
|}.
Next Obligation.
  proper.
  apply (iprod_jointly_monic _ _ _ (fun_iprod_ump y)).
  intros a.
  rewrite (fun_iprod_fmap_commutes x0 a).
  rewrite (fun_iprod_fmap_commutes y0 a).
  now rewrite X.
Qed.
Next Obligation.
  apply (iprod_jointly_monic _ _ _ (fun_iprod_ump x)).
  intros a.
  rewrite (fun_iprod_fmap_commutes (@id C x) a).
  rewrite fmap_id, id_left, id_right.
  reflexivity.
Qed.
Next Obligation.
  apply (iprod_jointly_monic _ _ _ (fun_iprod_ump z)).
  intros a.
  rewrite (fun_iprod_fmap_commutes (f ∘ g) a).
  rewrite fmap_comp.
  rewrite (comp_assoc (fun_iprod_pr z a)
             (fun_iprod_fmap f) (fun_iprod_fmap g)).
  rewrite (fun_iprod_fmap_commutes f a).
  rewrite <- (comp_assoc (fmap[F a] f) (fun_iprod_pr y a)
                (fun_iprod_fmap g)).
  rewrite (fun_iprod_fmap_commutes g a).
  rewrite (comp_assoc (fmap[F a] f) (fmap[F a] g) (fun_iprod_pr x a)).
  reflexivity.
Qed.

(* The [a]th projection 自然变换: 自然性 square
 IS defining equation arrow action. （已译） *)
Program Definition Fun_iprod_proj (a : A) : Fun_iprod ⟹ F a := {|
  transform := fun c => fun_iprod_pr c a
|}.
Next Obligation. symmetry; apply fun_iprod_fmap_commutes. Qed.
Next Obligation. apply fun_iprod_fmap_commutes. Qed.

Definition fun_iprod_tuple_at (Q : C ⟶ D) (pi : ∀ a, Q ⟹ F a) (c : C) :
  Q c ~> fun_iprod_obj c :=
  unique_obj (iprod_desc (fun_iprod_ump c) (fun a => transform (pi a) c)).

Lemma fun_iprod_tuple_commutes (Q : C ⟶ D) (pi : ∀ a, Q ⟹ F a)
  (c : C) (a : A) :
  fun_iprod_pr c a ∘ fun_iprod_tuple_at Q pi c ≈ transform (pi a) c.
Proof.
  exact (unique_property
           (iprod_desc (fun_iprod_ump c) (fun a => transform (pi a) c)) a).
Qed.

(* The mediating transformation. Its 自然性 where 自然性 of
 competing family [pi] spent, nowhere else. （已译） *)
Program Definition fun_iprod_tuple (Q : C ⟶ D) (pi : ∀ a, Q ⟹ F a) :
  Q ⟹ Fun_iprod := {|
  transform := fun c => fun_iprod_tuple_at Q pi c
|}.
Next Obligation.
  apply (iprod_jointly_monic _ _ _ (fun_iprod_ump y)).
  intros a.
  rewrite (comp_assoc (fun_iprod_pr y a) (fun_iprod_fmap f)
             (fun_iprod_tuple_at Q pi x)).
  rewrite (fun_iprod_fmap_commutes f a).
  rewrite <- (comp_assoc (fmap[F a] f) (fun_iprod_pr x a)
                (fun_iprod_tuple_at Q pi x)).
  rewrite (fun_iprod_tuple_commutes Q pi x a).
  rewrite (comp_assoc (fun_iprod_pr y a) (fun_iprod_tuple_at Q pi y)
             (fmap[Q] f)).
  rewrite (fun_iprod_tuple_commutes Q pi y a).
  apply naturality.
Qed.
Next Obligation.
  symmetry.
  apply (iprod_jointly_monic _ _ _ (fun_iprod_ump y)).
  intros a.
  rewrite (comp_assoc (fun_iprod_pr y a) (fun_iprod_fmap f)
             (fun_iprod_tuple_at Q pi x)).
  rewrite (fun_iprod_fmap_commutes f a).
  rewrite <- (comp_assoc (fmap[F a] f) (fun_iprod_pr x a)
                (fun_iprod_tuple_at Q pi x)).
  rewrite (fun_iprod_tuple_commutes Q pi x a).
  rewrite (comp_assoc (fun_iprod_pr y a) (fun_iprod_tuple_at Q pi y)
             (fmap[Q] f)).
  rewrite (fun_iprod_tuple_commutes Q pi y a).
  apply naturality.
Qed.

(* The elementary 普遍性质, [C, D]. Existence is
 [fun_iprod_tuple]; triangle uniqueness clause the
 corresponding facts D, taken at each 对象. （已译） *)
Program Definition Fun_IsIndexedProduct :
  @IsIndexedProduct ([C, D]) A F Fun_iprod Fun_iprod_proj := {|
  iprod_desc := fun Q pi => {| unique_obj := fun_iprod_tuple Q pi |}
|}.
Next Obligation. apply fun_iprod_tuple_commutes. Qed.
Next Obligation.
  apply (uniqueness
           (iprod_desc (fun_iprod_ump x) (fun a => transform (pi a) x))).
  intros a.
  apply X.
Qed.

End FunIndexedProducts.

(*
   本节说明 Terminal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Fun_HasIndexedProducts {C D : Category}
  (HP : @HasIndexedProducts D) : @HasIndexedProducts ([C, D]) :=
  @Build_HasIndexedProducts ([C, D])
    (fun A F => @Fun_iprod C D HP A F)
    (fun A F a => @Fun_iprod_proj C D HP A F a)
    (fun A F => @Fun_IsIndexedProduct C D HP A F).

(* 相关说明。 （已译） *)

Definition bool_fam {C : Category} (x y : C) : bool → C :=
  fun b => if b then x else y.

Definition cartesian_bool_proj {C : Category} (CP : @Cartesian C) (x y : C)
  (b : bool) : @product_obj C CP x y ~> bool_fam x y b :=
  match b with
  | true  => exl
  | false => exr
  end.

Program Definition cartesian_bool_IsIndexedProduct {C : Category}
  (CP : @Cartesian C) (x y : C) :
  IsIndexedProduct (bool_fam x y) (@product_obj C CP x y)
    (cartesian_bool_proj CP x y) := {|
  iprod_desc := fun c pi => {| unique_obj := pi true △ pi false |}
|}.
Next Obligation.
  destruct a; simpl.
  - apply exl_fork.
  - apply exr_fork.
Qed.
Next Obligation.
  symmetry.
  apply ump_products.
  split.
  - exact (X true).
  - exact (X false).
Qed.

(** 本节：The pointwise indexed product at two-element index, compared the
 pointwise binary product Instance/Fun/Cartesian.v. （已译） *)

Definition Fun_bool_iprod_iso {C D : Category}
  (HP : @HasIndexedProducts D) (CD : @Cartesian D) (F G : C ⟶ D) :
  @Isomorphism ([C, D])
    (Fun_iprod HP (@bool_fam ([C, D]) F G))
    (@product_obj ([C, D]) (Functor_Category_Cartesian C D CD) F G) :=
  iprod_unique_iso (@bool_fam ([C, D]) F G) _ _ _ _
    (Fun_IsIndexedProduct HP (@bool_fam ([C, D]) F G))
    (cartesian_bool_IsIndexedProduct
       (Functor_Category_Cartesian C D CD) F G).

Definition Fun_bool_iprod_iso_commutes {C D : Category}
  (HP : @HasIndexedProducts D) (CD : @Cartesian D) (F G : C ⟶ D) (b : bool) :
  cartesian_bool_proj (Functor_Category_Cartesian C D CD) F G b
    ∘ to (Fun_bool_iprod_iso HP CD F G)
    ≈ Fun_iprod_proj HP (@bool_fam ([C, D]) F G) b :=
  iprod_compare_commutes (@bool_fam ([C, D]) F G) _ _ _ _
    (cartesian_bool_IsIndexedProduct
       (Functor_Category_Cartesian C D CD) F G) b.

Definition Fun_bool_iprod_iso_inv_commutes {C D : Category}
  (HP : @HasIndexedProducts D) (CD : @Cartesian D) (F G : C ⟶ D) (b : bool) :
  @compose ([C, D]) _ _ _
      (Fun_iprod_proj HP (@bool_fam ([C, D]) F G) b)
      (from (Fun_bool_iprod_iso HP CD F G))
    ≈ cartesian_bool_proj (Functor_Category_Cartesian C D CD) F G b :=
  iprod_compare_inv_commutes (@bool_fam ([C, D]) F G) _ _ _ _
    (Fun_IsIndexedProduct HP (@bool_fam ([C, D]) F G)) b.

(* 相关说明。 （已译） *)

Section Strictness.

Context {C : Category}.
Context {D : Category}.
Context (T : @Terminal D).
Context (HP : @HasIndexedProducts D).

Example fun_terminal_obj (c : C) :
  fobj[@terminal_obj ([C, D]) (Functor_Category_Terminal T)] c
    = @terminal_obj D T := eq_refl.

Example fun_terminal_fmap (c c' : C) (f : c ~> c') :
  fmap[@terminal_obj ([C, D]) (Functor_Category_Terminal T)] f
    = @id D (@terminal_obj D T) := eq_refl.

Example fun_terminal_one_component (F : C ⟶ D) (c : C) :
  transform (@one ([C, D]) (Functor_Category_Terminal T) F) c
    = @one D T (F c) := eq_refl.

Example fun_iprod_obj_computes {A : Type} (F : A → (C ⟶ D)) (c : C) :
  fobj[Fun_iprod HP F] c = indexed_product (fun a => fobj[F a] c) := eq_refl.

Example fun_iprod_proj_component {A : Type} (F : A → (C ⟶ D))
  (a : A) (c : C) :
  transform (Fun_iprod_proj HP F a) c
    = indexed_product_proj (fun a => fobj[F a] c) a := eq_refl.

End Strictness.

Section StrictnessNegatives.

Context {C : Category}.
Context {D : Category}.
Context (HP : @HasIndexedProducts D).
Context (CD : @Cartesian D).
Context (F G : C ⟶ D) (c : C).

(* CONTROL: 对象 action pointwise indexed product the
 indexed product pointwise family, nose. （已译） *)
Example ctl_bool_iprod_obj :
  fobj[Fun_iprod HP (@bool_fam ([C, D]) F G)] c
    = indexed_product (fun b : bool => fobj[@bool_fam ([C, D]) F G b] c)
  := eq_refl.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example bool_iprod_is_binary_product :
  fobj[Fun_iprod HP (@bool_fam ([C, D]) F G)] c
    = fobj[@product_obj ([C, D]) (Functor_Category_Cartesian C D CD) F G] c
  := eq_refl.

(* 相关说明。 （已译） *)
Example fun_iprod_class_mediator {A : Type} (Fm : A → (C ⟶ D))
  (Q : C ⟶ D) (pi : ∀ a, Q ⟹ Fm a) :
  unique_obj (iprod_desc (Fun_IsIndexedProduct HP Fm) pi)
    = fun_iprod_tuple HP Fm Q pi := eq_refl.

End StrictnessNegatives.

(* * ** Relation diagonal 函子 （已译） *)

Section DiagonalComparison.

Context {C : Category}.
Context {D : Category}.
Context (d : D) (c : C).

(* Object arrow actions agree [Functor/Diagonal.v]'s 常值
 函子 ON THE NOSE. （已译） *)
Example constant_functor_diagonal_obj :
  fobj[@Constant_Functor C D d] c = fobj[fobj[@Diagonal D C] d] c := eq_refl.

Example constant_functor_diagonal_fmap (f : c ~> c) :
  fmap[@Constant_Functor C D d] f = fmap[fobj[@Diagonal D C] d] f := eq_refl.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Fail Example constant_functor_is_diagonal :
  @Constant_Functor C D d = fobj[@Diagonal D C] d := eq_refl.

End DiagonalComparison.

(** ** Witnesses over [_2, Sets] *)

Definition FunBoolSet : SetoidObject := {|
  carrier   := bool
; is_setoid := eq_Setoid bool
|}.

Definition Two_Bool : _2 ⟶ Sets := @Constant_Functor _2 Sets FunBoolSet.

Definition Two_Sets_Terminal : @Terminal ([_2, Sets]) :=
  Functor_Category_Terminal Sets_Terminal.

Example two_sets_terminal_obj (o : _2) :
  fobj[@terminal_obj ([_2, Sets]) Two_Sets_Terminal] o
    = @terminal_obj Sets Sets_Terminal := eq_refl.

Program Definition two_pick (b : bool) :
  @terminal_obj ([_2, Sets]) Two_Sets_Terminal ⟹ Two_Bool := {|
  transform := fun _ => {| morphism := fun _ => b |}
|}.

(*
   本节说明函子、hom、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem two_pick_distinct : two_pick true ≈ two_pick false → False.
Proof.
  intros Heq.
  exact (match Heq TwoX ttt with eq_refl => I end).
Qed.

Theorem two_sets_one_unique (F : _2 ⟶ Sets)
  (u v : F ~{[_2, Sets]}~> @terminal_obj ([_2, Sets]) Two_Sets_Terminal) :
  u ≈ v.
Proof. exact (@one_unique ([_2, Sets]) Two_Sets_Terminal F u v). Qed.

Definition Two_Sets_HasIndexedProducts : @HasIndexedProducts ([_2, Sets]) :=
  Fun_HasIndexedProducts Sets_HasIndexedProducts.

Definition two_bool_fam : bool → (_2 ⟶ Sets) := fun _ => Two_Bool.

Definition two_bool_prod : _2 ⟶ Sets :=
  @indexed_product ([_2, Sets]) Two_Sets_HasIndexedProducts bool two_bool_fam.

Example two_bool_prod_carrier :
  carrier (fobj[two_bool_prod] TwoX) = (∀ _ : bool, bool) := eq_refl.

Definition two_all_true : carrier (fobj[two_bool_prod] TwoX) :=
  fun _ => true.

Definition two_all_false : carrier (fobj[two_bool_prod] TwoX) :=
  fun _ => false.

(* The pointwise product does not collapse: it has at least two elements. *)
Theorem two_bool_prod_separates : two_all_true ≈ two_all_false → False.
Proof.
  intros Heq.
  exact (match Heq true with eq_refl => I end).
Qed.

(* Its projections compute. *)
Example two_bool_proj_computes (b : bool) :
  transform
    (@indexed_product_proj ([_2, Sets]) Two_Sets_HasIndexedProducts
       bool two_bool_fam b) TwoX two_all_true = true := eq_refl.

(*
   本节说明 Terminal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition two_pick_family (b : bool) :
  @terminal_obj ([_2, Sets]) Two_Sets_Terminal ⟹ two_bool_fam b :=
  two_pick b.

Definition two_pick_med :
  @terminal_obj ([_2, Sets]) Two_Sets_Terminal ~{[_2, Sets]}~> two_bool_prod :=
  unique_obj
    (iprod_desc
       (@indexed_product_ump ([_2, Sets]) Two_Sets_HasIndexedProducts
          bool two_bool_fam)
       two_pick_family).

Example two_pick_med_true :
  transform two_pick_med TwoX ttt true = true := eq_refl.

Example two_pick_med_false :
  transform two_pick_med TwoX ttt false = false := eq_refl.

Theorem two_pick_med_commutes (b : bool) :
  @indexed_product_proj ([_2, Sets]) Two_Sets_HasIndexedProducts
    bool two_bool_fam b ∘ two_pick_med ≈ two_pick_family b.
Proof.
  exact (unique_property
           (iprod_desc
              (@indexed_product_ump ([_2, Sets]) Two_Sets_HasIndexedProducts
                 bool two_bool_fam)
              two_pick_family) b).
Qed.

(* * ** The nullary case: terminal 函子 empty pointwise product （已译） *)

Program Definition terminal_empty_IsIndexedProduct {C : Category}
  (T : @Terminal C) {A : Type} (Hempty : A → False) (f : A → C)
  (proj : ∀ a : A, @terminal_obj C T ~> f a) :
  IsIndexedProduct f (@terminal_obj C T) proj := {|
  iprod_desc := fun c pi => {| unique_obj := one |}
|}.
Next Obligation. destruct (Hempty a). Qed.
Next Obligation. apply one_unique. Qed.

(*
   本节说明函子、同构、始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Fun_empty_iprod_terminal {C D : Category}
  (HP : @HasIndexedProducts D) (T : @Terminal D)
  {A : Type} (Hempty : A → False) (F : A → (C ⟶ D)) :
  @Isomorphism ([C, D])
    (Fun_iprod HP F)
    (@terminal_obj ([C, D]) (Functor_Category_Terminal T)) :=
  @iprod_unique_iso ([C, D]) A F _ _ _ _
    (Fun_IsIndexedProduct HP F)
    (terminal_empty_IsIndexedProduct
       (Functor_Category_Terminal T) Hempty F
       (fun a => False_rect _ (Hempty a))).
