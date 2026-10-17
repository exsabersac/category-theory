Require Import Category.Lib.
Require Import Equations.Prop.Logic.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Fun.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.

Generalizable All Variables.

(** * 出自行走形状 1、2、3 的函子 *)

(* nLab:      https://ncatlab.org/nlab/show/terminal+category

   行走形状 (walking shapes)：终范畴、并行箭头、跨与共跨等小范畴，用作图的指标，
   使极限/余极限呈现为到这些形状的函子（Mac Lane §I.3）。本文件定义这些形状及其与
   C 中图的对应。长文首本波次压缩为导言；细节后续可续译。 *)

#[local] Obligation Tactic := idtac.

(* ---------------------------------------------------------------------- *)
(** ** Objects of C versus functors out of the point *)
(* ---------------------------------------------------------------------- *)

(* The functor picking out an object: everything goes to [x], the lone
   arrow of [_1] to [id]. *)
Program Definition Point {C : Category} (x : C) : _1 ⟶ C := {|
  fobj := fun _ => x;
  fmap := fun _ _ _ => id
|}.
Next Obligation. intros; reflexivity. Qed.
Next Obligation. intros; symmetry; apply id_left. Qed.

(* ... and the object it picks out. *)
Definition point_of {C : Category} (F : _1 ⟶ C) : C := F ttt.

(*
   本文件给出形状/往返相关引理。 First 往返. This is [=] 之间 OBJECTS, 其中 本库 的fers 无 [≈]; it holds 由 [eq_refl], so it is near-trivial -- [Po在t x] w作为 built 到 have [x] 作为 its value.

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem point_of_Point {C : Category} (x : C) : point_of (Point x) = x.
Proof. reflexivity. Qed.

(*
   Second round trip, at the strict 函子 equality: [Point (F ttt)] and

   本节说明相关定义、性质与动机。 [F] have same 对象 map nose, their 态射 maps agree.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Point_point_of_strict {C : Category} (F : _1 ⟶ C) :
  @equiv _ Functor_StrictEq_Setoid (Point (point_of F)) F.
Proof.
  unshelve refine (existT _ _ _).
  - intro x; destruct x; reflexivity.
  - intros x y f; destruct x, y, f; simpl.
    unfold transport, transport_r; simpl.
    symmetry; exact (@fmap_id _ _ F ttt).
Qed.

Corollary Point_point_of {C : Category} (F : _1 ⟶ C) : Point (point_of F) ≈ F.
Proof. apply strict_equiv_implies_fun_equiv, Point_point_of_strict. Qed.

(*
   The correspondence is 忠实 in the strongest available sense: two

   对象 give equivalent 函子 当且仅当 they are isomorphic.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Point_equiv_iso {C : Category} (x y : C) : (Point x ≈ Point y) ↔ (x ≅ y).
Proof.
  split.
  - intros [i _]; exact (i ttt).
  - intro i; exists (fun _ => i); intros a b f; simpl.
    rewrite id_right, iso_from_to; reflexivity.
Qed.

(* The same correspondence one level up, as functors between categories.
   [One_Eval] evaluates at the point, [One_Const] is [Point] made
   functorial. *)
Program Definition One_Eval {C : Category} : [_1, C] ⟶ C := {|
  fobj := fun F => F ttt;
  fmap := fun F G η => transform[η] ttt
|}.
Next Obligation. intros C F G η θ e; exact (e ttt). Qed.
Next Obligation. intros C F; exact (@fmap_id _ _ F ttt). Qed.
Next Obligation. intros C F G H η θ; reflexivity. Qed.

Program Definition One_Const {C : Category} : C ⟶ [_1, C] := {|
  fobj := Point;
  fmap := fun x y f => {| transform := fun _ => f |}
|}.
Next Obligation. intros C x y f a b g; now rewrite id_left, id_right. Qed.
Next Obligation. intros C x y f a b g; now rewrite id_left, id_right. Qed.
Next Obligation. intros C x y f g e a; exact e. Qed.
Next Obligation. intros C x a; reflexivity. Qed.
Next Obligation. intros C x y z f g a; reflexivity. Qed.

(*
   [Point (F ttt) ≅ F] in the 函子 范畴, with identity components.

   本节说明相关定义、性质与动机。 [Point_point_of_strict] above is different currency, equality 函子; it does reach this 同构, but only via [strict_equiv_implies_fun_equiv] then [函子_Setoid_Nat_Iso], that route hides components.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Point_point_of_iso {C : Category} (F : _1 ⟶ C) :
  @Isomorphism (@Fun _1 C) (Point (point_of F)) F := {|
  to   := {| transform := fun a =>
    match a as a' return Point (point_of F) a' ~> F a' with ttt => id end |};
  from := {| transform := fun a =>
    match a as a' return F a' ~> Point (point_of F) a' with ttt => id end |}
|}.
Next Obligation.
  intros C F a b f; destruct a, b, f; simpl.
  rewrite (@fmap_id _ _ F ttt); cat.
Qed.
Next Obligation.
  intros C F a b f; destruct a, b, f; simpl.
  rewrite (@fmap_id _ _ F ttt); cat.
Qed.
Next Obligation.
  intros C F a b f; destruct a, b, f; simpl.
  rewrite (@fmap_id _ _ F ttt); cat.
Qed.
Next Obligation.
  intros C F a b f; destruct a, b, f; simpl.
  rewrite (@fmap_id _ _ F ttt); cat.
Qed.
Next Obligation.
  intros C F a; destruct a; simpl; rewrite (@fmap_id _ _ F ttt); cat.
Qed.
Next Obligation. intros C F a; destruct a; simpl; cat. Qed.

(*
   本节：[[_1, C] ≃ C], theorem behind Instance/One.v's header prose. This. is EQUIVALENCE 范畴: [≅[Cat]] this library is [Cat]'s 同构, [Cat]'s hom-setoid identifies 函子 up 自然 同构.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition One_Fun_iso {C : Category} : [_1, C] ≅[Cat] C := {|
  to   := One_Eval;
  from := One_Const
|}.
Next Obligation.
  intro C.
  apply strict_equiv_implies_fun_equiv.
  unshelve refine (existT _ _ _).
  - intro x; reflexivity.
  - intros x y f; reflexivity.
Qed.
Next Obligation.
  intro C.
  exists (fun F => Point_point_of_iso F).
  intros F G η a; destruct a; simpl; now rewrite id_left, id_right.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Morphisms of C versus functors out of the walking arrow *)
(* ---------------------------------------------------------------------- *)

(* The functor materializing a morphism: [TwoX] and [TwoY] go to its
   endpoints, [TwoXY] to the morphism itself, the two identities to [id]. *)
Program Definition Walk {C : Category} {x y : C} (f : x ~> y) : _2 ⟶ C := {|
  fobj := fun a => match a with TwoX => x | TwoY => y end;
  fmap := fun a b (g : TwoHom a b) =>
    match g in TwoHom a' b'
      return (match a' with TwoX => x | TwoY => y end)
             ~> (match b' with TwoX => x | TwoY => y end) with
    | TwoIdX => id
    | TwoIdY => id
    | TwoXY  => f
    end
|}.
Next Obligation. intros C x y f a; destruct a; reflexivity. Qed.
Next Obligation.
  intros C x y f a b c g h.
  pose proof (TwoHom_inv _ _ g) as Hg.
  pose proof (TwoHom_inv _ _ h) as Hh.
  destruct a, b, c; simpl in *; try contradiction; subst; simpl; cat.
Qed.

(*
   本节说明相关定义、性质与动机。 Instance/Two.v's [id] at [TwoX] reduces [TwoIdX], so [fmap_id]. applies it up conversion; but [TwoIdX] is not SYNTACTICALLY [id], which is enough stop [rewrite fmap_id] [apply fmap_id].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma fmap_TwoIdX {C : Category} (F : _2 ⟶ C) : fmap[F] TwoIdX ≈ id.
Proof. exact (@fmap_id _ _ F TwoX). Qed.

Lemma fmap_TwoIdY {C : Category} (F : _2 ⟶ C) : fmap[F] TwoIdY ≈ id.
Proof. exact (@fmap_id _ _ F TwoY). Qed.

(* ... and the morphism it materializes. *)
Definition arrow_of {C : Category} (F : _2 ⟶ C) : F TwoX ~> F TwoY := fmap[F] TwoXY.

(*
   本节说明相关定义、性质与动机。 First round trip, definitional therefore near-trivial: [Walk f] was.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem arrow_of_Walk {C : Category} {x y : C} (f : x ~> y) : arrow_of (Walk f) ≈ f.
Proof. reflexivity. Qed.

(*
   Second round trip, at the strict 函子 equality.  The two identity

   本节说明相关定义、性质与动机。 cases are where content is: [Walk (arrow_of F)] sends them [id] construction, only [fmap_id] identifies that [fmap[F]] them.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Walk_arrow_of_strict {C : Category} (F : _2 ⟶ C) :
  @equiv _ Functor_StrictEq_Setoid (Walk (arrow_of F)) F.
Proof.
  unshelve refine (existT _ _ _).
  - intro a; destruct a; reflexivity.
  - intros a b g; destruct g; simpl; unfold transport, transport_r; simpl.
    + symmetry; apply fmap_TwoIdX.
    + symmetry; apply fmap_TwoIdY.
    + reflexivity.
Qed.

Corollary Walk_arrow_of {C : Category} (F : _2 ⟶ C) : Walk (arrow_of F) ≈ F.
Proof. apply strict_equiv_implies_fun_equiv, Walk_arrow_of_strict. Qed.

(*
   The 对象 action of [Walk f] does not see [f] at all: parallel

   本节说明相关定义、性质与动机。 态射 give 函子 literally same action 对象.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Walk_objects_agree {C : Category} {x y : C} (f g : x ~> y) :
  ∀ a, Walk f a = Walk g a.
Proof. intro a; destruct a; reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(** ** The comparison [_2, C] versus the arrow category *)
(* ---------------------------------------------------------------------- *)

(* A functor out of [_2] gives the object of [Arrow C] that its generating
   arrow names; a natural transformation gives the commuting square, which
   is precisely its naturality at [TwoXY]. *)
Program Definition Arrow_of_Fun {C : Category} : [_2, C] ⟶ @Arrow C := {|
  fobj := fun F => ((F TwoX, F TwoY); fmap[F] TwoXY);
  fmap := fun F G η => ((transform[η] TwoX, transform[η] TwoY); _)
|}.
Next Obligation. intros C F G η; simpl; apply naturality. Qed.
Next Obligation.
  intros C F G η θ e; split; simpl; [ exact (e TwoX) | exact (e TwoY) ].
Qed.
Next Obligation. intros C F; split; simpl; [ apply fmap_TwoIdX | apply fmap_TwoIdY ]. Qed.
Next Obligation. intros C F G H η θ; split; simpl; reflexivity. Qed.

(*
   Conversely an 对象 of [Arrow C] is a 态射, hence a [Walk], and a

   本节：交换方块 is 自然变换 between two [Walk]s: naturality at two identities is 单位律, at [TwoXY] it is square itself.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Fun_of_Arrow {C : Category} : @Arrow C ⟶ [_2, C] := {|
  fobj := fun x => Walk (`2 x);
  fmap := fun x y u =>
    {| transform := fun a =>
         match a as a' return Walk (`2 x) a' ~> Walk (`2 y) a' with
         | TwoX => fst (`1 u)
         | TwoY => snd (`1 u)
         end |}
|}.
Next Obligation.
  intros C x y u a b f; destruct f; simpl;
    try (now rewrite id_left, id_right).
  exact (`2 u).
Qed.
Next Obligation.
  intros C x y u a b f; destruct f; simpl;
    try (now rewrite id_left, id_right).
  symmetry; exact (`2 u).
Qed.
Next Obligation. intros C x y u v [H1 H2] a; destruct a; simpl; assumption. Qed.
Next Obligation. intros C x a; destruct a; reflexivity. Qed.
Next Obligation. intros C x y z f g a; destruct a; reflexivity. Qed.

(*
   本节说明相关定义、性质与动机。 The strict half comparison: going Arrow C -> [_2, C] -> Arrow C. returns 对象 one started from, nose. The 对象 equality needs pair comma 对象 destructured, which is why proof opens pattern rather than [eq_refl];

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Arrow_Fun_Arrow_strict {C : Category} :
  @equiv _ Functor_StrictEq_Setoid (Arrow_of_Fun ◯ Fun_of_Arrow) (Id[@Arrow C]).
Proof.
  unshelve refine (existT _ _ _).
  - intros [[a b] h]; reflexivity.
  - intros [[a b] h] [[a' b'] h'] u; simpl.
    unfold transport, transport_r; simpl.
    split; reflexivity.
Qed.

(*
   The other half, as a 自然 同构 in [[_2, C]].  Its components

   本节说明相关定义、性质与动机。 are identities, which is sense which two 函子 differ only how they present [fmap] at two identity arrows [_2];

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Walk_arrow_of_iso {C : Category} (F : _2 ⟶ C) :
  @Isomorphism (@Fun _2 C) (Walk (arrow_of F)) F := {|
  to   := {| transform := fun a =>
    match a as a' return Walk (arrow_of F) a' ~> F a' with
    | TwoX => id
    | TwoY => id
    end |};
  from := {| transform := fun a =>
    match a as a' return F a' ~> Walk (arrow_of F) a' with
    | TwoX => id
    | TwoY => id
    end |}
|}.
Next Obligation.
  intros C F a b f; destruct f; simpl;
    rewrite ?fmap_TwoIdX, ?fmap_TwoIdY; cat.
Qed.
Next Obligation.
  intros C F a b f; destruct f; simpl;
    rewrite ?fmap_TwoIdX, ?fmap_TwoIdY; cat.
Qed.
Next Obligation.
  intros C F a b f; destruct f; simpl;
    rewrite ?fmap_TwoIdX, ?fmap_TwoIdY; cat.
Qed.
Next Obligation.
  intros C F a b f; destruct f; simpl;
    rewrite ?fmap_TwoIdX, ?fmap_TwoIdY; cat.
Qed.
Next Obligation.
  intros C F a; destruct a; simpl; rewrite ?fmap_TwoIdX, ?fmap_TwoIdY; cat.
Qed.
Next Obligation.
  intros C F a; destruct a; simpl; rewrite ?fmap_TwoIdX, ?fmap_TwoIdY; cat.
Qed.

(*
   本节说明相关定义、性质与动机。 The comparison Construction/Arrow.v left open. [≅[Cat]] is an.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Two_Fun_Arrow {C : Category} : [_2, C] ≅[Cat] @Arrow C := {|
  to   := Arrow_of_Fun;
  from := Fun_of_Arrow
|}.
Next Obligation.
  intro C.
  apply strict_equiv_implies_fun_equiv, Arrow_Fun_Arrow_strict.
Qed.
Next Obligation.
  intro C.
  exists (fun F => Walk_arrow_of_iso F).
  intros F G η a; destruct a; simpl; now rewrite id_left, id_right.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Composable pairs versus functors out of the ordinal 3 *)
(* ---------------------------------------------------------------------- *)

(*
   The two generating steps of [_3] are [ord_step] at the two 对象 of

   本节说明相关定义、性质与动机。 [Ordinal 2]; their endpoints are Instance/Ordinal.v's [ord3_0], [ord3_1], [ord3_2] definitionally, which is what lets types below be written without transports.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition ord2_0 : Ord_obj 2 := ord_at 0%nat (le_t_S le_t_n).
Definition ord2_1 : Ord_obj 2 := ord_at 1%nat le_t_n.

Definition three_01 : ord3_0 ~{_3}~> ord3_1 := ord_step ord2_0.
Definition three_12 : ord3_1 ~{_3}~> ord3_2 := ord_step ord2_1.
Definition three_02 : ord3_0 ~{_3}~> ord3_2 := three_12 ∘ three_01.

(* The object assignment of a composable pair, read off an index.  It is
   total on [nat] because Instance/Ordinal.v's [OrdSteps] is; the values
   past 2 are never consulted. *)
Definition pair_obj {C : Category} (x y z : C) : nat → C :=
  fun k => match k with O => x | S O => y | _ => z end.

Definition pair_steps {C : Category} (X : nat → C)
  (f : X 0%nat ~> X 1%nat) (g : X 1%nat ~> X 2%nat) : OrdSteps 2 X :=
  fun k =>
    match k as k0 return le_t (S k0) 2 → X k0 ~> X (S k0) with
    | O        => fun _ => f
    | S O      => fun _ => g
    | S (S k') => fun H =>
        False_rect _ (le_t_zero_absurd (le_t_SS_inv (le_t_SS_inv H)))
    end.

(* A composable pair gives a diagram of shape 3.  This is
   Instance/Ordinal.v's [Functor_of_Steps] at n = 2, the case one below its
   [Functor_of_Triple]. *)
Definition Functor_of_Pair {C : Category} {x y z : C}
  (f : x ~> y) (g : y ~> z) : _3 ⟶ C :=
  Functor_of_Steps (pair_steps (pair_obj x y z) f g).

Theorem Functor_of_Pair_fst {C : Category} {x y z : C} (f : x ~> y) (g : y ~> z) :
  fmap[Functor_of_Pair f g] three_01 ≈ f.
Proof. exact (Functor_of_Steps_step (pair_steps (pair_obj x y z) f g) ord2_0). Qed.

Theorem Functor_of_Pair_snd {C : Category} {x y z : C} (f : x ~> y) (g : y ~> z) :
  fmap[Functor_of_Pair f g] three_12 ≈ g.
Proof. exact (Functor_of_Steps_step (pair_steps (pair_obj x y z) f g) ord2_1). Qed.

(*
   本节说明相关定义、性质与动机。 [_3] has six arrows: three identities, two generating steps, and. [three_02].

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Functor_of_Pair_comp {C : Category} {x y z : C} (f : x ~> y) (g : y ~> z) :
  fmap[Functor_of_Pair f g] three_02 ≈ g ∘ f.
Proof.
  unfold three_02.
  rewrite fmap_comp, Functor_of_Pair_fst, Functor_of_Pair_snd.
  reflexivity.
Qed.

(* ... and the composable pair a diagram of shape 3 carries. *)
Definition pair_fst {C : Category} (F : _3 ⟶ C) : F ord3_0 ~> F ord3_1 :=
  fmap[F] three_01.
Definition pair_snd {C : Category} (F : _3 ⟶ C) : F ord3_1 ~> F ord3_2 :=
  fmap[F] three_12.

(* The comparison isomorphism at each object of [_3].  An object is one of
   the three, so the three named ones are hit; the fourth branch is the
   out-of-range index, ruled out by the bound. *)
Definition pair_theta {C : Category} (F : _3 ⟶ C) (w : Ord_obj 3) :
  Functor_of_Pair (pair_fst F) (pair_snd F) w ≅ F w.
Proof.
  destruct w as [i H]; destruct i as [| [| [| i]]].
  - exact (ord_functor_iso F (@ord_obj_eq 3 ord3_0 (ord_at 0%nat H) eq_refl)).
  - exact (ord_functor_iso F (@ord_obj_eq 3 ord3_1 (ord_at 1%nat H) eq_refl)).
  - exact (ord_functor_iso F (@ord_obj_eq 3 ord3_2 (ord_at 2%nat H) eq_refl)).
  - destruct (le_t_zero_absurd (le_t_SS_inv (le_t_SS_inv (le_t_SS_inv H)))).
Defined.

(*
   本节说明相关定义、性质与动机。 The substantive round trip: every diagram shape 3 is one built. from its own composable pair.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Functor_of_Pair_of_Functor {C : Category} (F : _3 ⟶ C) :
  Functor_of_Pair (pair_fst F) (pair_snd F) ≈ F.
Proof.
  apply (ord_functor_equiv_from_steps _ F (pair_theta F)).
  intros [i H]; destruct i as [| [| i]]; simpl.
  - rewrite (Functor_of_Steps_step
               (pair_steps (pair_obj (F ord3_0) (F ord3_1) (F ord3_2))
                           (pair_fst F) (pair_snd F)) (ord_at 0%nat H)).
    simpl.
    unfold pair_fst, three_01.
    rewrite <- !fmap_comp.
    apply fmap_respects, le_t_irr.
  - rewrite (Functor_of_Steps_step
               (pair_steps (pair_obj (F ord3_0) (F ord3_1) (F ord3_2))
                           (pair_fst F) (pair_snd F)) (ord_at 1%nat H)).
    simpl.
    unfold pair_snd, three_12.
    rewrite <- !fmap_comp.
    apply fmap_respects, le_t_irr.
  - destruct (le_t_zero_absurd (le_t_SS_inv (le_t_SS_inv H))).
Qed.

(*
   本节说明相关定义、性质与动机。 The list vocabulary ([In], [NoDup], [length]) [lia] are used from. here on.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.

(* ---------------------------------------------------------------------- *)
(** ** Seven Sketches §3.3.2, Example 3.36: the correspondence at [_3] *)
(* ---------------------------------------------------------------------- *)

(* [_3] has exactly three non-identity morphisms, and the [_2]-correspondence
   turns each into a functor [_2 ⟶ _3].  These are the three the example
   draws. *)
Definition Two_Three_01 : _2 ⟶ _3 := Walk three_01.
Definition Two_Three_12 : _2 ⟶ _3 := Walk three_12.
Definition Two_Three_02 : _2 ⟶ _3 := Walk three_02.

(*
   Their 对象 actions, computed.  These are [=] between 对象, by

   本节说明相关定义、性质与动机。 [eq_refl]; they are near-trivial individually are recorded because together they are what distinguishes three 函子.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Two_Three_01_dom : Two_Three_01 TwoX = ord3_0 := eq_refl.
Example Two_Three_01_cod : Two_Three_01 TwoY = ord3_1 := eq_refl.
Example Two_Three_12_dom : Two_Three_12 TwoX = ord3_1 := eq_refl.
Example Two_Three_12_cod : Two_Three_12 TwoY = ord3_2 := eq_refl.
Example Two_Three_02_dom : Two_Three_02 TwoX = ord3_0 := eq_refl.
Example Two_Three_02_cod : Two_Three_02 TwoY = ord3_2 := eq_refl.

(* The correspondence exercised on this concrete target: each functor gives
   back the morphism it came from. *)
Corollary Two_Three_01_arrow : arrow_of Two_Three_01 ≈ three_01.
Proof. exact (arrow_of_Walk three_01). Qed.
Corollary Two_Three_12_arrow : arrow_of Two_Three_12 ≈ three_12.
Proof. exact (arrow_of_Walk three_12). Qed.
Corollary Two_Three_02_arrow : arrow_of Two_Three_02 ≈ three_02.
Proof. exact (arrow_of_Walk three_02). Qed.

(*
   The two 范畴-level comparisons instantiated at this same target,

   本节说明相关定义、性质与动机。 which is neither empty nor point: [_3] has three 对象 six 态射, enumeration below records.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Example Two_Fun_Arrow_at_three : [_2, _3] ≅[Cat] @Arrow _3 := Two_Fun_Arrow.
Example One_Fun_iso_at_three : [_1, _3] ≅[Cat] _3 := One_Fun_iso.

(* In an ordinal, isomorphic objects have equal indices: the two legs give
   inequalities in both directions. *)
Lemma ord_iso_val {n} {x y : Ord_obj n} (i : @Isomorphism (Ordinal n) x y) :
  ord_val x = ord_val y.
Proof.
  pose proof (le_t_to_le (to i)) as H1.
  pose proof (le_t_to_le (from i)) as H2.
  simpl in *; lia.
Qed.

(*
   Non-vacuity of Example 3.36: the three 函子 are pairwise

   本节说明相关定义、性质与动机。 non-equivalent -- not merely distinct terms, but not naturally isomorphic, since 自然 同构 would force equal indices at 对象 where they differ.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Two_Three_01_12 : (Two_Three_01 ≈ Two_Three_12) → False.
Proof. intros [i _]; pose proof (ord_iso_val (i TwoX)) as E; discriminate. Qed.

Theorem Two_Three_01_02 : (Two_Three_01 ≈ Two_Three_02) → False.
Proof. intros [i _]; pose proof (ord_iso_val (i TwoY)) as E; discriminate. Qed.

Theorem Two_Three_12_02 : (Two_Three_12 ≈ Two_Three_02) → False.
Proof. intros [i _]; pose proof (ord_iso_val (i TwoX)) as E; discriminate. Qed.

(*
   The example's own observation: over this target the 对象 action

   本节说明相关定义、性质与动机。 already determines 函子. The proof consumes thinness [_3] nothing else -- two transported 态射 actions are parallel arrows [Ordinal 3], [le_t_irr] says there is at most one such.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem two_three_objects_determine (F G : _2 ⟶ _3) (H : ∀ a, F a = G a) :
  @equiv _ Functor_StrictEq_Setoid F G.
Proof. exists H; intros a b f; apply le_t_irr. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Seven Sketches §3.3.2, Exercise 3.37: there are exactly six *)
(* ---------------------------------------------------------------------- *)

(* The correspondence, packaged at the total space of morphisms of [_3].
   [OrdMor 3] bundles a morphism with its endpoints, which is exactly the
   data a functor out of [_2] carries. *)
Definition two_three_mor (F : _2 ⟶ _3) : OrdMor 3 :=
  existT _ (F TwoX) (existT _ (F TwoY) (fmap[F] TwoXY)).

Definition mor_two_three (m : OrdMor 3) : _2 ⟶ _3 := Walk (projT2 (projT2 m)).

(* Near-trivial by destructuring: [Walk] stores its argument verbatim.  The
   [=] here reaches a morphism, but of [Ordinal 3], whose hom-setoid IS
   [Morphism_equality]; [≈] and [=] coincide there. *)
Theorem two_three_mor_of_mor (m : OrdMor 3) : two_three_mor (mor_two_three m) = m.
Proof. destruct m as [a [b h]]; reflexivity. Qed.

Theorem mor_of_two_three_mor (F : _2 ⟶ _3) :
  @equiv _ Functor_StrictEq_Setoid (mor_two_three (two_three_mor F)) F.
Proof. exact (Walk_arrow_of_strict F). Qed.

(* A functor [_2 ⟶ _3] read as a pair of indices, THROUGH the
   correspondence: [ord_coords] is Instance/Ordinal.v's coordinate map on
   morphisms, and [two_three_mor] is the correspondence. *)
Definition two_three_coords (F : _2 ⟶ _3) : (nat * nat)%type :=
  ord_coords (two_three_mor F).

Definition two_three_index : list (nat * nat) := ord_pairs 3.

(*
   本节说明相关定义、性质与动机。 The count. It is DERIVED, from Instance/Ordinal.v's closed formula.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem two_three_count : (length two_three_index = 6)%nat.
Proof. pose proof (ord_morphism_count 3) as H; unfold two_three_index; lia. Qed.

Theorem two_three_nodup : NoDup two_three_index.
Proof. exact (ord_pairs_nodup 3). Qed.

Theorem two_three_coords_in (F : _2 ⟶ _3) : In (two_three_coords F) two_three_index.
Proof. exact (ord_coords_in_pairs (two_three_mor F)). Qed.

(*
   Distinct indices are the only way two of these 函子 can differ:

   本节说明相关定义、性质与动机。 equal coordinates force strict equality 函子, transporting Instance/Ordinal.v's [ord_coords_inj] along correspondence.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem two_three_coords_faithful (F G : _2 ⟶ _3) :
  two_three_coords F = two_three_coords G →
  @equiv _ Functor_StrictEq_Setoid F G.
Proof.
  intro E.
  pose proof (ord_coords_inj (two_three_mor F) (two_three_mor G) E) as Em.
  pose proof (mor_of_two_three_mor F) as H1.
  pose proof (mor_of_two_three_mor G) as H2.
  rewrite Em in H1.
  exact (Equivalence_Transitive _ _ _ (Equivalence_Symmetric _ _ H1) H2).
Qed.

(* ... and every admissible pair of indices is realized, one functor per
   pair i ≤ j < 3. *)
Theorem two_three_coords_onto (i j : nat) (Hij : (i <= j)%nat) (Hj : (j < 3)%nat) :
  { F : _2 ⟶ _3 & two_three_coords F = (i, j) }.
Proof.
  destruct (ord_mor_of_pair i j Hij Hj) as [m Em].
  exists (mor_two_three m).
  unfold two_three_coords.
  now rewrite two_three_mor_of_mor.
Qed.

(* The index list is exactly the pairs i ≤ j < 3. *)
Theorem two_three_index_char (i j : nat) :
  In (i, j) two_three_index ↔ ((i <= j)%nat ∧ (j < 3)%nat).
Proof.
  split.
  - intro H; destruct (ord_pairs_sound 3 i j H) as [H1 H2]; exact (H1, H2).
  - intros [H1 H2]; exact (ord_pairs_complete 3 i j H1 H2).
Qed.

(* Exercise 3.37, assembled: the functors [_2 ⟶ _3] are classified, up to
   strict functor equality, by a duplicate-free list of SIX index pairs,
   one per i ≤ j. *)
Theorem two_three_enumeration :
  ((length two_three_index = 6)%nat *
   NoDup two_three_index *
   (∀ F : _2 ⟶ _3, In (two_three_coords F) two_three_index) *
   (∀ i j, (i <= j)%nat → (j < 3)%nat →
      { F : _2 ⟶ _3 & two_three_coords F = (i, j) }) *
   (∀ F G : _2 ⟶ _3, two_three_coords F = two_three_coords G →
      @equiv _ Functor_StrictEq_Setoid F G))%type.
Proof.
  exact (two_three_count, two_three_nodup, two_three_coords_in,
         two_three_coords_onto, two_three_coords_faithful).
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Seven Sketches §3.3.3, Exercise 3.45: the point into [Sets] *)
(* ---------------------------------------------------------------------- *)

(* Two small setoids used only as witnesses below. *)
Definition empty_setoid_object : SetoidObject :=
  {| carrier := False; is_setoid := eq_Setoid False |}.

Definition two_setoid_object : SetoidObject :=
  {| carrier := TwoObj; is_setoid := eq_Setoid TwoObj |}.

Program Definition const_TwoX : two_setoid_object ~{Sets}~> two_setoid_object := {|
  morphism := fun _ => TwoX
|}.

(*
   The tested converse promised at [Walk_对象_agree] and at

   本节说明相关定义、性质与动机。 [two_three_对象_determine]: over [Sets] identity constant map two-element setoid give two 函子 out [_2] SAME 对象 action, which [arrow_of] separates.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Walk_objects_insufficient :
  ((∀ a, Walk (@id Sets two_setoid_object) a = Walk const_TwoX a) *
   ((arrow_of (Walk (@id Sets two_setoid_object)) ≈ arrow_of (Walk const_TwoX))
      → False))%type.
Proof.
  split.
  - apply Walk_objects_agree.
  - intro H.
    pose proof (H TwoY) as E; simpl in E.
    discriminate.
Qed.

(*
   Exercise 3.45, the 构造性 direction: for every setoid S there is a

   本节说明相关定义、性质与动机。 函子 from point whose value at point is S. [=] between 对象 again, near-trivial -- [Point S] was built it -- but it is precisely statement exercise asks for.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Sets_point_value (S : Sets) : Point S ttt = S.
Proof. reflexivity. Qed.

(* ... and the round trip back. *)
Corollary Sets_point_of (F : _1 ⟶ Sets) : Point (point_of F) ≈ F.
Proof. exact (Point_point_of F). Qed.

(* The identification is at the right granularity: two setoids give
   equivalent functors from the point exactly when they are isomorphic in
   [Sets]. *)
Corollary Sets_point_iso (S T : Sets) :
  (Point S ≈ Point T) ↔ (S ≅[Sets] T).
Proof. exact (Point_equiv_iso S T). Qed.

(*
   本节说明相关定义、性质与动机。 Non-vacuity [Sets] instantiation, witness that escapes the. degenerate case: empty setoid singleton give NON-equivalent 函子 from point.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Theorem Sets_point_separates :
  (Point (C:=Sets) empty_setoid_object ≈ Point (C:=Sets) unit_setoid_object)
    → False.
Proof.
  intro H.
  destruct (fst (Point_equiv_iso _ _) H) as [f g _ _].
  exact (g ttt).
Qed.
