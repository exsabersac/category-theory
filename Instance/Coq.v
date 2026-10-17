Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Strong.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Structure.Constant.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The 范畴 COQ types functions. （已译） *)

(*
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_sets

   本文件给出 Coq 类型相关实例。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   nLab:  https://ncatlab.org/nlab/show/ETCS
   https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory

   本节说明Lawvere 理论相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export]
Program Instance Coq : Category := {
  obj     := Type;                                   (* objects are types *)
  hom     := λ A B : Type, A → B;                    (* morphisms are functions *)
  homset  := λ _ _, {| equiv := λ f g, ∀ x, f x = g x |};  (* pointwise equality *)
  id      := λ _ x, x;                               (* identity function *)
  compose := λ _ _ _ g f x, g (f x)                  (* function composition *)
}.
Next Obligation. equivalence; congruence. Qed.
Next Obligation. proper; congruence. Qed.

(* Terminal 对象: singleton `unit`, unique map `λ _, tt`. （已译） *)
#[export]
Program Instance Coq_Terminal : @Terminal Coq := {
  terminal_obj := unit : Type;       (* the terminal object 1 := unit *)
  one := λ _ a, tt                    (* the unique map x ~> unit *)
}.
Next Obligation. destruct (f x0), (g x0); reflexivity. Qed.

(* 相关说明。 （已译） *)
#[export]
Program Instance Coq_Cartesian : @Cartesian Coq := {
  product_obj := λ x y, x * y : Type;          (* product object x × y *)
  fork := λ _ _ _ f g x, (f x, g x);           (* pairing ⟨f, g⟩ *)
  exl  := λ _ _ p, fst p;                       (* first projection *)
  exr  := λ _ _ p, snd p                        (* second projection *)
}.
Next Obligation. proper; congruence. Qed.
Next Obligation.
  intros; simplify; intros.
  - rewrite H; reflexivity.
  - rewrite H; reflexivity.
  - intros; simplify.
    rewrite <- H, <- H0.
    rewrite <- surjective_pairing; reflexivity.
Qed.

(* 相关说明。 （已译） *)
#[export]
Program Instance Coq_Monoidal : @Monoidal Coq :=
  @CC_Monoidal Coq Coq_Cartesian Coq_Terminal.

(*
   本节说明伴随、hom、同构相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Program Instance Coq_Closed : @Closed Coq _ := {
  exponent_obj := Basics.arrow;                         (* exponential y^x := x → y *)
  exp_iso := λ _ _ _,
    {| to   := {| morphism := λ f a b, f (a, b) |}      (* curry *)
     ; from := {| morphism := λ f p, f (fst p) (snd p) |} |}  (* uncurry *)
}.
Next Obligation. proper; extensionality X0; congruence. Qed.
Next Obligation. proper; congruence. Qed.

(* 相关说明。 （已译） *)
#[export]
Program Instance Coq_ClosedMonoidal : @ClosedMonoidal Coq :=
  @CCC_ClosedMonoidal Coq Coq_Cartesian Coq_Terminal Coq_Closed.

(*
   本节说明始/终对象相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Program Instance Coq_Initial : Initial Coq := {
  terminal_obj := False;             (* the initial object 0 := False *)
  one := λ _ _, False_rect _ _       (* the unique map False ~> x *)
}.
Next Obligation. contradiction. Qed.

(*
   本节说明笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export]
Program Instance Coq_Cocartesian : @Cocartesian Coq := {
  product_obj := sum;                          (* coproduct object x + y *)
  fork := λ _ _ _ f g x,                        (* copairing [f, g] *)
            match x with
            | Datatypes.inl v => f v
            | Datatypes.inr v => g v
            end;
  exl  := λ _ _ p, Datatypes.inl p;            (* left injection inl *)
  exr  := λ _ _ p, Datatypes.inr p             (* right injection inr *)
}.
Next Obligation.
  split; intros.
  - split; intros;
    rewrite H; reflexivity.
  - destruct x0; firstorder.
Qed.

(*
   nLab: https://ncatlab.org/nlab/show/tensorial+strength

   本节说明函子、（余）强度、笛卡尔相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

#[export]
Program Instance Coq_StrongFunctor (F : Coq ⟶ Coq) : StrongFunctor F := {|
  strength := λ _ _ p, fmap[F] (λ y, (fst p, y)) (snd p)  (* x × F y ~> F (x × y) *)
|}.
Next Obligation.
  repeat srewrite_r (@fmap_comp _ _ F).
  f_equal.
Qed.
Next Obligation.
  repeat srewrite_r (@fmap_comp _ _ F).
  now srewrite (@fmap_id _ _ F).
Qed.
Next Obligation.
  repeat srewrite_r (@fmap_comp _ _ F).
  f_equal.
Qed.
