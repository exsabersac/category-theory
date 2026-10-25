Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** Applicative endofunctors on COQ, with the four laws as class fields. / COQ 上的应用函子端，四条定律作为类字段。 *)

(*
 nLab: https://ncatlab.org/nlab/show/applicative+functor
 Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor

 An applicative functor (Haskell sense) over COQ is an endofunctor
 [F : Coq ⟶ Coq] equipped with [pure : a → F a], injecting a value, and
 [ap : F (a → b) → F a → F b] (Haskell's [<*>]), applying a wrapped function
 to a wrapped argument. Categorically this is exactly a strong lax monoidal
 endofunctor on COQ with its cartesian monoidal structure (tensor [×], unit
 [unit]): [pure] supplies the unit [η : 1 → F 1] and [ap] the laxator
 [μ : F x ⊗ F y → F (x ⊗ y)], the four laws below being the lax-monoidal
 coherence axioms. The commented-out development at the end of CoqApplicative
 sketches this equivalence concretely.

 Unlike the parametric class in Theory/Coq/Applicative.v (which carries only
 [pure] and [ap], leaving lawfulness as a per-instance obligation), this
 formulation bundles the four applicative laws as class fields, stated as
 pointwise Leibniz equations on COQ morphisms:
 ap_id          [pure id <*> v = v];
 ap_comp        [pure (∘) <*> u <*> v <*> w = u <*> (v <*> w)];
 ap_homo        [pure f <*> pure x = pure (f x)];
 ap_interchange [u <*> pure y = pure (λ g, g y) <*> u];
 together with [ap_fmap] recovering [fmap f = ap (pure f)]. The laws are
 stated with [=] at function type, so any instance discharging them under
 this layer's pointwise-equality morphisms relies on the pre-existing
 functional_extensionality axiom of Instance/Coq.v; the class itself adds
 none, and is consistent (e.g. the identity functor instantiates it with no
 axioms). This file declares no concrete instances. 

 --------
 nLab:  https://ncatlab.org/nlab/show/applicative+functor 
 维基百科:  https://en.wikipedia.org/wiki/Applicative_functor 

 在 COQ 上的一个适用函子（Haskell 意义上的）是一个函子
 [F : Coq ⟶ Coq] ，配备了 [pure : a → F a] ，用于注入一个值，以及
 [ap : F (a → b) → F a → F b] （Haskell 的 [<*>]），将封装的函数应用到封装的参数。
 从范畴的角度来看，这正是 COQ 上的一个强松单幺函子，它具有笛卡尔单幺结构（张量 [×]，单位 [unit]）：[pure] 提供单位 [η : 1 → F 1]，[ap] 提供松化子 [μ : F x ⊗ F y → F (x ⊗ y)]，下面的四条律是松单幺的一致性公理。CoqApplicative 最后的被注释掉的开发部分具体勾勒了这一等价关系。与 Theory/Coq/Applicative.v 中的参数类不同（该类仅包含 [pure] 和 [ap]，将合法性作为每个实例的责任），此处的定义将四条适用性定律作为类字段捆绑在一起，以 COQ 同态上的逐点 Leibniz 方程形式陈述：
 ap_id           [pure id <*> v = v] ;
 ap_comp         [pure (∘) <*> u <*> v <*> w = u <*> (v <*> w)] ;
 ap_homo         [pure f <*> pure x = pure (f x)] ;
 ap_interchange  [u <*> pure y = pure (λ g, g y) <*> u] ;
 同时包括 [ap_fmap] 用以恢复 [fmap f = ap (pure f)]。定律在函数类型上以 [=] 形式陈述，因此任何在此层的逐点相等同态下解决它们的实例，都依赖于 Instance/Coq.v 中预先存在的 functional_extensionality 公理；该类本身不增加任何公理，并且是一致的（例如，恒等函子可在不需要任何公理的情况下实例化该类）。此文件未声明任何具体实例。
*)

Section Applicative.

Context `{F : Coq ⟶ Coq}.

Reserved Notation "f <*> g" (at level 29, left associativity).

Class Applicative := {
  pure : ∀ {a : Type}, a → F a;
  ap   : ∀ {a b : Type}, F (a → b) → F a → F b
    where "F <*> g" := (ap F g);

  ap_id : ∀ a : Type, ap (pure (@id Coq a)) = id;
  ap_comp : ∀ (a b c : Type) (v : F (a → b)) (u : F (b → c)) (w : F a),
    pure (fun F g x => F (g x)) <*> u <*> v <*> w = u <*> (v <*> w);
  ap_homo : ∀ (a b : Type) (x : a) (F : a → b),
    pure F <*> pure x = pure (F x);
  ap_interchange : ∀ (a b : Type) (y : a) (u : F (a → b)),
    u <*> pure y = pure (fun F => F y) <*> u;

  ap_fmap : ∀ (a b : Type) (f : a → b),
    ap (pure f) = @fmap _ _ F _ _ f
}.

End Applicative.

Arguments pure {F _ _} _.
Arguments ap   {F _ _ _} _ x.

Coercion Applicative_Functor `{@Applicative F} : Coq ⟶ Coq := F.

Notation "pure[ F ]" := (@pure F _ _) (at level 0, F at next level).
Notation "pure[ F G ]" := (@pure (fun x => F (G x)) _ _) (at level 0).

Notation "ap[ F ]" := (@ap F _ _ _) (at level 0).
Notation "ap[ F G ]" := (@ap (fun x => F (G x)) _ _ _) (at level 0).

Infix "<*>" := ap (at level 29, left associativity).
Notation "x <**> F" := (ap F x) (at level 29, left associativity).
Notation "x <**[ F ]> f" := (@ap F _ _ _ f x) (at level 29, left associativity).
Infix "<*[ F ]>" :=
  (@ap F _ _ _) (at level 29, left associativity, only parsing).

Notation "[| F x y .. z |]" := (.. (F <$> x <*> y) .. <*> z)
    (at level 9, left associativity, F at level 9,
     x at level 9, y at level 9, z at level 9, only parsing).

Definition liftA2 `{Applicative} {A B C : Type}
  (f : A → B → C) (x : F A) (y : F B) : F C := ap (fmap[F] f x) y.

Infix "*>" := (liftA2 (const id)) (at level 29, left associativity).
Infix "<*" := (liftA2 const) (at level 29, left associativity).

Section CoqApplicative.

Context {F : Coq ⟶ Coq}.
Context {J : @Applicative F}.

(* Every Applicative endofunctor on Coq is a strong lax monoidal functor. / 在 Coq 上的每个应用函子端函子都是强松单子函子。 *)

(* Program Definition Coq_Product_Monoidal : @Monoidal Coq := / 程序定义 Coq_Product_Monoidal : @Monoidal Coq := *)
(* @Product_Monoidal Coq Coq_Cartesian Coq_Terminal. / @Product_Monoidal Coq Coq_Cartesian Coq_Terminal. *)

(*
   Program Definition Coq_Product_Monoidal : @Monoidal Coq := {|
   tensor :=
   {| fobj := fun x : Type =>
   {| fobj := fun y : Type => x * y
   ; fmap := fun _ _ f x => (fst x, f (snd x)) |}
   ; fmap := fun _ _ f =>
   {| transform := _ |} |};
   I  := unit : Type
   |}.
   Next Obligation. proper; congruence. Qed.
   Next Obligation.
   proper.
   destruct x0.
   unfold Coq_Product_Monoidal_obligation_4.
   congruence.
   Qed.
   Next Obligation.
   isomorphism.
   - exact snd.
   - exact (fun x => (tt, x)).
   - reflexivity.
   - destruct x, u; reflexivity.
   Qed.
   Next Obligation.
   isomorphism.
   - exact fst.
   - exact (fun x => (x, tt)).
   - reflexivity.
   - destruct x, u; reflexivity.
   Qed.
   Next Obligation. isomorphism; simpl; intros; intuition. Qed.

   Program Definition applicative_is_strong :
   @StrongFunctor Coq Coq_Product_Monoidal F := {|
   strength := fun _ _ x => fmap[F] (λ y, (fst x, y)) (snd x)
   |}.

   --------
   程序定义 Coq_Product_Monoidal : @Monoidal Coq := {|
   tensor :=
   {| fobj := fun x : Type =>
   {| fobj := fun y : Type => x * y
   ; fmap := fun _ _ f x => (fst x, f (snd x)) |}
   ; fmap := fun _ _ f =>
   {| transform := _ |} |};
   I  := unit : Type
   |}.
   Next Obligation. proper; congruence. Qed.
   Next Obligation.
   proper.
   destruct x0.
   unfold Coq_Product_Monoidal_obligation_4.
   congruence.
   Qed.
   Next Obligation.
   isomorphism.
   - exact snd.
   - exact (fun x => (tt, x)).
   - reflexivity.
   - destruct x, u; reflexivity.
   Qed.
   Next Obligation.
   isomorphism.
   - exact fst.
   - exact (fun x => (x, tt)).
   - reflexivity.
   - destruct x, u; reflexivity.
   Qed.
   Next Obligation. isomorphism; simpl; intros; intuition. Qed.程序定义 applicative_is_strong :
   @StrongFunctor Coq Coq_Product_Monoidal F := {|
   strength := fun _ _ x => fmap [F]  (λ y, (fst x, y)) (snd x)
   |}。
*)

(*
   Program Definition Coq_Product_Monoidal_F : @Monoidal Coq := {|
   tensor :=
   {| fobj := fun x : Type =>
   {| fobj := fun y : Type => F x * F y
   ; fmap := fun _ _ f x => (fst x, fmap[F] f (snd x)) |}
   ; fmap := fun _ _ f =>
   {| transform := _ |} |};
   I  := F (unit : Type)
   |}.
   Next Obligation.
   proper; simpl.
   f_equiv.
   pose proof (@fmap_respects _ _ F X0 y x y); simpl in X1.
   apply X1, H.
   Qed.
   Next Obligation.
   proper; simpl.
   f_equiv.
   pose proof (@fmap_id _ _ F X0); simpl in X1.
   apply X1.
   Qed.
   Next Obligation.
   proper; simpl.
   f_equiv.
   pose proof (@fmap_comp _ _ F x0 y z); simpl in X1.
   apply X1.
   Qed.
   Next Obligation.
   intuition.
   apply (fmap[F] f); assumption.
   Qed.

   --------
   程序定义 Coq_Product_Monoidal_F : @Monoidal Coq := {|
   tensor :=
   {| fobj := fun x : Type =>
   {| fobj := fun y : Type => F x * F y
   ; fmap := fun _ _ f x => (fst x, fmap [F]  f (snd x)) |}
   ; fmap := fun _ _ f =>
   {| transform := _ |} |};
   I  := F (unit : Type)
   |}。
   Next Obligation.
   proper; simpl.
   f_equiv.
   pose proof (@fmap_respects _ _ F X0 y x y); simpl in X1.
   apply X1, H.
   Qed.
   Next Obligation.
   proper; simpl.
   f_equiv.
   pose proof (@fmap_id _ _ F X0); simpl in X1.
   apply X1.
   Qed.
   Next Obligation.
   proper; simpl.
   f_equiv.
   pose proof (@fmap_comp _ _ F x0 y z); simpl in X1.
   apply X1.
   Qed.
   Next Obligation.
   intuition.
   apply (fmap [F]  f); assumption.
   Qed.
*)

(* Definition applicative_is_lax : / 定义 applicative_is_lax ： *)
(* @LaxMonoidalFunctor Coq Coq Coq_Product_Monoidal Coq_Product_Monoidal_F F := {| / @LaxMonoidalFunctor Coq Coq Coq_Product_Monoidal Coq_Product_Monoidal_F F := {| *)
(* pure := fun _ => @I Coq Coq_Product_Monoidal_F; / pure := fun _ => @I Coq Coq_Product_Monoidal_F; *)
(* ap_functor_nat := _ / ap_functor_nat := _ *)
(* |}. *)

(* Theorem applicative_is_strong_lax : / 定理 applicative_is_strong_lax ： *)
(* StrongLaxMonoidalFunctor Coq Product_Monoidal F / StrongLaxMonoidal函子 Coq Product_Monoidal F *)
(* applicative_is_strong applicative_is_lax. / applicative 是强的 applicative 是松的。 *)

End CoqApplicative.
