Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Coq.Functor.Proofs.
Require Import Category.Theory.Coq.Applicative.Proofs.
Require Import Category.Theory.Coq.Monad.Proofs.
Require Import Category.Theory.Coq.Maybe.

Generalizable All Variables.

(** Law proofs for the Maybe/option [1 + a] instances / 用于 Maybe/option [1 + a] 实例的定律证明 *)

(*
nLab: https://ncatlab.org/nlab/show/maybe+monad
   Wikipedia: https://en.wikipedia.org/wiki/Option_type

   The instances themselves live in [Theory/Coq/Maybe.v]; here we record their
   lawfulness.  The final [Maybe_Functor : IsFunctor] discharges the two functor
   laws -- identity [fmap id = id] and composition [fmap (g ∘ f) = fmap g ∘ fmap f]
   -- by exhibiting the operation as a genuine endofunctor on [Coq] (an
   [AFunctor]), exactly as the sibling [Either] and [Tuple] proof files do.

   The preceding lemmas are characterisation (“spec”) lemmas describing each
   operation by its action on [Just]/[Nothing].  They make precise the equations
   the sources give for the functor/applicative/monad/Alternative structure --
   [fmap f Nothing = Nothing], [Just f <*> Just x = Just (f x)],
   [Nothing >>= f = Nothing], [Just x >>= f = f x], left-biased [<|>] -- as
   biconditionals on when a result is [Just x] versus [Nothing].

--------
nLab: https://ncatlab.org/nlab/show/maybe+monad
   维基百科: https://en.wikipedia.org/wiki/Option_type

   实例本身存在于 [Theory/Coq/Maybe.v]；在这里我们记录它们的合法性。最终的 [Maybe_Functor : IsFunctor] 通过展示该操作作为 [Coq]（一个 [AFunctor]）上的真正 Endofunctor，从而满足两个函子律 —— 单位 [fmap id = id] 和复合 [fmap (g ∘ f) = fmap g ∘ fmap f] —— 正如其兄弟文件 [Either] 和 [Tuple] 所做的证明一样。

   前面的引理是表征（“规范”）引理，通过其在 [Just]/[Nothing] 上的作用描述每个操作。它们精确指出了来源中给出的函子/可应用/Monad/Alternative 结构的方程 —— [fmap f Nothing = Nothing]、[Just f <*> Just x = Just (f x)]、[Nothing >>= f = Nothing]、[Just x >>= f = f x]、左偏 [<|>] —— 作为结果是 [Just x] 还是 [Nothing] 的双条件等式。
*)

Import MonadNotations.

(* [<|>] (left-biased choice) returns a [Just] iff either operand does. / [<|>]（左偏选择）仅当任一操作数返回 [Just] 时才返回 [Just]。 *)

Lemma Maybe_choose_spec {a} {x y : Maybe a} :
  isJust (x <|> y) = (isJust x || isJust y)%bool.
Proof.
  destruct x; auto.
Qed.

(* Functor: [fmap f m] is [Just x] exactly when [m = Just y] and [x = f y]. / 函子：[fmap f m] 当且仅当 [m = Just y] 和 [x = f y] 时为 [Just x]。 *)
Lemma fmap_endo_just {c} (f : c → c) (m : Maybe c) (x : c) :
  f <$> m = Just x <-> exists y, x = f y /\ m = Just y.
Proof.
  induction m; simpl; split; intros.
  - inversion_clear H.
    eexists; eauto.
  - destruct H, H; subst.
    now inversion_clear H0.
  - discriminate.
  - destruct H, H; discriminate.
Qed.

Lemma fmap_endo_nothing {c} (f : c → c) (m : Maybe c) :
  f <$> m = Nothing <-> m = Nothing.
Proof. induction m; simpl; intuition auto; discriminate. Qed.

(*
Applicative: [f <$> m <*> n] is [Just x] exactly when both arguments are
   [Just] and [x] is their combination.

--------
应用程序：当且仅当两个参数都是 [Just] 且 [x] 是它们的组合时，[f <$> m <*> n] 就是 [Just x]。
*)
Lemma ap_endo_just {c} (f : c → c → c) (m n : Maybe c) (x : c) :
  f <$> m <*> n = Just x
    <-> exists y z, x = f y z /\ m = Just y /\ n = Just z.
Proof.
  induction m, n; simpl; split; intros.
  - inversion_clear H.
    eexists; eauto.
  - destruct H, H, H, H0; subst.
    inversion_clear H0.
    now inversion_clear H1.
  - discriminate.
  - destruct H, H, H, H0; discriminate.
  - discriminate.
  - destruct H, H, H, H0; discriminate.
  - discriminate.
  - destruct H, H, H, H0; discriminate.
Qed.

Lemma ap_endo_nothing {c} (f : c → c → c) (m n : Maybe c) :
  f <$> m <*> n = Nothing <-> m = Nothing \/ n = Nothing.
Proof. induction m, n; simpl; intuition auto; discriminate. Qed.

(* Monad: [m >>= f] is [Just x] exactly when [m = Just y] and [f y = Just x]. / Monad：[m >>= f] 当且仅当 [m = Just y] 和 [f y = Just x] 时是 [Just x]。 *)
Lemma bind_endo_just {c} (f : c → Maybe c) (m : Maybe c) (x : c) :
  m >>= f = Just x <-> exists y, f y = Just x /\ m = Just y.
Proof.
  induction m; simpl; split; intros.
  - destruct (f a) eqn:?.
    + inversion H; subst.
      now eexists; eauto.
    + unfold bind in H.
      simpl in H.
      congruence.
  - destruct H, H.
    inversion H0; subst.
    now unfold bind; simpl.
  - discriminate.
  - destruct H, H.
    discriminate.
Qed.

Lemma bind_endo_nothing {c} (f : c → Maybe c) (m : Maybe c) :
  m >>= f = Nothing <-> m = Nothing \/ exists y, f y = Nothing /\ m = Just y.
Proof.
  induction m; simpl; split; intros.
  - destruct (f a) eqn:?.
    + unfold bind in H; simpl in H.
      congruence.
    + right.
      now eexists; eauto.
  - destruct H.
    + discriminate.
    + firstorder eauto.
      inversion_clear H0.
      now unfold bind; simpl.
  - now left.
  - reflexivity.
Qed.

(*
Alternative: [m <|> n] is [Just x] via the left operand, or via the right
   when the left is [Nothing] (left-biased choice).

--------
替代：[m <|> n] 是通过左操作数的 [Just x]，或者当左操作数是 [Nothing] 时通过右操作数（左偏选择）。
*)
Lemma alt_endo_just {c} (m n : Maybe c) (x : c) :
  m <|> n = Just x <-> m = Just x \/ (m = Nothing /\ n = Just x).
Proof. induction m; simpl; intuition auto; discriminate. Qed.

Lemma alt_endo_nothing {c} (m n : Maybe c) :
  m <|> n = Nothing <-> m = Nothing /\ n = Nothing.
Proof. induction m, n; simpl; intuition auto; discriminate. Qed.

(*
The lawful functor instance: [Maybe] is a genuine endofunctor on [Coq],
   discharging the identity and composition functor laws.  (The name reuses the
   source [Maybe_Functor] instance, as in the [Either]/[Tuple] proof files.)

--------
合法的函子实例：[Maybe] 是 [Coq] 上的一个真正的自函子，满足恒等函子和组合函子定律。（该名称重用了源 [Maybe_Functor] 实例，如 [Either]/[Tuple] 证明文件中所示。）
*)
Program Definition Maybe_Functor : IsFunctor Maybe_Functor := {|
  a_fmap := Maybe_Functor;
|}.
Next Obligation.
  proper.
  destruct x1; simpl; auto.
  now rewrite H.
Qed.
Next Obligation.
  now destruct x0.
Qed.
Next Obligation.
  now destruct x0.
Qed.
