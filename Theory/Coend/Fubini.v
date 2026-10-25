Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.End.
Require Import Category.Structure.Coend.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Coend.

Generalizable All Variables.

(**
* Fubini / interchange for coends, in [Sets]

    SCOPE.  This file establishes the Fubini isomorphism [coend_fubini]
    [∫^{(c,d)} H ≅ ∫^c ∫^d H] for a [Sets]-valued integrand
    [H : (C ∏ D)^op ∏ (C ∏ D) ⟶ Sets], built on the concrete [Sets] coend
    [SetsCoend] of [Instance/Sets/Coend] (the funext-free inductive quotient).
    The abstract interchange theorem for coends valued in an arbitrary
    cocomplete category — which needs a supply of coends and their universal
    property at the target, rather than the by-hand [Sets] construction used
    here — is deferred (ledger 6).

--------
* Fubini / 对coends的互换，在 [Sets]中

范围。 该文件建立了Fubini同构 [coend_fubini]
[∫^{(c,d)} H ≅ ∫^c ∫^d H] 对一个 [Sets]-值的被积函数
[H : (C ∏ D)^op ∏ (C ∏ D) ⟶ Sets]，基于具体的 [Sets] coend
[SetsCoend] 来自 [Instance/Sets/Coend]（无funext的归纳商）。
在任意完备余范畴中取值的coends的抽象互换定理——它需要在目标处提供coends及其范畴论性质，而不是此处使用的手工 [Sets] 构造——将被推迟（账册6）。
*)

(** Element-level readings of the functor laws for a [Sets]-valued functor. / [Sets] 值函子函子定律的元素级解读。 *)
Local Lemma fmap_id_app {K : Category} (G : K ⟶ Sets) {x : K} (z : G x) :
  fmap[G] (@id K x) z ≈ z.
Proof. exact (@fmap_id K Sets G x z). Qed.

Local Lemma fmap_comp_app {K : Category} (G : K ⟶ Sets) {x y z : K}
  (g : y ~{K}~> z) (f : x ~{K}~> y) (w : G x) :
  fmap[G] (g ∘ f) w ≈ fmap[G] g (fmap[G] f w).
Proof. exact (@fmap_comp K Sets G x y z g f w). Qed.

(**
Collapse a two-fold [fmap] into a single one along a morphism equality:
    the workhorse for the coend bookkeeping below.

--------
将一个二重 [fmap] 沿着一个态射等式折叠成一个：下面用于余端记账的主要工具。
*)
Local Lemma fmap_two {K : Category} (G : K ⟶ Sets) {x y z : K}
  (m1 : y ~{K}~> z) (m2 : x ~{K}~> y) (m3 : x ~{K}~> z)
  (Hm : m1 ∘ m2 ≈ m3) (w : G x) :
  fmap[G] m1 (fmap[G] m2 w) ≈ fmap[G] m3 w.
Proof.
  transitivity (fmap[G] (m1 ∘ m2) w).
  - symmetry; apply fmap_comp_app.
  - exact (@fmap_respects _ _ G _ _ (m1 ∘ m2) m3 Hm w).
Qed.

Section Fubini.

Context {C D : Category}.
Context (H : (C ∏ D)^op ∏ (C ∏ D) ⟶ Sets).

(**
The inner integrand at fixed [c1 c2 : C]: the [D]-profunctor
    [(d1, d2) ↦ H ((c1, d1), (c2, d2))], contravariant in [d1], covariant in
    [d2], obtained by holding the [C]-coordinates fixed at [c1], [c2].

--------
在固定 [c1 c2 : C] 时的内部被积函数：[D]-仿函子 [(d1, d2) ↦ H ((c1, d1), (c2, d2))]，对 [d1] 是逆变的，对 [d2] 是协变的，通过将 [C] 坐标固定在 [c1]、[c2] 得到。
*)
(**
The action of [H] on a "rectangle" of moves: a contravariant [C]-move [u],
    a covariant [C]-move [v], a contravariant [D]-move [g1] and a covariant
    [D]-move [g2], with every object explicit so that no projection sits inside
    the morphism literal (which is what makes Coq insert [eq_rect] transports).
    This single engine drives every functorial action below; the inner coend
    fixes [u], [v] at identities, the [Inner] functor fixes [g1], [g2] at
    identities, and every composition collapses through [Hact_comp].

--------
[H] 对于一组“矩形”变换的作用：一个逆变的 [C]-变换 [u]， 一个协变的 [C]-变换 [v]，一个逆变的 [D]-变换 [g1] 和一个协变的 [D]-变换 [g2]，其中每个对象都是显式的，以便没有投影嵌入在态射字面量中（这就是 Coq 插入 [eq_rect] 传输的原因）。 这个单一的引擎驱动下面的每个函子作用； 内部共端固定 [u]，[v] 为恒等映射，[Inner] 函子固定 [g1]，[g2] 为恒等映射，并且每个组合都通过 [Hact_comp] 折叠。
*)
Definition Hact (c1 c2 c1' c2' : C) (d1 d2 d1' d2' : D)
  (u : c1' ~{C}~> c1) (v : c2 ~{C}~> c2')
  (g1 : d1' ~{D}~> d1) (g2 : d2 ~{D}~> d2') :
  H ((c1, d1), (c2, d2)) ~{Sets}~> H ((c1', d1'), (c2', d2')) :=
  fmap[H] (((u, g1), (v, g2))
             : ((c1, d1), (c2, d2))
                 ~{(C ∏ D)^op ∏ (C ∏ D)}~> ((c1', d1'), (c2', d2'))).

(** [Hact] at all identities is the identity of [H]. / [Hact] 在所有恒等中都是 [H] 的恒等。 *)
Lemma Hact_id (c1 c2 : C) (d1 d2 : D) (w : H ((c1, d1), (c2, d2))) :
  Hact c1 c2 c1 c2 d1 d2 d1 d2
    (@id C c1) (@id C c2) (@id D d1) (@id D d2) w ≈ w.
Proof. exact (fmap_id_app H w). Qed.

(** [Hact] respects [≈] in all four morphism arguments. / [Hact] 在所有四个同态参数中尊重 [≈]。 *)
Lemma Hact_respects (c1 c2 c1' c2' : C) (d1 d2 d1' d2' : D)
  (u u' : c1' ~{C}~> c1) (v v' : c2 ~{C}~> c2')
  (g1 g1' : d1' ~{D}~> d1) (g2 g2' : d2 ~{D}~> d2')
  (Hu : u ≈ u') (Hv : v ≈ v') (Hg1 : g1 ≈ g1') (Hg2 : g2 ≈ g2')
  (w : H ((c1, d1), (c2, d2))) :
  Hact c1 c2 c1' c2' d1 d2 d1' d2' u v g1 g2 w
    ≈ Hact c1 c2 c1' c2' d1 d2 d1' d2' u' v' g1' g2' w.
Proof.
  unfold Hact.
  refine (@fmap_respects _ _ H _ _ _ _ _ w).
  split; split; simpl; assumption.
Qed.

(**
Composing two [Hact]s collapses to a single one: the contravariant legs
    ([u], [g1]) compose reversed (they live in the opposite factors, which is
    definitional), the covariant legs ([v], [g2]) forwards.

--------
将两个 [Hact] 组合会折叠为一个：逆变部分（[u], [g1]）以相反顺序组合（它们存在于相反的因子中，这是定义性的），协变部分（[v], [g2]）则向前组合。
*)
Lemma Hact_comp (c1 c2 c1' c2' c1'' c2'' : C) (d1 d2 d1' d2' d1'' d2'' : D)
  (u : c1' ~{C}~> c1) (v : c2 ~{C}~> c2')
  (u' : c1'' ~{C}~> c1') (v' : c2' ~{C}~> c2'')
  (g1 : d1' ~{D}~> d1) (g2 : d2 ~{D}~> d2')
  (g1' : d1'' ~{D}~> d1') (g2' : d2' ~{D}~> d2'')
  (w : H ((c1, d1), (c2, d2))) :
  Hact c1' c2' c1'' c2'' d1' d2' d1'' d2'' u' v' g1' g2'
    (Hact c1 c2 c1' c2' d1 d2 d1' d2' u v g1 g2 w)
    ≈ Hact c1 c2 c1'' c2'' d1 d2 d1'' d2''
        (u ∘ u') (v' ∘ v) (g1 ∘ g1') (g2' ∘ g2) w.
Proof.
  unfold Hact.
  apply fmap_two.
  reflexivity.
Qed.

(**
A [Hact_comp] variant that also rewrites the four composed morphisms to
    chosen targets, so callers can absorb the identity laws in one step.

--------
一种 [Hact_comp] 变体，它还将四个复合的态射重写到选定的目标，因此调用者可以在一步中吸收恒等律。
*)
Lemma Hact_comp_clean (c1 c2 c1' c2' c1'' c2'' : C)
  (d1 d2 d1' d2' d1'' d2'' : D)
  (u : c1' ~{C}~> c1) (v : c2 ~{C}~> c2')
  (u' : c1'' ~{C}~> c1') (v' : c2' ~{C}~> c2'')
  (g1 : d1' ~{D}~> d1) (g2 : d2 ~{D}~> d2')
  (g1' : d1'' ~{D}~> d1') (g2' : d2' ~{D}~> d2'')
  (uu : c1'' ~{C}~> c1) (vv : c2 ~{C}~> c2'')
  (gg1 : d1'' ~{D}~> d1) (gg2 : d2 ~{D}~> d2'')
  (Hu : u ∘ u' ≈ uu) (Hv : v' ∘ v ≈ vv)
  (Hg1 : g1 ∘ g1' ≈ gg1) (Hg2 : g2' ∘ g2 ≈ gg2)
  (w : H ((c1, d1), (c2, d2))) :
  Hact c1' c2' c1'' c2'' d1' d2' d1'' d2'' u' v' g1' g2'
    (Hact c1 c2 c1' c2' d1 d2 d1' d2' u v g1 g2 w)
    ≈ Hact c1 c2 c1'' c2'' d1 d2 d1'' d2'' uu vv gg1 gg2 w.
Proof.
  transitivity (Hact c1 c2 c1'' c2'' d1 d2 d1'' d2''
                  (u ∘ u') (v' ∘ v) (g1 ∘ g1') (g2' ∘ g2) w).
  - apply Hact_comp.
  - apply Hact_respects; assumption.
Qed.

(**
The inner integrand at fixed [c1 c2 : C]: the [D]-profunctor
    [(d1, d2) ↦ H ((c1, d1), (c2, d2))], its functorial action being [Hact]
    with the [C]-coordinates held at identities.

--------
在固定 [c1 c2 : C] 时的内部积分项：[D]-双函子 [(d1, d2) ↦ H ((c1, d1), (c2, d2))]，其函子作用为 [Hact]，并且 [C] 坐标保持为恒等映射。
*)
Program Definition InnerIntegrand (c1 c2 : C) : D^op ∏ D ⟶ Sets := {|
  fobj := fun dp => H ((c1, fst dp), (c2, snd dp));
  fmap := fun dp dq g =>
    Hact c1 c2 c1 c2 (fst dp) (snd dp) (fst dq) (snd dq)
      (@id C c1) (@id C c2) (fst g) (snd g)
|}.
Next Obligation.
  unfold Proper, respectful; intros g g' [Hg1 Hg2] x.
  apply Hact_respects; try reflexivity; assumption.
Qed.
Next Obligation. apply Hact_id. Qed.
Next Obligation.
  transitivity (Hact c1 c2 c1 c2 o3 o4 o o0
                  (id ∘ id) (id ∘ id) (h ∘ h1) (h2 ∘ h0) x0).
  - apply Hact_respects;
      [ symmetry; apply id_left | symmetry; apply id_left
      | reflexivity | reflexivity ].
  - symmetry; apply Hact_comp.
Qed.

(**
The leg at [d] of the [Inner]-functorial action of a [C]-move [(u, v)]:
    apply the [C]-move by [Hact] (identities on the [D]-coordinate) and inject
    into the inner coend at [c1', c2'].

--------
在 [d] 的 [Inner]-函子作用的 [C]-移动 [(u, v)] 的腿：
    通过 [Hact]（在 [D] 坐标上的恒等）应用 [C]-移动并注入到 [c1', c2'] 的内部共端中。
*)
Program Definition outer_leg (c1 c2 c1' c2' : C)
  (u : c1' ~{C}~> c1) (v : c2 ~{C}~> c2') (d : D) :
  SetoidMorphism (InnerIntegrand c1 c2 (d, d))
                 (coend_apex_setoid (InnerIntegrand c1' c2')) :=
  {| morphism := fun w =>
       ci (InnerIntegrand c1' c2') d
         (Hact c1 c2 c1' c2' d d d d u v (@id D d) (@id D d) w) |}.
Next Obligation.
  unfold Proper, respectful; intros w w' Hww'.
  apply ce_point.
  apply proper_morphism; exact Hww'.
Qed.

Lemma outer_leg_cond (c1 c2 c1' c2' : C)
  (u : c1' ~{C}~> c1) (v : c2 ~{C}~> c2') :
  Cowedge_cond (InnerIntegrand c1 c2)
    (coend_apex_setoid (InnerIntegrand c1' c2'))
    (outer_leg c1 c2 c1' c2' u v).
Proof.
  unfold Cowedge_cond; intros x y f a; simpl.
  (*
The two nested [Hact]s collapse to the [InnerIntegrand c1' c2'] cowedge
     legs applied to [w''], and the middle step is that coend's own glue.

--------
两个嵌套的 [Hact] 倒塌到 [InnerIntegrand c1' c2'] 牛楔腿上，应用于 [w'']，中间步骤是该接头自身的胶水。
*)
  pose (w'' := Hact c1 c2 c1' c2' y x y x u v (@id D y) (@id D x) a).
  apply (ce_trans (InnerIntegrand c1' c2') _
           (ci (InnerIntegrand c1' c2') x
              (Hact c1' c2' c1' c2' y x x x
                 (@id C c1') (@id C c2') (op f) (@id D x) w''))).
  { apply ce_point.
    transitivity (Hact c1 c2 c1' c2' y x x x u v (op f) (@id D x) a).
    - apply Hact_comp_clean;
        [ apply id_left | apply id_right | apply id_right | apply id_left ].
    - symmetry; apply Hact_comp_clean;
        [ apply id_right | apply id_left | apply id_left | apply id_left ]. }
  apply (ce_trans (InnerIntegrand c1' c2') _
           (ci (InnerIntegrand c1' c2') y
              (Hact c1' c2' c1' c2' y x y y
                 (@id C c1') (@id C c2') (@id D y) f w''))).
  { exact (ce_glue (InnerIntegrand c1' c2') x y f w''). }
  apply ce_point.
  transitivity (Hact c1 c2 c1' c2' y x y y u v (@id D y) f a).
  - apply Hact_comp_clean;
      [ apply id_right | apply id_left | apply id_left | apply id_right ].
  - symmetry; apply Hact_comp_clean;
      [ apply id_left | apply id_right | apply id_left | apply id_left ].
Qed.

(**
The [Inner]-functorial action of a [C]-move as the coend mediator of the
    legs above.

--------
作为上述腿的余端中介，[C]-移动的 [Inner]-函子作用。
*)
Definition inner_fmap (c1 c2 c1' c2' : C)
  (u : c1' ~{C}~> c1) (v : c2 ~{C}~> c2') :
  coend_apex_setoid (InnerIntegrand c1 c2)
    ~{Sets}~> coend_apex_setoid (InnerIntegrand c1' c2') :=
  coend_mediator (InnerIntegrand c1 c2)
    (outer_leg c1 c2 c1' c2' u v) (outer_leg_cond c1 c2 c1' c2' u v).

(** Computation rule of the mediator on a generator (definitional). / 介体在生成元上的计算规则（定义性）。 *)
Lemma inner_fmap_ci (c1 c2 c1' c2' : C)
  (u : c1' ~{C}~> c1) (v : c2 ~{C}~> c2') (d : D)
  (w : H ((c1, d), (c2, d))) :
  inner_fmap c1 c2 c1' c2' u v (ci (InnerIntegrand c1 c2) d w)
    ≈ ci (InnerIntegrand c1' c2') d
        (Hact c1 c2 c1' c2' d d d d u v (@id D d) (@id D d) w).
Proof. reflexivity. Qed.

(**
The iterated-coend functor [Inner (c1, c2) = ∫^d H ((c1, d), (c2, d))],
    contravariant in [c1], covariant in [c2].

--------
迭代余积函子 [Inner (c1, c2) = ∫^d H ((c1, d), (c2, d))]，在 [c1] 上是逆变的，在 [c2] 上是协变的。
*)
Program Definition Inner : C^op ∏ C ⟶ Sets := {|
  fobj := fun p => coend_apex_setoid (InnerIntegrand (fst p) (snd p));
  fmap := fun p q uv =>
    inner_fmap (fst p) (snd p) (fst q) (snd q) (fst uv) (snd uv)
|}.
Next Obligation.
  unfold Proper, respectful; intros uv uv' [Huv1 Huv2].
  apply (coend_med_eq (SetsCoend (InnerIntegrand o1 o2))
           (coend_apex_setoid (InnerIntegrand o o0))
           (outer_leg o1 o2 o o0 (fst uv') (snd uv'))
           (outer_leg_cond o1 o2 o o0 (fst uv') (snd uv'))).
  - intros d w.
    transitivity (ci (InnerIntegrand o o0) d
                    (Hact o1 o2 o o0 d d d d (fst uv) (snd uv)
                       (@id D d) (@id D d) w)).
    + apply inner_fmap_ci.
    + apply ce_point.
      apply Hact_respects; [ exact Huv1 | exact Huv2 | reflexivity | reflexivity ].
  - intros d w.
    apply inner_fmap_ci.
Qed.
Next Obligation.
  destruct x0 as [d w].
  apply ce_point.
  apply Hact_id.
Qed.
Next Obligation.
  destruct x0 as [d w].
  apply ce_point.
  symmetry.
  apply Hact_comp_clean;
    [ reflexivity | reflexivity | apply id_left | apply id_left ].
Qed.

(**
The diagonal contravariant image [bimap[H] (op (u,g)) id] in [Hact] form;
    a definitional identity, phrased with an explicit hom annotation so the pair
    [(u, g)] elaborates as a [C ∏ D] morphism rather than a bare product.

--------
对角逆变像 [bimap[H] (op (u,g)) id] 在 [Hact] 形式中；一种定义性恒等式，用显式 hom 注解表达，因此该对 [(u, g)] 被阐释为 [C ∏ D] 射而不是裸积。
*)
Local Lemma bimap_diag (c1 c2 : C) (d1 d2 : D)
  (u : c1 ~{C}~> c2) (g : d1 ~{D}~> d2) (w : H ((c2, d2), (c1, d1))) :
  bimap[H] (op ((u, g) : (c1, d1) ~{C ∏ D}~> (c2, d2))) (id, id) w
    ≈ Hact c2 c1 c1 c1 d2 d1 d1 d1 u (@id C c1) g (@id D d1) w.
Proof. reflexivity. Qed.

(** The diagonal covariant image [bimap[H] id (op-free) (u,g)] in [Hact] form. / 对角协变图像 [bimap[H] id (无操作) (u,g)] 以 [Hact] 形式。 *)
Local Lemma bimap_codiag (c1 c2 : C) (d1 d2 : D)
  (u : c1 ~{C}~> c2) (g : d1 ~{D}~> d2) (w : H ((c2, d2), (c1, d1))) :
  bimap[H] (id, id) ((u, g) : (c1, d1) ~{C ∏ D}~> (c2, d2)) w
    ≈ Hact c2 c1 c2 c2 d2 d1 d2 d2 (@id C c2) u (@id D d2) g w.
Proof. reflexivity. Qed.

(** ** The Fubini comparison [∫^{(c,d)} H ≅ ∫^c ∫^d H] / ** Fubini 比较 [∫^{(c,d)} H ≅ ∫^c ∫^d H] *)

(**
Forward leg at [(c, d)]: [h ↦ ci c (ci d h)] (outer over [C] of inner over
    [D]).

--------
在 [(c, d)] 的前腿：[h ↦ ci c (ci d h)]（外侧覆盖 [C]，内侧覆盖 [D]）。
*)
Program Definition fwd_leg (cd : C ∏ D) :
  SetoidMorphism (H (cd, cd)) (coend_apex_setoid Inner) :=
  match cd as cd0
    return SetoidMorphism (H (cd0, cd0)) (coend_apex_setoid Inner) with
  | (c, d) =>
      {| morphism := fun h => ci Inner c (ci (InnerIntegrand c c) d h) |}
  end.
Next Obligation.
  unfold Proper, respectful; intros h h' Hh.
  apply ce_point; apply ce_point; exact Hh.
Qed.

Lemma fwd_cond : Cowedge_cond H (coend_apex_setoid Inner) fwd_leg.
Proof.
  unfold Cowedge_cond; intros x y f a.
  destruct x as [c1 d1], y as [c2 d2], f as [fc fd]; simpl.
  (* The two witnesses moving [a] partway around the square. / 两名目击者将 [a] 移动到广场周围的一部分。 *)
  pose (b1 := Hact c2 c1 c1 c1 d2 d1 d2 d1 fc (@id C c1) (@id D d2) (@id D d1) a).
  pose (a2 := Hact c2 c1 c2 c1 d2 d1 d2 d2 (@id C c2) (@id C c1) (@id D d2) fd a).
  (* Step 1: rewrite the diagonal image as the inner [op fd]-image of [b1]. / 步骤1：将对角图像重写为[b1]的内部[op fd]图像。 *)
  apply (ce_trans Inner _
    (ci Inner c1 (ci (InnerIntegrand c1 c1) d1
       (Hact c1 c1 c1 c1 d2 d1 d1 d1 (@id C c1) (@id C c1) fd (@id D d1) b1)))).
  { apply ce_point; apply ce_point.
    rewrite (bimap_diag c1 c2 d1 d2 fc fd a); subst b1; symmetry.
    apply Hact_comp_clean;
      [ apply id_right | apply id_left | apply id_left | apply id_left ]. }
  (* Step 2: the inner [D]-coend glue at [c1] for [fd]. / 步骤 2：在 [c1] 的 [fd] 上涂抹内部 [D]-协同胶。 *)
  apply (ce_trans Inner _
    (ci Inner c1 (ci (InnerIntegrand c1 c1) d2
       (Hact c1 c1 c1 c1 d2 d1 d2 d2 (@id C c1) (@id C c1) (@id D d2) fd b1)))).
  { apply ce_point; exact (ce_glue (InnerIntegrand c1 c1) d1 d2 fd b1). }
  (* Step 3: collapse the inner image to [Z]. / 步骤3：将内部图像折叠到 [Z]。 *)
  apply (ce_trans Inner _
    (ci Inner c1 (ci (InnerIntegrand c1 c1) d2
       (Hact c2 c1 c1 c1 d2 d1 d2 d2 fc (@id C c1) (@id D d2) fd a)))).
  { apply ce_point; apply ce_point; subst b1.
    apply Hact_comp_clean;
      [ apply id_right | apply id_left | apply id_left | apply id_right ]. }
  (* Step 4: exhibit [Z] as the outer [op fc]-image of [ci d2 a2]. / 步骤4：将[Z]展示为[ci d2 a2]的外部[op fc]图像。 *)
  apply (ce_trans Inner _
    (ci Inner c1 (inner_fmap c2 c1 c1 c1 fc (@id C c1)
       (ci (InnerIntegrand c2 c1) d2 a2)))).
  { apply ce_point.
    transitivity (ci (InnerIntegrand c1 c1) d2
                    (Hact c2 c1 c1 c1 d2 d2 d2 d2 fc (@id C c1)
                       (@id D d2) (@id D d2) a2)).
    - apply ce_point; subst a2; symmetry.
      apply Hact_comp_clean;
        [ apply id_left | apply id_left | apply id_left | apply id_left ].
    - symmetry; apply inner_fmap_ci. }
  (* Step 5: the outer [C]-coend glue for [fc]. / 步骤5：用于[fc]的外部[C]共聚物胶。 *)
  apply (ce_trans Inner _
    (ci Inner c2 (inner_fmap c2 c1 c2 c2 (@id C c2) fc
       (ci (InnerIntegrand c2 c1) d2 a2)))).
  { exact (ce_glue Inner c1 c2 fc (ci (InnerIntegrand c2 c1) d2 a2)). }
  (* Step 6: collapse the outer image to [Y]. / 第6步：将外部图像折叠到 [Y]。 *)
  apply ce_point.
  transitivity (ci (InnerIntegrand c2 c2) d2
                  (Hact c2 c1 c2 c2 d2 d2 d2 d2 (@id C c2) fc
                     (@id D d2) (@id D d2) a2)).
  - apply inner_fmap_ci.
  - apply ce_point.
    rewrite (bimap_codiag c1 c2 d1 d2 fc fd a); subst a2.
    apply Hact_comp_clean;
      [ apply id_left | apply id_right | apply id_left | apply id_left ].
Qed.

(** The forward comparison map [∫^{(c,d)} H → ∫^c ∫^d H]. / 前向比较映射 [∫^{(c,d)} H → ∫^c ∫^d H]。 *)
Definition fwd :
  coend_apex_setoid H ~{Sets}~> coend_apex_setoid Inner :=
  coend_mediator H fwd_leg fwd_cond.

(**
Post-composing a coend morphism onto the injections yields a cowedge: the
    legs [fun x => m ∘ coend_inj E] inherit their glue from [E]'s own.

--------
将一个余端态射后合成到注入上会产生一个余楔：腿 [fun x => m ∘ coend_inj E] 从 [E] 自身继承它们的粘合。
*)
Lemma postcompose_cowedge {K : Category} (G : K^op ∏ K ⟶ Sets)
  (E : Coend G) (Q : SetoidObject) (m : coend_obj E ~{Sets}~> Q) :
  Cowedge_cond G Q (fun x => m ∘ @coend_inj K Sets G E x).
Proof.
  intros x y f.
  rewrite <- !comp_assoc, (coend_cowedge E f).
  reflexivity.
Qed.

(**
Backward inner cowedge at [c]: inject [∫^d H((c,d),(c,d))] into [∫ H] by
    landing at index [(c, d)]; the [D]-glue for [g] is [H]'s own glue at the
    pair morphism [(id, g)].

--------
在 [c] 处向后内部牛楔：通过在索引 [(c, d)] 处着陆，将 [∫^d H((c,d),(c,d))] 注入 [∫ H]；[g] 的 [D]-粘合剂是 [H] 在对偶态射 [(id, g)] 处的自身粘合剂。
*)
Lemma bwd_inner_cond (c : C) :
  Cowedge_cond (InnerIntegrand c c) (coend_apex_setoid H)
    (fun d => coend_inj_mor H (c, d)).
Proof.
  intros d1 d2 g a.
  exact (ce_glue H (c, d1) (c, d2) (id, g) a).
Qed.

(**
Backward leg at [c]: the mediator [∫^d H((c,d),(c,d)) → ∫ H].  Its domain
    is stated as [Inner (c, c)] (definitionally the inner coend apex) so that
    the compositions with [bimap[Inner]] below resolve their category.

--------
在 [c] 的后腿：介体 [∫^d H((c,d),(c,d)) → ∫ H]。它的结构域被说明为 [Inner (c, c)]（定义上是内部卷顶），因此与下面的 [bimap[Inner] 的组合能够解决它们的范畴。
*)
Definition bwd_leg (c : C) :
  Inner (c, c) ~{Sets}~> coend_apex_setoid H :=
  coend_mediator (InnerIntegrand c c) (fun d => coend_inj_mor H (c, d))
    (bwd_inner_cond c).

(**
Backward outer cowedge: the [C]-glue for [fc] reduces, on generators, to a
    single [H]-glue at the pair morphism [(fc, id)]; the two sides agree with
    the common cowedge [fun d => bwd_leg c1 ∘ bimap[Inner] (op fc) id ∘ inj_d].

--------
向后外余楔：生成器上的 [C] 胶水对于 [fc] 简化为在对态射 [(fc, id)] 上的单个 [H] 胶水；两边与公共余楔 [fun d => bwd_leg c1 ∘ bimap[Inner] (op fc) id ∘ inj_d] 一致。
*)
Lemma bwd_cond : Cowedge_cond Inner (coend_apex_setoid H) bwd_leg.
Proof.
  intros c1 c2 fc.
  apply (coend_med_eq (SetsCoend (InnerIntegrand c2 c1)) (coend_apex_setoid H)
    (fun d => (bwd_leg c1 ∘ bimap[Inner] (op fc) id)
              ∘ @coend_inj D Sets (InnerIntegrand c2 c1)
                  (SetsCoend (InnerIntegrand c2 c1)) d)
    (postcompose_cowedge (InnerIntegrand c2 c1)
       (SetsCoend (InnerIntegrand c2 c1)) (coend_apex_setoid H)
       (bwd_leg c1 ∘ bimap[Inner] (op fc) id))
    (bwd_leg c1 ∘ bimap[Inner] (op fc) id)
    (bwd_leg c2 ∘ bimap[Inner] id fc)).
  - intro d; reflexivity.
  - intros d w.
    symmetry.
    exact (ce_glue H (c1, d) (c2, d) (fc, id) w).
Qed.

(** The backward comparison map [∫^c ∫^d H → ∫^{(c,d)} H]. / 向后的比较映射 [∫^c ∫^d H → ∫^{(c,d)} H]。 *)
Definition bwd :
  coend_apex_setoid Inner ~{Sets}~> coend_apex_setoid H :=
  coend_mediator Inner bwd_leg bwd_cond.

(**
[fwd] undoes [bwd_leg] fibrewise: on a generator [ci d h] both send it to
    [ci c (ci d h)].

--------
[fwd] 对 [bwd_leg] 进行纤维化逆操作：在生成元 [ci d h] 上，它们都会将其发送到 [ci c (ci d h)]。
*)
Lemma fwd_bwd_leg (c : C) :
  fwd ∘ bwd_leg c ≈ coend_inj_mor Inner c.
Proof.
  apply (coend_med_eq (SetsCoend (InnerIntegrand c c)) (coend_apex_setoid Inner)
    (fun d => (coend_inj_mor Inner c
                 : Inner (c, c) ~{Sets}~> coend_apex_setoid Inner)
              ∘ @coend_inj D Sets (InnerIntegrand c c)
                  (SetsCoend (InnerIntegrand c c)) d)
    (postcompose_cowedge (InnerIntegrand c c)
       (SetsCoend (InnerIntegrand c c)) (coend_apex_setoid Inner)
       (coend_inj_mor Inner c))
    (fwd ∘ bwd_leg c) (coend_inj_mor Inner c)).
  - intros d h; reflexivity.
  - intro d; reflexivity.
Qed.

(** Round trip on [∫^c ∫^d H]: [fwd ∘ bwd ≈ id]. / 在 [∫^c ∫^d H] 上的往返行程：[fwd ∘ bwd ≈ id]。 *)
Lemma fubini_to_from : fwd ∘ bwd ≈ id.
Proof.
  apply (coend_med_eq (SetsCoend Inner) (coend_apex_setoid Inner)
    (coend_inj_mor Inner) (coend_apex_cowedge Inner) (fwd ∘ bwd) id).
  - intro c.
    transitivity (fwd ∘ bwd_leg c).
    + intro s; reflexivity.
    + exact (fwd_bwd_leg c).
  - intros c s; reflexivity.
Qed.

(** Round trip on [∫^{(c,d)} H]: [bwd ∘ fwd ≈ id]. / 在 [∫^{(c,d)} H] 上的往返行程：[bwd ∘ fwd ≈ id]。 *)
Lemma fubini_from_to : bwd ∘ fwd ≈ id.
Proof.
  apply (coend_med_eq (SetsCoend H) (coend_apex_setoid H)
    (coend_inj_mor H) (coend_apex_cowedge H) (bwd ∘ fwd) id).
  - intro p; destruct p as [c d]; intros h; reflexivity.
  - intros p h; reflexivity.
Qed.

(** The Fubini isomorphism [∫^{(c,d)} H ≅ ∫^c ∫^d H] in [Sets]. / Fubini 同构在 [Sets] 中的 [∫^{(c,d)} H ≅ ∫^c ∫^d H]。 *)
Definition coend_fubini :
  coend_obj (SetsCoend H) ≅[Sets] coend_obj (SetsCoend Inner) :=
  {| to := fwd;
     from := bwd;
     iso_to_from := fubini_to_from;
     iso_from_to := fubini_from_to |}.

End Fubini.
