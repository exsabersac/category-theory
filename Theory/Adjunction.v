Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/adjoint+functor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   F : D ⟶ C（左伴随）与 U : C ⟶ D（右伴随）之间的伴随 F ⊣ U 此处以 hom 集形式给出：
   setoid 范畴中一族同构 adj {x y} : (F x ~{C}~> y) ≊ (x ~{D}~> U y)，对两变元自然。
   写 ⌊f⌋ := to adj f、⌈f⌉ := from adj f 为两个转置，自然性由 [to_adj_nat_l]、
   [to_adj_nat_r]（及反向 [from_adj_nat_l]、[from_adj_nat_r]）记录。单位
   η := ⌊id⌋ : x ~> U (F x) 与余单位 ε := ⌈id⌉ : F (U x) ~> x 是恒等的转置，
   三角（之字形）恒等式 ε ∘ fmap[F] η ≈ id[F x]（counit_fmap_unit）与
   fmap[U] ε ∘ η ≈ id[U x]（fmap_counit_unit）作为派生推论成立。 *)

(* 伴随的起源、无处不在与用途

   nLab:  https://ncatlab.org/nlab/show/adjoint+functor
   Paper: Kan, "Adjoint functors", Transactions of the American
          Mathematical Society 87(2), 1958
   Paper: Lawvere, "Adjointness in Foundations", Dialectica 23(3/4), 1969;
          reprinted as TAC Reprints 16, 2006

   伴随函子由 Daniel Kan——同伦理论家、Eilenberg 的博士生——在上述 1958 论文中引入。
   概念由同调代数的需要所提示，彼处形如 Hom(F x, y) ≅ Hom(x, U y) 的自然双射早已常用，
   典范情形是阿贝尔群上的张量-hom 伴随 − ⊗ A ⊣ Hom(A, −)。名称记录与 Hilbert 空间上
   伴随线性算子 ⟨L x, y⟩ = ⟨x, R y⟩ 的类比；nLab 把范畴概念描述为对那一更老概念的
   某种范畴化。Mac Lane 在《Categories for the Working Mathematician》（Springer, 1971）
   序言中给出标准评价：「伴随函子无处不在」，该书中部把普遍构造、极限与自由对象
   呈现为伴随的诸多面孔。

   概念的三种呈现等价，本库均形式化。本文件以 Kan 的 hom 集形式为原始：自然的
   setoid 同构族 [adj]。单位/余单位形式——η 与 ε 服从两条三角恒等式，此处作为派生推论
   [counit_fmap_unit] 与 [fmap_counit_unit] 出现——是 Adjunction/Natural/Transformation.v
   的类 [Adjunction_Transform]，两种形式的往返在
   Adjunction/Natural/Transformation/Universal.v。普遍箭头形式是 Theory/Universal/Arrow.v，
   其 [AdjunctionFromUniversalArrows] 从逐点普遍解族组装伴随，是 Adjunction/GAFT.v
   伴随函子定理背后的引擎。伴随弱于范畴同构或等价，但足以运送结构：伴随在自然同构
   下唯一（下文 [right_adjoint_iso]、[left_adjoint_iso]），右伴随保持极限、左伴随保持
   余极限（Adjunction/Continuity.v，本文件末注记已预示），且每个伴随诱导单子。后者是
   Huber 的观察（"Homotopy theory in general categories", Mathematische Annalen 144, 1961），
   此处实现为 Monad/Adjunction.v 的 [Adjunction_Monad]；其逆——每个单子都如此产生——
   在 1965 年被证明两次：Kleisli（"Every standard construction is induced by a pair of
   adjoint functors", Proceedings of the AMS 16(3), 1965）给出初始分解，Eilenberg 与
   Moore（"Adjoint functors and triples", 1965）给出终结分解，树内分别为
   Monad/Kleisli/Adjunction.v 与 Monad/Eilenberg/Moore/Adjunction.v。

   Lawvere 的 "Adjointness in Foundations" 主张：首先在范畴论中分离并命名的伴随性
   也遍及逻辑——笛卡尔闭结构完全由伴随给出，curry 是 − × a ⊣ (−)^a——量词形成伴随三元组
   ∃ ⊣ 替换 ⊣ ∀（在 hyperdoctrine 纤维上），该三元组在类型论中再现为依赖和与积、在几何中
   为基变换。在偏序之间，伴随恰是 Galois 联络——在 Instance/Proset/Galois.v 双向证明，
   且证明本类的连贯性字段在薄目标上空虚而 hom 集同构则否（[succ_not_self_adjoint]）——
   其反变变体恢复经典 Galois 理论；抽象解释（Cousot and Cousot, POPL 1977）建立在此特殊情形上，
   具体域与抽象域之间的联络 α ⊣ γ——c ⊑ γ(a) ⟺ α(c) ≼ a——是静态分析器的可靠性纪律，
   且此类联络可复合，故近似阶段可堆叠。

   对函数式程序员（Milewski, "Adjunctions", 2016），转置 ⌊-⌋ 与 ⌈-⌉ 是 Haskell Adjunction
   类的 leftAdjunct 与 rightAdjunct，而 [unit] 与 [counit] 特殊化为 return 与 extract。
   积类型是对角函子的右伴随——具体见 Adjunction/Diagonal/Product.v 的
   [Diagonal_Product_Adjunction]——函数类型来自 − × a ⊣ (−)^a，以 eval 为余单位。
   下一块注释的自由/遗忘读法，树内由 Construction/Free/Quiver.v 的 [FreeForgetfulAdjunction]
   见证，是历史上中心的例子族，但并非全部：极限与 Kan 扩张本身也是伴随（分别对对角与限制函子）。 *)

(*
   伴随 relate two 函子 that map between the same two 范畴

   本节：(though 反 directions), manner 即 weaker than 同构 等价, but still quite informative. 一般地, one 函子 is forgetful, maps constructions from more expressive domain into one that captures only essence that structure;

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section Adjunction.

Universes o1 h1 p1 o2 h2 p2.
Context {C : Category@{o1 h1 p1}}.
Context {D : Category@{o2 h2 p2}}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Reserved Notation "⌊ f ⌋".
Reserved Notation "⌈ f ⌉".

(* o3 p3 are universes larger than either C or D. *)
Class Adjunction@{o3 p3 so sh sp} := {
  (* adj {x y} : F x ~{C}~> y ≊ x ~{D}~> U y *)
  adj {x y} :
    @Isomorphism@{so sh p3} Sets@{o3 so}
      {| carrier := @hom C (F x) y; is_setoid := @homset C (F x) y |}
      {| carrier := @hom D x (U y); is_setoid := @homset D x (U y) |}
    where "⌊ f ⌋" := (to   adj f)
      and "⌈ f ⌉" := (from adj f);

  (* Naturality of the iso in both arguments, stated for the forward transpose
     ⌊-⌋ = to adj (naturality in x, via F) and ... *)
  to_adj_nat_l {x y z} (f : F y ~> z) (g : x ~> y) :
    ⌊f ∘ fmap[F] g⌋ ≈ ⌊f⌋ ∘ g;
  (* ... naturality in y, via U. *)
  to_adj_nat_r {x y z} (f : y ~> z) (g : F x ~> y) :
    ⌊f ∘ g⌋ ≈ fmap[U] f ∘ ⌊g⌋;

  (*
   本节说明相关定义、性质与动机。 The dual (_sym) statements inverse transpose ⌈-⌉ = from adj;.

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
  from_adj_nat_l {x y z} (f : y ~> U z) (g : x ~> y) :
    ⌈f ∘ g⌉ ≈ ⌈f⌉ ∘ fmap[F] g;
  from_adj_nat_r {x y z} (f : y ~> z) (g : x ~> U y) :
    ⌈fmap[U] f ∘ g⌉ ≈ f ∘ ⌈g⌉
}.

Definition Build_Adjunction'
  (adj : forall x y,
    @Isomorphism Sets
      {| carrier := @hom C (F x) y; is_setoid := @homset C (F x) y |}
      {| carrier := @hom D x (U y); is_setoid := @homset D x (U y) |})
  (to_adj_nat_l : forall x y z (f : F y ~> z) (g : x ~> y),
      (to (adj _ _)  (f ∘ fmap[F] g) ≈ (to (adj _ _) f) ∘ g))
  (to_adj_nat_r : forall x y z (f : y ~> z) (g : F x ~> y),
      (to (adj _ _) (f ∘ g) ≈ fmap[U] f ∘ (to (adj _ _) g)))
  : Adjunction.
Proof.
  unshelve eapply Build_Adjunction.
  + apply to_adj_nat_l.
  + apply to_adj_nat_r.
  + intros x y z f g.
    set (f' := from (adj y z) f).
    apply ((snd (@injectivity_is_monic _ _ (adj x z))) _).
    change (to (adj x z) (from (adj x z) _)) with
      (((adj x z) ∘ (from (adj x z))) (f ∘ g)).
    rewrite ((iso_to_from (adj x z)) (f ∘ g)); simpl;
    rewrite to_adj_nat_l.
    refine (compose_respects _ _ _ g _ (Equivalence_Reflexive _)).
    unfold f'; symmetry.
    exact ((iso_to_from (adj y z)) f).
  + intros x y z f g.
    set (g' :=  from (adj x y) g).
    apply ((snd (@injectivity_is_monic _ _ (adj x z))) _).
    rewrite (iso_to_from (adj x z) (fmap[U] f ∘ g)); simpl.
    rewrite to_adj_nat_r.
    apply (compose_respects (fmap[U] f) _ (Equivalence_Reflexive _)).
    unfold g'; symmetry;
      apply (iso_to_from (adj x y) g).
Defined.

Context `{@Adjunction}.

Notation "⌊ f ⌋" := (to adj f).
Notation "⌈ f ⌉" := (from adj f).

Corollary adj_univ `(f : F x ~> y) (g : x ~> U y) :
  f ≈ ⌈g⌉ ↔ ⌊f⌋ ≈ g.
Proof.
  split; intros.
  - rewrite X.
    sapply (@iso_to_from Sets _ _ (@adj _ x y)).
  - rewrite <- X.
    symmetry.
    sapply (@iso_from_to Sets _ _ (@adj _ x y)).
Qed.

Corollary to_adj_comp_law {x y} (f : F x ~> y) :
  ⌈⌊f⌋⌉ ≈ f.
Proof. sapply (@iso_from_to Sets _ _ (@adj _ x y) f). Qed.

Corollary from_adj_comp_law {x y} (f : x ~> U y) :
  ⌊⌈f⌉⌋ ≈ f.
Proof. sapply (@iso_to_from Sets _ _ (@adj _ x y) f). Qed.

Definition unit   {x : D} : x ~> U (F x) := ⌊id⌋.
Definition counit {x : C} : F (U x) ~> x := ⌈id⌉.

Notation "'η'" := unit.
Notation "'ε'" := counit.

Corollary from_adj_unit {x} :
  ⌈η⌉ ≈ id[F x].
Proof. sapply (@iso_from_to Sets _ _ (@adj _ x (F x))). Qed.

Corollary to_adj_counit {x} :
  ⌊ε⌋ ≈ id[U x].
Proof. sapply (@iso_to_from Sets _ _ (@adj _ (U x) x)). Qed.

Corollary counit_comp {x y} (f : F x ~> y) :
  ε ∘ fmap[F] (fmap[U] f) ≈ f ∘ ε.
Proof.
  unfold counit.
  rewrite <- from_adj_nat_l.
  rewrite <- from_adj_nat_r.
  rewrite id_left, id_right.
  reflexivity.
Qed.

Corollary unit_comp {x y} (f : x ~> U y) :
  fmap[U] (fmap[F] f) ∘ η ≈ η ∘ f.
Proof.
  unfold unit.
  rewrite <- to_adj_nat_l.
  rewrite <- to_adj_nat_r.
  rewrite id_left, id_right.
  reflexivity.
Qed.

Corollary adj_univ_impl {x y} (f : F x ~> y) (g : x ~> U y) :
  f ≈ ε ∘ fmap[F] g ↔ ⌊f⌋ ≈ g.
Proof.
  unfold counit.
  split; intros.
  - rewrite X; clear X.
    rewrite <- from_adj_nat_l.
    rewrite id_left.
    apply from_adj_comp_law.
  - rewrite <- X; clear X.
    rewrite <- from_adj_nat_l.
    rewrite id_left.
    symmetry.
    apply to_adj_comp_law.
Qed.

Corollary to_adj_unit {x y} (f : F x ~> y) :
  ⌊f⌋ ≈ fmap[U] f ∘ η.
Proof.
  rewrite <- (id_right f).
  rewrite to_adj_nat_r.
  rewrite fmap_comp; cat.
Qed.

Corollary from_adj_counit {x y} (f : x ~> U y) :
  ⌈f⌉ ≈ ε ∘ fmap[F] f.
Proof.
  rewrite <- (id_left f).
  rewrite from_adj_nat_l.
  rewrite fmap_comp; cat.
Qed.

Corollary counit_fmap_unit  {x} :
  ε ∘ fmap[F] η ≈ id[F x].
Proof.
  unfold unit, counit.
  rewrite <- from_adj_nat_l; cat.
  sapply (@iso_from_to Sets _ _ (@adj _ x (F x))).
Qed.

Corollary fmap_counit_unit  {x} :
  fmap[U] ε ∘ η ≈ id[U x].
Proof.
  unfold unit, counit.
  rewrite <- to_adj_nat_r; cat.
  sapply (@iso_to_from Sets _ _ (@adj _ (U x) x)).
Qed.

Corollary fmap_from_adj_unit {x y} (f : x ~{D}~> y) : fmap[F] f ≈ ⌈η ∘ f⌉.
Proof.
  unfold unit.
  rewrite from_adj_nat_l.
  rewrite to_adj_comp_law; cat.
Qed.

Corollary fmap_to_adj_counit {x y} (f : x ~{C}~> y) : fmap[U] f ≈ ⌊f ∘ ε⌋.
Proof.
  unfold counit.
  rewrite to_adj_nat_r.
  rewrite from_adj_comp_law; cat.
Qed.

(* If F is a faithful functor, and f is monic, then adj f is monic. *)
Theorem adj_monic  {x y} (f : F x ~> y) c (g h : c ~> x) :
  Faithful F → Monic f ->
    ⌊f⌋ ∘ g ≈ ⌊f⌋ ∘ h → g ≈ h.
Proof.
  intros.
  rewrite <- !to_adj_nat_l in X1.
  assert
    (Proper
       (@equiv _ unit_setoid ==> equiv)
       (λ _ : unit_setoid_object, f ∘ fmap[F] g)) as XA by proper.
  assert
    (Proper
       (@equiv _ unit_setoid ==> equiv)
       (λ _ : unit_setoid_object, f ∘ fmap[F] h)) as XB by proper.
  pose proof
       (monic (Monic:=@iso_to_monic Sets
                                    {| is_setoid := homset (fobj[F] c) y |}
                                    {| is_setoid := homset c (fobj[U] y) |}
                                    (@adj H c y))
              unit_setoid_object
              {| morphism  := λ _ : unit_setoid_object, f ∘ fmap[F] g |}
              {| morphism  := λ _ : unit_setoid_object, f ∘ fmap[F] h |}) as X2.
  simpl in X2.
  now apply X, X0, X2.
Qed.

Corollary to_adj_respects {x y} (f g : F x ~{C}~> y) :
  f ≈ g → ⌊f⌋ ≈ ⌊g⌋.
Proof. intros; now rewrites. Qed.

Corollary from_adj_respects {x y} (f g : x ~{D}~> U y) :
  f ≈ g → ⌈f⌉ ≈ ⌈g⌉.
Proof. intros; now rewrites. Qed.

End Adjunction.

Arguments Adjunction {C D} F%_functor U%_functor.

Declare Scope adjunction_scope.
Declare Scope adjunction_type_scope.
Bind Scope adjunction_scope with Adjunction.
Delimit Scope adjunction_type_scope with adjunction_type.
Delimit Scope adjunction_scope with adjunction.
Open Scope adjunction_type_scope.
Open Scope adjunction_scope.

Notation "F ⊣ G" := (@Adjunction _ _ F G) (at level 59) : category_scope.
Notation "adj[ A ]" := (@adj _ _ _ _ A _ _)
  (at level 9, format "adj[ A ]") : morphism_scope.

(* Wikipedia: "If the functor F : C ← D has two right adjoints G and G', then
   G and G' are naturally isomorphic. The same is true for left adjoints." *)

Theorem right_adjoint_iso `(F : C ⟶ D) (G G' : D ⟶ C) :
  F ⊣ G → F ⊣ G' → G ≈ G'.
Proof.
  intros.
  construct.
  - isomorphism.
    + apply adj; simpl.
      apply X; simpl.
      exact id.
    + apply adj; simpl.
      apply X0; simpl.
      exact id.
    + simpl.
      rewrite <- to_adj_nat_l.
      rewrite <- from_adj_nat_l.
      rewrite id_left.
      rewrite to_adj_comp_law.
      rewrite from_adj_comp_law.
      reflexivity.
    + simpl.
      rewrite <- to_adj_nat_l.
      rewrite <- from_adj_nat_l.
      rewrite id_left.
      rewrite to_adj_comp_law.
      rewrite from_adj_comp_law.
      reflexivity.
  - simpl.
    rewrite <- to_adj_nat_l.
    rewrite <- from_adj_nat_l.
    rewrite id_left.
    rewrite <- to_adj_nat_l.
    rewrite <- from_adj_nat_l.
    rewrite <- to_adj_nat_r.
    rewrite <- from_adj_nat_r.
    rewrite id_right.
    rewrite to_adj_comp_law.
    rewrite from_adj_comp_law.
    reflexivity.
Qed.

Theorem left_adjoint_iso `(G : D ⟶ C) (F F' : C ⟶ D) :
  F ⊣ G → F' ⊣ G → F ≈ F'.
Proof.
  intros.
  construct.
  - isomorphism.
    + apply adj; simpl.
      apply X0; simpl.
      exact id.
    + apply adj; simpl.
      apply X; simpl.
      exact id.
    + simpl.
      rewrite <- from_adj_nat_r.
      rewrite <- to_adj_nat_r.
      rewrite id_right.
      rewrite from_adj_comp_law.
      rewrite to_adj_comp_law.
      reflexivity.
    + simpl.
      rewrite <- from_adj_nat_r.
      rewrite <- to_adj_nat_r.
      rewrite id_right.
      rewrite from_adj_comp_law.
      rewrite to_adj_comp_law.
      reflexivity.
  - simpl.
    rewrite <- from_adj_nat_r.
    rewrite <- to_adj_nat_r.
    rewrite id_right.
    rewrite <- from_adj_nat_l.
    rewrite <- to_adj_nat_l.
    rewrite id_left.
    rewrite from_adj_comp_law.
    rewrite to_adj_comp_law.
    reflexivity.
Qed.

(*
   本节：Future direction (no scaffolding here yet):. "The most important property adjoints is their continuity: every 函子 that has 左伴随 (and therefore is 右伴随) is continuous (i.e. commutes 极限 范畴 theoretical sense);

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(** ** Transporting an adjunction along an isomorphism of left adjoints *)

(*
   A 函子 naturally isomorphic to a 左伴随 is a 左伴随,

   本节：with SAME 右伴随. [right_伴随_iso] [left_伴随_iso] above run other way (from two 伴随 同构), Theory/等价/伴随.v transports along EQUIVALENCE OF CATEGORIES rather than along 2-cell, Theory/函子.v's [transport_ad

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section AdjunctionAlongIso.

#[local] Obligation Tactic := idtac.

Context {C D : Category}.
Context {F F' : D ⟶ C}.
Context {G : C ⟶ D}.
Context (Hiso : F ≈ F').
Context (A : F' ⊣ G).

Definition aali_cell (x : D) : F x ≅ F' x := projT1 Hiso x.

Lemma aali_natural {x y : D} (g : x ~> y) :
  fmap[F] g ∘ from (aali_cell x) ≈ from (aali_cell y) ∘ fmap[F'] g.
Proof.
  rewrite (projT2 Hiso x y g).
  rewrite <- comp_assoc.
  rewrite (iso_to_from (aali_cell x)).
  now rewrite id_right.
Qed.

Definition aali_to (x : D) (y : C) (f : F x ~> y) : x ~> G y :=
  to (@adj C D F' G A x y) (f ∘ from (aali_cell x)).

Definition aali_from (x : D) (y : C) (g : x ~> G y) : F x ~> y :=
  from (@adj C D F' G A x y) g ∘ to (aali_cell x).

Lemma aali_to_from (x : D) (y : C) (g : x ~> G y) :
  aali_to x y (aali_from x y g) ≈ g.
Proof.
  unfold aali_to, aali_from.
  rewrite <- comp_assoc.
  rewrite (iso_to_from (aali_cell x)).
  rewrite id_right.
  exact (@from_adj_comp_law C D F' G A x y g).
Qed.

Lemma aali_from_to (x : D) (y : C) (f : F x ~> y) :
  aali_from x y (aali_to x y f) ≈ f.
Proof.
  unfold aali_to, aali_from.
  rewrite (@to_adj_comp_law C D F' G A x y (f ∘ from (aali_cell x))).
  rewrite <- comp_assoc.
  rewrite (iso_from_to (aali_cell x)).
  now rewrite id_right.
Qed.

Program Definition aali_iso (x : D) (y : C) :
  @Isomorphism Sets
    {| carrier := @hom C (F x) y; is_setoid := @homset C (F x) y |}
    {| carrier := @hom D x (G y); is_setoid := @homset D x (G y) |} := {|
  to   := {| morphism := aali_to x y |};
  from := {| morphism := aali_from x y |}
|}.
Next Obligation.
  intros x y f f' Hf; unfold aali_to.
  now rewrite Hf.
Qed.
Next Obligation.
  intros x y g g' Hg; unfold aali_from.
  now rewrite Hg.
Qed.
Next Obligation. intros x y g; exact (aali_to_from x y g). Qed.
Next Obligation. intros x y f; exact (aali_from_to x y f). Qed.

Definition adjunction_along_left_iso : F ⊣ G.
Proof using A C D F F' G Hiso.
  unshelve eapply (@Build_Adjunction' C D F G aali_iso).
  - intros x y z f g; simpl; unfold aali_to.
    rewrite <- comp_assoc.
    rewrite (aali_natural g).
    rewrite comp_assoc.
    exact (@to_adj_nat_l C D F' G A x y z (f ∘ from (aali_cell y)) g).
  - intros x y z f g; simpl; unfold aali_to.
    rewrite <- comp_assoc.
    exact (@to_adj_nat_r C D F' G A x y z f (g ∘ from (aali_cell x))).
Defined.

Example aali_to_is_transpose (x : D) (y : C) (f : F x ~> y) :
  to (@adj C D F G adjunction_along_left_iso x y) f
    = to (@adj C D F' G A x y) (f ∘ from (aali_cell x)) := eq_refl.

End AdjunctionAlongIso.

Arguments aali_cell {C D F F'} Hiso x.
Arguments adjunction_along_left_iso {C D F F' G} Hiso A.
