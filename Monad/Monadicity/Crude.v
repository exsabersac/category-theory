Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Instance.Fun.
Require Import Category.Monad.Adjunction.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Limit.Preservation.

Generalizable All Variables.

(**
* Crude monadicity

    nLab:      https://ncatlab.org/nlab/show/monadicity+theorem
    Wikipedia: https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem

    Fix an adjunction F ⊣ U with F : D ⟶ C, its induced monad
    T = U ◯ F on D (Monad/Comparison.v packages it transparently as
    [Adjunction_Induced_Monad], with ret = η and join = U ε F), and the
    Eilenberg–Moore comparison K = [EM_Comparison] : C ⟶ D^T.  The crude
    monadicity theorem states that K is an equivalence of categories
    provided that

      1. C has coequalizers of reflexive pairs ([HasReflexiveCoequalizers]),
      2. U preserves them ([PreservesReflexiveCoequalizers] below), and
      3. U reflects isomorphisms ([ReflectsIsos], i.e. U is conservative).

    Deviation of form: hypothesis 2 is stated elementarily — for every
    reflexive pair and every elementary coequalizer of it, the U-image of
    the coequalizing map is again an elementary coequalizer of the image
    pair.  This is the standard crude hypothesis.  Relating it to the
    colimit-based [PreservesColimit] vocabulary would use the Phase-8
    conversions ([coequalizer_is_coequalizer] / [is_coequalizer_colimit]
    in Structure/Coequalizer.v with [preserves_colimit] in
    Structure/Limit/Preservation.v) plus an identification of the
    composed diagram [U ◯ APair f g] with [APair (fmap[U] f) (fmap[U] g)]
    that the library does not carry; the elementary form is what the
    proof consumes directly, so no bridge is needed here.
    CORRECTION (#477): accurate when written; the relation no longer
    needs that identification.  Structure/Coequalizer.v's
    [parallel_colimit_coequalizer], at [K := U ◯ APair f g], reads any
    colimiting cocone over the composed diagram as an elementary
    coequalizer of [fmap[U] f] and [fmap[U] g] by conversion, and
    [parallel_coequalizer_colimit] goes back (Test/ProbeAbsolute477.v,
    C30).  They are what such a relation would now use, against the
    cone-level [PreservesColimitCocone] at each reflexive pair rather
    than the apex-only [PreservesColimit]; the relation itself is not
    stated anywhere, and the identification is still not carried.

    The construction of the quasi-inverse G = [Crude_Inverse] : D^T ⟶ C
    is the classical Beck argument:

    - Every algebra (d, α) has a canonical presentation by free objects:
      the pair ε_{F d}, F α : F (U (F d)) ⇉ F d is reflexive with common
      section F η_d — the two retraction laws are the zig-zag identity
      [counit_fmap_unit] and the F-image of the algebra unit law [t_id].
      G (d, α) is the chosen coequalizer q of this pair, with
      coequalizing map e : F d ~> q.

    - G on morphisms is by descent: for an algebra homomorphism h the
      composite e' ∘ F h₀ coforks the presentation of the source (by
      counit naturality and the commuting square of h), so it descends
      uniquely through e.  Functoriality is descent uniqueness; every
      square of mediators commutes because both sides descend the same
      cofork.

    - Downstairs, applying U to the defining coequalizer yields (by
      hypothesis 2) a coequalizer of the pair U ε_{F d}, U (F α), which
      is definitionally the canonical pair μ_d, T α of the algebra —
      the pair split-coequalized by α itself ([canonical_split] in
      Monadicity/BeckObjects.v).  Coequalizers of the same pair agree up
      to isomorphism: descending α through U e gives [crude_to], while
      the split coequalizer's own descent of U e is
      [crude_from] = U e ∘ η_d, and the two are mutually inverse.

    - The counit K (G (d, α)) ≅ (d, α): [crude_from] underlies an
      algebra homomorphism (d, α) ~> K (G (d, α)) (its commuting square
      is counit naturality plus the zig-zag identity), and its carrier
      is invertible; the inverse arrow is again a homomorphism by the
      conjugation argument [em_iso_inverse_hom] of BeckObjects.v — this
      is conservativity of U^T at work, with the inverse kept
      transparent so the isomorphism can be assembled by hand.

    - The unit c ≅ G (K c): the counit ε_c coforks the presentation of
      the algebra K c = (U c, U ε_c) by naturality, so it descends to a
      mediator θ_c : G (K c) ~> c.  Its U-image coincides (by descent
      uniqueness) with the comparison iso [crude_to] at K c, hence is
      invertible; hypothesis 3 reflects the invertibility of θ_c itself.

    All mediating morphisms are compared through the uniqueness clause
    of descent, and both natural-isomorphism cells of the equivalence
    ([Functor_Setoid]'s bundled form) carry their conjugation coherence
    by the same discipline. 

--------
* 粗略的单一性

nLab：https://ncatlab.org/nlab/show/monadicity+theorem
 维基百科：https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem

将附加词 F ⊣ U 与 F : D ⟶ C 修复，其导出单子
 T = U ◯ F on D（Monad/Comparison.v 将其透明地封装为
 [Adjunction_Induced_Monad]，其中 ret = η 且 join = U ε F)，并且
 艾伦伯格-摩尔比较 K = [EM_Comparison] : C ⟶ D^T。 粗制的
 一元性定理指出 K 是类别的等价性
 前提是

1. C 有自反对的共均衡器 ([HasReflexiveCoequalizers])，
 2. U 保留它们（下面的 [PreservesReflexiveCoequalizers]），并且
 3. U反映同构（[ReflectsIsos]，即U是保守的）。

形式偏差：假设 2 是基本陈述的——对于每一个
 自反对及其每个基本余均衡器，U-图像
 协同均衡图又是图像的基本协同均衡器
 对。 这是标准的粗略假设。 将其与
 基于 colimit 的 [PreservesColimit] 词汇表将使用 Phase-8
 转换（[coequalizer_is_coequalizer] / [is_coequalizer_colimit]
 在 Structure/Coequalizer.v 中使用 [preserves_colimit]
 Structure/Limit/Preservation.v) 加上一个标识
 [U ◯ APair f g] 与 [APair (fmap[U] f) 的组合图 (fmap[U] g)]
 图书馆没有； 基本形式是
 证明直接消耗，所以这里不需要桥。 更正（#477）：书写准确； 关系不再
 需要那个身份证明。
结构/Coequalizer.v 的
 [parallel_colimit_coequalizer]、[K := U ◯ APair f g] 读取任何
 将可锥作为基本的组合图进行限制
 通过转换 [fmap[U] f] 和 [fmap[U] g] 的协均衡器，以及
 [parallel_coequalizer_colimit] 返回（Test/ProbeAbsolute477.v，
 C30）。 它们就是现在这种关系所使用的，以对抗
 每个自反对的锥体水平 [PreservesColimitCocone]
 比仅顶点 [PreservesColimit]； 关系本身不是
 已在任何地方注明，但仍未携带身份证明。

拟逆 G = [Crude_Inverse] 的构造：D^T ⟶ C
 是经典的贝克论证：

- 每个代数 (d, α) 都有自由对象的规范表示：
 ε_{F d}, F α : F (U (F d)) ⇉ F d 是自反的
 F η_d 部分 — 两个回缩定律是 zig-zag 恒等式
 [counit_fmap_unit] 和代数单位法 [t_id] 的 F 图像。 
G (d, α) 是该对中所选的协均衡器 q，其中
 共均衡映射 e : F d ~> q。

- 态射上的 G 是由下降而来的：对于代数同态 h
 复合 e' ∘ F h₀ 共同分叉源的呈现（通过
 计算自然性和 h) 的通勤平方，因此它下降
 唯一通过 e。 功能性是血统的独特性； 每个
 调解员的正方形通勤，因为双方下降相同
 科福克。

- 楼下，将 U 应用于定义的 coequalizer 产量（通过
 假设 2) U ε_{F d}, U (F α) 对的共均衡器，其中
 定义上是代数的规范对 μ_d, T α —
 该对由 α 本身分裂共均衡（[canonical_split] in
 Monadicity/BeckObjects.v)。 同一对的共均衡器一致
 到同构：从 α 降到 U e 给出 [crude_to]，而
 分裂共均衡器自身的 U e 下降为
 [crude_from] = U e ∘ η_d，两者互逆。

- 单位 K (G (d, α)) ≅ (d, α)：[crude_from] 是
 代数同态 (d, α) ~> K (G (d, α)) （其交换平方
 是单位自然性加上 zig-zag 恒等式）及其载体
 是可逆的； 反箭头又是同态
 BeckObjects.v 的共轭参数 [em_iso_inverse_hom] — this
 是 U^T 的保守性，其逆值保持不变
 透明，因此同构可以手工组装。

- 单位 c ≅ G (K c)：单位 ε_c 共同表示
 代数 K c = (U c, U ε_c) 自然地，所以它下降到 a
 中介者 θ_c : G (K c) ~> c。 它的 U 形像重合（通过下降
 唯一性）与 K c 处的比较 iso [crude_to]，因此是
 可逆； 假设3反映了θ_c本身的可逆性。

所有中介态射都通过唯一性子句进行比较
 的血统，以及等价的两个自然同构细胞
 （[Functor_Setoid] 的捆绑形式）具有共轭一致性
 由同一学科。 
*)

(* Hypothesis 2, stated elementarily: U carries any elementary
   coequalizer of a reflexive pair to an elementary coequalizer of the
   image pair, at the image apex, coequalized by the image map. *)
Definition PreservesReflexiveCoequalizers {C D : Category} (U : C ⟶ D) :
  Type :=
  ∀ (x y : C) (f g : x ~{C}~> y), ReflexivePair f g →
    ∀ (q : C) (e : y ~{C}~> q), IsCoequalizer f g q e →
      IsCoequalizer (fmap[U] f) (fmap[U] g) (U q) (fmap[U] e).

Section CrudeMonadicity.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).
Context (RC : HasReflexiveCoequalizers C).
Context (pres : PreservesReflexiveCoequalizers U).
Context (refl : ReflectsIsos U).

Local Notation HM := (Adjunction_Induced_Monad A).
Local Notation EM := (@EilenbergMoore D (U ◯ F) HM).
Local Notation K := (EM_Comparison A).

(**
** The canonical presentation of an algebra, upstairs in C

    For an algebra x = (d, α) of the induced monad, the parallel pair

        ε_{F d}, F α : F (U (F d)) ⇉ F d

    is reflexive, with common section F η_d. 

--------
** 代数的规范表示，楼上的 C 语言

 对于诱导单子的代数 x = (d, α)，平行对

 ε_{F d}, F α : F (U (F d)) ⇉ F d

 是自反的，具有公共部分 F η_d。 
*)

Definition crude_pair_l (x : EM) :
  F (U (F (`1 x))) ~{C}~> F (`1 x) :=
  @counit _ _ _ _ A (F (`1 x)).

Definition crude_pair_r (x : EM) :
  F (U (F (`1 x))) ~{C}~> F (`1 x) :=
  fmap[F] (t_alg[`2 x]).

(*
The algebra unit law α ∘ η ≈ id, re-read through the transparent
   identification ret = η of the induced monad. 

--------
代数单位律 α ∘ η ≈ id，通过透明重新读一遍
 识别 ret = 诱导单子的 η。 
*)
Lemma crude_alg_unit (x : EM) :
  t_alg[`2 x] ∘ @unit _ _ _ _ A (`1 x) ≈ id.
Proof. exact (@t_id D (U ◯ F) HM (`1 x) (`2 x)). Qed.

(* ε_{F d} retracts F η_d: the zig-zag identity.  / ε_{F d} 收回 F η_d：zig-zag 恒等式。*)
Lemma crude_section_l (x : EM) :
  @counit _ _ _ _ A (F (`1 x)) ∘ fmap[F] (@unit _ _ _ _ A (`1 x)) ≈ id.
Proof. exact (@counit_fmap_unit _ _ _ _ A (`1 x)). Qed.

(* F α retracts F η_d: the F-image of the algebra unit law.  / F α 收回 F η_d：代数单位律的 F 图像。*)
Lemma crude_section_r (x : EM) :
  fmap[F] (t_alg[`2 x]) ∘ fmap[F] (@unit _ _ _ _ A (`1 x)) ≈ id.
Proof.
  rewrite <- fmap_comp.
  rewrite (crude_alg_unit x).
  apply fmap_id.
Qed.

Definition crude_reflexive (x : EM) :
  ReflexivePair (crude_pair_l x) (crude_pair_r x) :=
  common_section_reflexive (crude_pair_l x) (crude_pair_r x)
    (fmap[F] (@unit _ _ _ _ A (`1 x)))
    (crude_section_l x) (crude_section_r x).

(** ** The quasi-inverse on objects: the chosen reflexive coequalizer  / ** 对象的拟逆：所选择的自反协均衡器*)

Definition crude_coeq (x : EM) :
  ∃ (q : C) (e : F (`1 x) ~{C}~> q),
    IsCoequalizer (crude_pair_l x) (crude_pair_r x) q e :=
  @reflexive_coeq C RC (F (U (F (`1 x)))) (F (`1 x))
    (crude_pair_l x) (crude_pair_r x) (crude_reflexive x).

Definition crude_G_obj (x : EM) : C := `1 (crude_coeq x).

Definition crude_e (x : EM) : F (`1 x) ~{C}~> crude_G_obj x :=
  `1 (`2 (crude_coeq x)).

Definition crude_is_coeq (x : EM) :
  IsCoequalizer (crude_pair_l x) (crude_pair_r x)
    (crude_G_obj x) (crude_e x) :=
  `2 (`2 (crude_coeq x)).

(* The cofork law of the chosen coequalizer, in unfolded form.  / 所选辅均衡器的辅叉法则，以展开形式呈现。*)
Lemma crude_cofork (x : EM) :
  crude_e x ∘ @counit _ _ _ _ A (F (`1 x))
    ≈ crude_e x ∘ fmap[F] (t_alg[`2 x]).
Proof. exact (cofork (crude_is_coeq x)). Qed.

Definition crude_e_epic (x : EM) : Epic (crude_e x) :=
  coequalizer_epic _ _ (crude_is_coeq x).

(** ** The quasi-inverse on morphisms: descent  / ** 态射的拟逆：下降*)

(*
The commuting square of an algebra homomorphism, with the action of
   the composite functor spelled out as fmap[U] (fmap[F] -). 

--------
代数同态的交换平方，其作用为
 复合函子拼写为 fmap[U] (fmap[F] -)。 
*)
Lemma crude_hom_square {x y : EM} (h : x ~{EM}~> y) :
  t_alg_hom[h] ∘ t_alg[`2 x]
    ≈ t_alg[`2 y] ∘ fmap[U] (fmap[F] (t_alg_hom[h])).
Proof.
  exact (@t_alg_hom_commutes D (U ◯ F) HM (`1 x) (`1 y) (`2 x) (`2 y) h).
Qed.

(*
e' ∘ F h₀ coforks the presentation of the source: push ε across F h₀
   by counit naturality, trade ε for F α' under e' (the cofork law of
   the target), and close with the commuting square of h. 

--------
e' ∘ F h₀ 共同分叉源的呈现：将 ε 推过 F h₀
 根据单位自然性，在 e' 下用 ε 换取 F α'（cofork 定律
 目标），并以 h 的通勤平方为闭合。 
*)
Lemma crude_G_map_cofork {x y : EM} (h : x ~{EM}~> y) :
  (crude_e y ∘ fmap[F] (t_alg_hom[h])) ∘ @counit _ _ _ _ A (F (`1 x))
    ≈ (crude_e y ∘ fmap[F] (t_alg_hom[h])) ∘ fmap[F] (t_alg[`2 x]).
Proof.
  rewrite <- (comp_assoc (crude_e y) (fmap[F] (t_alg_hom[h]))
                (@counit _ _ _ _ A (F (`1 x)))).
  rewrite <- (comp_assoc (crude_e y) (fmap[F] (t_alg_hom[h]))
                (fmap[F] (t_alg[`2 x]))).
  rewrite <- (adj_counit_natural A (fmap[F] (t_alg_hom[h]))).
  rewrite (comp_assoc (crude_e y) (@counit _ _ _ _ A (F (`1 y)))
             (fmap[F] (fmap[U] (fmap[F] (t_alg_hom[h]))))).
  rewrite (crude_cofork y).
  rewrite <- (comp_assoc (crude_e y) (fmap[F] (t_alg[`2 y]))
                (fmap[F] (fmap[U] (fmap[F] (t_alg_hom[h]))))).
  rewrite <- (@fmap_comp D C F _ _ _ (t_alg[`2 y])
                (fmap[U] (fmap[F] (t_alg_hom[h])))).
  rewrite <- (crude_hom_square h).
  rewrite (@fmap_comp D C F _ _ _ (t_alg_hom[h]) (t_alg[`2 x])).
  reflexivity.
Qed.

Definition crude_G_desc {x y : EM} (h : x ~{EM}~> y) :
  ∃! u : crude_G_obj x ~{C}~> crude_G_obj y,
    u ∘ crude_e x ≈ crude_e y ∘ fmap[F] (t_alg_hom[h]) :=
  coeq_desc (crude_is_coeq x) (crude_e y ∘ fmap[F] (t_alg_hom[h]))
    (crude_G_map_cofork h).

Definition crude_G_map {x y : EM} (h : x ~{EM}~> y) :
  crude_G_obj x ~{C}~> crude_G_obj y :=
  unique_obj (crude_G_desc h).

Definition crude_G_map_commutes {x y : EM} (h : x ~{EM}~> y) :
  crude_G_map h ∘ crude_e x ≈ crude_e y ∘ fmap[F] (t_alg_hom[h]) :=
  unique_property (crude_G_desc h).

(** Functoriality of the descent, by descent uniqueness.  / 血统的功能性，源于血统的独特性。*)

Lemma crude_G_map_respects {x y : EM} (h k : x ~{EM}~> y) (E : h ≈ k) :
  crude_G_map h ≈ crude_G_map k.
Proof.
  apply (uniqueness (crude_G_desc h)).
  rewrite (crude_G_map_commutes k).
  apply compose_respects.
  - reflexivity.
  - apply fmap_respects.
    symmetry.
    exact E.
Qed.

Lemma crude_G_map_id (x : EM) : crude_G_map (@id EM x) ≈ id.
Proof.
  apply (uniqueness (crude_G_desc (@id EM x))).
  change (id ∘ crude_e x ≈ crude_e x ∘ fmap[F] (@id D (`1 x))).
  rewrite fmap_id.
  rewrite id_left.
  now rewrite id_right.
Qed.

Lemma crude_G_map_comp {x y z : EM}
  (h : y ~{EM}~> z) (k : x ~{EM}~> y) :
  crude_G_map (h ∘ k) ≈ crude_G_map h ∘ crude_G_map k.
Proof.
  apply (uniqueness (crude_G_desc (h ∘ k))).
  rewrite <- (comp_assoc (crude_G_map h) (crude_G_map k) (crude_e x)).
  rewrite (crude_G_map_commutes k).
  rewrite (comp_assoc (crude_G_map h) (crude_e y)
             (fmap[F] (t_alg_hom[k]))).
  rewrite (crude_G_map_commutes h).
  rewrite <- (comp_assoc (crude_e z) (fmap[F] (t_alg_hom[h]))
                (fmap[F] (t_alg_hom[k]))).
  rewrite <- (@fmap_comp D C F _ _ _ (t_alg_hom[h]) (t_alg_hom[k])).
  reflexivity.
Qed.

(** The quasi-inverse functor G : D^T ⟶ C.  / 拟逆函子 G : D^T ⟶ C.*)

Definition Crude_Inverse : EM ⟶ C :=
  @Build_Functor EM C
    crude_G_obj
    (fun x y h => crude_G_map h)
    (fun x y h k E => crude_G_map_respects h k E)
    (fun x => crude_G_map_id x)
    (fun x y z h k => crude_G_map_comp h k).

(**
** Downstairs: the U-image coequalizer and the canonical splitting

    Applying the preservation hypothesis to the defining coequalizer of
    G (d, α) exhibits U (G (d, α)) as a coequalizer of the pair
    U ε_{F d}, U (F α) — which is, definitionally, the canonical pair
    μ_d, T α split-coequalized by α itself ([canonical_split]). 

--------
** 楼下：U-image 协均衡器和规范分裂

 将保存假设应用于定义的协均衡器
 G (d, α) 表现出 U (G (d, α)) 作为该对的共均衡器
 U ε_{F d}, U (F α) — 定义上，这是规范对
 μ_d，T α 由 α 本身分裂共均衡 ([canonical_split])。 
*)

Definition crude_U_coeq (x : EM) :
  IsCoequalizer
    (fmap[U] (@counit _ _ _ _ A (F (`1 x))))
    (fmap[U] (fmap[F] (t_alg[`2 x])))
    (U (crude_G_obj x)) (fmap[U] (crude_e x)) :=
  pres _ _ _ _ (crude_reflexive x) _ _ (crude_is_coeq x).

Definition crude_Ue_epic (x : EM) : Epic (fmap[U] (crude_e x)) :=
  coequalizer_epic _ _ (crude_U_coeq x).

(* α coforks its own U-image pair: the algebra action law, reversed.  / α cofork 自己的 U 图像对：代数作用定律，相反。*)
Lemma crude_alpha_cofork (x : EM) :
  t_alg[`2 x] ∘ fmap[U] (@counit _ _ _ _ A (F (`1 x)))
    ≈ t_alg[`2 x] ∘ fmap[U] (fmap[F] (t_alg[`2 x])).
Proof.
  symmetry.
  exact (@t_action D (U ◯ F) HM (`1 x) (`2 x)).
Qed.

(* The comparison map U (G (d, α)) ~> d: descend α through U e.  / 比较图U(G(d,α))→d：从α下降到Ue。*)
Definition crude_to_desc (x : EM) :
  ∃! u : U (crude_G_obj x) ~{D}~> `1 x,
    u ∘ fmap[U] (crude_e x) ≈ t_alg[`2 x] :=
  coeq_desc (crude_U_coeq x) (t_alg[`2 x]) (crude_alpha_cofork x).

Definition crude_to (x : EM) : U (crude_G_obj x) ~{D}~> `1 x :=
  unique_obj (crude_to_desc x).

Definition crude_to_e (x : EM) :
  crude_to x ∘ fmap[U] (crude_e x) ≈ t_alg[`2 x] :=
  unique_property (crude_to_desc x).

(*
The inverse comparison d ~> U (G (d, α)): the split coequalizer's
   descent of U e through α, i.e. U e ∘ η_d (the section of the
   canonical splitting is the monad unit). 

--------
逆比较 d ~> U (G (d, α))：分割协均衡器的
 U e 通过 α 的下降，即 U e ∘ η_d （
 规范分裂是单子单位）。 
*)
Definition crude_from (x : EM) : `1 x ~{D}~> U (crude_G_obj x) :=
  fmap[U] (crude_e x) ∘ @unit _ _ _ _ A (`1 x).

(*
Naturality of the unit at the algebra action, with the composite
   functor spelled out. 

--------
代数作用下单位的自然性，以及复合
 函子拼写出来。 
*)
Lemma crude_unit_alpha (x : EM) :
  @unit _ _ _ _ A (`1 x) ∘ t_alg[`2 x]
    ≈ fmap[U] (fmap[F] (t_alg[`2 x])) ∘ @unit _ _ _ _ A (U (F (`1 x))).
Proof. exact (adj_unit_natural A (t_alg[`2 x])). Qed.

(*
The defining triangle of the split-side descent: restricting
   [crude_from] along α recovers U e.  Slide η across α by naturality,
   trade U (F α) for U ε under U e (the U-image of the cofork law), and
   close with the zig-zag identity. 

--------
分边下降的定义三角形：限制
 [crude_from] 沿 α 恢复 U e。 自然地将 η 滑过 α，
 在 U e（cofork 定律的 U 图像）下用 U (F α) 换取 U ε，以及
 与之字形特征接近。 
*)
Lemma crude_from_alpha (x : EM) :
  crude_from x ∘ t_alg[`2 x] ≈ fmap[U] (crude_e x).
Proof.
  unfold crude_from.
  rewrite <- (comp_assoc (fmap[U] (crude_e x))
                (@unit _ _ _ _ A (`1 x)) (t_alg[`2 x])).
  rewrite (crude_unit_alpha x).
  rewrite (comp_assoc (fmap[U] (crude_e x))
             (fmap[U] (fmap[F] (t_alg[`2 x])))
             (@unit _ _ _ _ A (U (F (`1 x))))).
  rewrite <- (@fmap_comp C D U _ _ _ (crude_e x)
                (fmap[F] (t_alg[`2 x]))).
  rewrite <- (crude_cofork x).
  rewrite (@fmap_comp C D U _ _ _ (crude_e x)
             (@counit _ _ _ _ A (F (`1 x)))).
  rewrite <- (comp_assoc (fmap[U] (crude_e x))
                (fmap[U] (@counit _ _ _ _ A (F (`1 x))))
                (@unit _ _ _ _ A (U (F (`1 x))))).
  rewrite (@fmap_counit_unit _ _ _ _ A (F (`1 x))).
  now rewrite id_right.
Qed.

(** The two comparisons are mutually inverse.  / 这两个比较是互为倒数的。*)

Lemma crude_to_from (x : EM) : crude_to x ∘ crude_from x ≈ id.
Proof.
  unfold crude_from.
  rewrite (comp_assoc (crude_to x) (fmap[U] (crude_e x))
             (@unit _ _ _ _ A (`1 x))).
  rewrite (crude_to_e x).
  exact (crude_alg_unit x).
Qed.

Lemma crude_from_to (x : EM) : crude_from x ∘ crude_to x ≈ id.
Proof.
  apply (@epic _ _ _ _ (crude_Ue_epic x)).
  rewrite <- (comp_assoc (crude_from x) (crude_to x)
                (fmap[U] (crude_e x))).
  rewrite (crude_to_e x).
  rewrite (crude_from_alpha x).
  now rewrite id_left.
Qed.

(**
** The counit of the equivalence: K (G (d, α)) ≅ (d, α) in D^T

    [crude_from] underlies an algebra homomorphism from (d, α) to the
    comparison algebra (U (G x), U ε): the square reduces, after
    splitting the composites, to counit naturality at e followed by the
    zig-zag identity ε F ∘ F η ≈ id. 

--------
** 等价单位：D^T 中的 K (G (d, α)) ≅ (d, α)

 [crude_from] 是从 (d, α) 到 (d, α) 的代数同态的基础
 比较代数(U(G x),U ε)：平方减少，经过
 分裂复合材料，计算 e 处的自然性，然后是
 之字形恒等式 ε F ∘ F η ≈ id。 
*)

Lemma crude_from_commutes (x : EM) :
  crude_from x ∘ t_alg[`2 x]
    ≈ fmap[U] (@counit _ _ _ _ A (crude_G_obj x))
        ∘ fmap[U] (fmap[F] (crude_from x)).
Proof.
  rewrite (crude_from_alpha x).
  unfold crude_from.
  rewrite (@fmap_comp D C F _ _ _ (fmap[U] (crude_e x))
             (@unit _ _ _ _ A (`1 x))).
  rewrite (@fmap_comp C D U _ _ _ (fmap[F] (fmap[U] (crude_e x)))
             (fmap[F] (@unit _ _ _ _ A (`1 x)))).
  rewrite (comp_assoc (fmap[U] (@counit _ _ _ _ A (crude_G_obj x)))
             (fmap[U] (fmap[F] (fmap[U] (crude_e x))))
             (fmap[U] (fmap[F] (@unit _ _ _ _ A (`1 x))))).
  rewrite <- (@fmap_comp C D U _ _ _
                (@counit _ _ _ _ A (crude_G_obj x))
                (fmap[F] (fmap[U] (crude_e x)))).
  rewrite (adj_counit_natural A (crude_e x)).
  rewrite (@fmap_comp C D U _ _ _ (crude_e x)
             (@counit _ _ _ _ A (F (`1 x)))).
  rewrite <- (comp_assoc (fmap[U] (crude_e x))
                (fmap[U] (@counit _ _ _ _ A (F (`1 x))))
                (fmap[U] (fmap[F] (@unit _ _ _ _ A (`1 x))))).
  rewrite <- (@fmap_comp C D U _ _ _
                (@counit _ _ _ _ A (F (`1 x)))
                (fmap[F] (@unit _ _ _ _ A (`1 x)))).
  rewrite (@counit_fmap_unit _ _ _ _ A (`1 x)).
  rewrite fmap_id.
  now rewrite id_right.
Qed.

(* The homomorphism (d, α) ~> K (G (d, α)) carried by [crude_from].  / [crude_from]携带的同态(d,α)→K(G(d,α))。*)
Definition crude_counit_hom_inv (x : EM) :
  x ~{EM}~> K (crude_G_obj x) :=
  @Build_TAlgebraHom D (U ◯ F) HM (`1 x) (U (crude_G_obj x))
    (`2 x) (EM_Comparison_Algebra A (crude_G_obj x))
    (crude_from x) (crude_from_commutes x).

(* Its carrier is invertible, transparently.  / 其载体是可翻转的、透明的。*)
Definition crude_from_is_iso (x : EM) : IsIsomorphism (crude_from x) :=
  {| two_sided_inverse := crude_to x
   ; is_right_inverse  := crude_from_to x
   ; is_left_inverse   := crude_to_from x |}.

(*
The inverse homomorphism K (G (d, α)) ~> (d, α): conjugating the
   commuting square by the inverse carrier — the conservativity kernel
   [em_iso_inverse_hom] of BeckObjects.v, kept transparent so that its
   carrier is [crude_to] on the nose. 

--------
反同态 K (G (d, α)) ~> (d, α)：共轭
 逆载体的通勤平方——保守性核
 BeckObjects.v 的 [em_iso_inverse_hom]，保持透明，以便其
 载体是鼻子上的 [crude_to]。 
*)
Definition crude_counit_hom (x : EM) :
  K (crude_G_obj x) ~{EM}~> x :=
  @em_iso_inverse_hom D (U ◯ F) HM x (K (crude_G_obj x))
    (crude_counit_hom_inv x) (crude_from_is_iso x).

(*
The counit component, as an isomorphism of D^T; the inverse laws are
   those of the carriers, since hom-equivalence upstairs is carrier
   equivalence. 

--------
单位分量，作为 D^T 的同构； 逆定律是
 那些运营商的，因为楼上的家相当于运营商
 等价性。 
*)
Definition crude_counit_component (x : EM) :
  @Isomorphism EM (K (crude_G_obj x)) x :=
  @Build_Isomorphism EM (K (crude_G_obj x)) x
    (crude_counit_hom x) (crude_counit_hom_inv x)
    (crude_to_from x) (crude_from_to x).

(*
Conjugation coherence of the counit cell, on carriers: cancel the
   epimorphism U e, contract the two descent triangles, and close with
   the commuting square of h. 

--------
载体上共基元的共轭相干性：取消
 外态 U e，收缩两个下降三角形，并以
 h的通勤广场。 
*)
Lemma crude_counit_coherence {x y : EM} (h : x ~{EM}~> y) :
  fmap[U] (crude_G_map h)
    ≈ (crude_from y ∘ t_alg_hom[h]) ∘ crude_to x.
Proof.
  apply (@epic _ _ _ _ (crude_Ue_epic x)).
  rewrite <- (comp_assoc (crude_from y ∘ t_alg_hom[h]) (crude_to x)
                (fmap[U] (crude_e x))).
  rewrite (crude_to_e x).
  rewrite <- (comp_assoc (crude_from y) (t_alg_hom[h]) (t_alg[`2 x])).
  rewrite (crude_hom_square h).
  rewrite (comp_assoc (crude_from y) (t_alg[`2 y])
             (fmap[U] (fmap[F] (t_alg_hom[h])))).
  rewrite (crude_from_alpha y).
  rewrite <- (@fmap_comp C D U _ _ _ (crude_G_map h) (crude_e x)).
  rewrite <- (@fmap_comp C D U _ _ _ (crude_e y)
                (fmap[F] (t_alg_hom[h]))).
  rewrite (crude_G_map_commutes h).
  reflexivity.
Qed.

Definition crude_equivalence_counit : K ◯ Crude_Inverse ≈ Id[EM].
Proof using A C D F RC U pres.
  exists (fun x => crude_counit_component x).
  intros x y h.
  exact (crude_counit_coherence h).
Defined.

(**
** The unit of the equivalence: c ≅ G (K c) in C

    The counit ε_c coforks the presentation of the comparison algebra
    K c = (U c, U ε_c), by counit naturality, and therefore descends to
    a mediator θ_c out of the coequalizer G (K c). 

--------
** 等价单位：C ≅ G (K c)

 计算单位 ε_c 分叉比较代数的表示
 K c = (U c, U ε_c)，按单位自然性，因此下降为
 协均衡器 G (K c) 中的中介器 θ_c。 
*)

Lemma crude_unit_cofork (c : C) :
  @counit _ _ _ _ A c ∘ @counit _ _ _ _ A (F (U c))
    ≈ @counit _ _ _ _ A c ∘ fmap[F] (fmap[U] (@counit _ _ _ _ A c)).
Proof.
  symmetry.
  exact (adj_counit_natural A (@counit _ _ _ _ A c)).
Qed.

Definition crude_unit_desc (c : C) :
  ∃! u : crude_G_obj (K c) ~{C}~> c,
    u ∘ crude_e (K c) ≈ @counit _ _ _ _ A c :=
  coeq_desc (crude_is_coeq (K c)) (@counit _ _ _ _ A c)
    (crude_unit_cofork c).

Definition crude_theta (c : C) : crude_G_obj (K c) ~{C}~> c :=
  unique_obj (crude_unit_desc c).

Definition crude_theta_e (c : C) :
  crude_theta c ∘ crude_e (K c) ≈ @counit _ _ _ _ A c :=
  unique_property (crude_unit_desc c).

(*
Downstairs, U θ_c is the comparison iso of the algebra K c: both
   descend U ε_c through U e, so the epimorphism U e identifies them. 

--------
楼下，U θ_c 是代数 K c 的比较 iso：两者
 U ε_c 下降到 U e，因此外同态 U e 识别了它们。 
*)
Lemma crude_U_theta (c : C) :
  fmap[U] (crude_theta c) ≈ crude_to (K c).
Proof.
  apply (@epic _ _ _ _ (crude_Ue_epic (K c))).
  rewrite (crude_to_e (K c)).
  rewrite <- (@fmap_comp C D U _ _ _ (crude_theta c) (crude_e (K c))).
  rewrite (crude_theta_e c).
  reflexivity.
Qed.

Lemma crude_U_theta_from (c : C) :
  fmap[U] (crude_theta c) ∘ crude_from (K c) ≈ id.
Proof using A C D F RC U pres.
  rewrite (crude_U_theta c).
  exact (crude_to_from (K c)).
Qed.

Lemma crude_from_U_theta (c : C) :
  crude_from (K c) ∘ fmap[U] (crude_theta c) ≈ id.
Proof using A C D F RC U pres.
  rewrite (crude_U_theta c).
  exact (crude_from_to (K c)).
Qed.

Definition crude_theta_U_iso (c : C) :
  IsIsomorphism (fmap[U] (crude_theta c)) :=
  {| two_sided_inverse := crude_from (K c)
   ; is_right_inverse  := crude_U_theta_from c
   ; is_left_inverse   := crude_from_U_theta c |}.

(* Conservativity of U reflects the invertibility upstairs.  / U的保守性反映了楼上的可逆性。*)
Definition crude_theta_iso (c : C) : IsIsomorphism (crude_theta c) :=
  @reflects_iso C D U refl _ _ (crude_theta c) (crude_theta_U_iso c).

Definition crude_theta_inv (c : C) : c ~{C}~> crude_G_obj (K c) :=
  @two_sided_inverse C _ _ (crude_theta c) (crude_theta_iso c).

Lemma crude_theta_theta_inv (c : C) :
  crude_theta c ∘ crude_theta_inv c ≈ id.
Proof.
  exact (@is_right_inverse C _ _ (crude_theta c) (crude_theta_iso c)).
Qed.

Definition crude_unit_component (c : C) : c ≅ crude_G_obj (K c) :=
  @Build_Isomorphism C c (crude_G_obj (K c))
    (crude_theta_inv c) (crude_theta c)
    (@is_left_inverse C _ _ (crude_theta c) (crude_theta_iso c))
    (@is_right_inverse C _ _ (crude_theta c) (crude_theta_iso c)).

(*
Naturality of θ: cancel the epimorphism e, contract the descent
   triangles of θ and of G (K f), and finish by counit naturality. 

--------
θ的自然性：取消同态e，收缩下降
 θ 和 G (K f) 的三角形，并按单位自然性完成。 
*)
Lemma crude_theta_natural {x y : C} (f : x ~{C}~> y) :
  f ∘ crude_theta x ≈ crude_theta y ∘ crude_G_map (fmap[K] f).
Proof.
  apply (@epic _ _ _ _ (crude_e_epic (K x))).
  rewrite <- (comp_assoc f (crude_theta x) (crude_e (K x))).
  rewrite (crude_theta_e x).
  rewrite <- (comp_assoc (crude_theta y) (crude_G_map (fmap[K] f))
                (crude_e (K x))).
  rewrite (crude_G_map_commutes (fmap[K] f)).
  rewrite (comp_assoc (crude_theta y) (crude_e (K y))
             (fmap[F] (t_alg_hom[fmap[K] f]))).
  rewrite (crude_theta_e y).
  symmetry.
  exact (adj_counit_natural A f).
Qed.

(* Conjugation coherence of the unit cell.  / 晶胞的共轭相干性。*)
Lemma crude_unit_coherence {x y : C} (f : x ~{C}~> y) :
  f ≈ (crude_theta y ∘ crude_G_map (fmap[K] f)) ∘ crude_theta_inv x.
Proof.
  rewrite <- (crude_theta_natural f).
  rewrite <- (comp_assoc f (crude_theta x) (crude_theta_inv x)).
  rewrite (crude_theta_theta_inv x).
  now rewrite id_right.
Qed.

Definition crude_equivalence_unit : Id[C] ≈ Crude_Inverse ◯ K.
Proof using A C D F RC U pres refl.
  exists (fun c => crude_unit_component c).
  intros x y f.
  exact (crude_unit_coherence f).
Defined.

(** ** The crude monadicity theorem  / ** 粗单性定理*)

Definition crude_monadicity : EquivalenceOfCategories (EM_Comparison A) :=
  {| quasi_inverse      := Crude_Inverse
   ; equivalence_counit := crude_equivalence_counit
   ; equivalence_unit   := crude_equivalence_unit |}.

End CrudeMonadicity.
