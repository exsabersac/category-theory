Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Equalizer.
Require Import Category.Instance.Parallel.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(* * * Coequalizers, elementarily: coforks and descent / * * 协等化器，基础上：共叉和下行 *)

(*
 nLab:      https://ncatlab.org/nlab/show/coequalizer
 Wikipedia: https://en.wikipedia.org/wiki/Coequaliser

 Given a parallel pair f, g : x ~> y in C, a coequalizer is an object q
 together with a coequalizing map e : y ~> q forming a "cofork" over the
 pair,

 e ∘ f ≈ e ∘ g,

 that is universal with this property: every h : y ~> z with
 h ∘ f ≈ h ∘ g descends uniquely through e, i.e. there is a unique
 u : q ~> z with u ∘ e ≈ h (Wikipedia; nLab presents the same universal
 property as the pushout-style colimit of the parallel pair).

 [Structure/Equalizer.v] already presents the coequalizer as a colimit
 over the walking parallel pair ([Coequalizer (APair f g) :=
 Colimit (APair f g)]).  This file provides the elementary, fork-shaped
 presentation [IsCoequalizer] together with conversions in both
 directions showing that the two presentations coincide:

 - [coequalizer_is_coequalizer] reads a colimit of [APair f g] as an
 elementary coequalizer at its apex, coequalized by the colimit
 injection over [ParY];
 - [is_coequalizer_colimit] rebuilds the bundled colimit from the
 elementary data.

 Uniqueness of the coequalizer object up to isomorphism
 ([coequalizer_unique]) and the classical fact that coequalizing maps
 are epimorphisms ([coequalizer_epic]; Wikipedia: "every coequalizer is
 an epimorphism") complete the API.  [HasCoequalizers] packages a choice
 of elementary coequalizer for every parallel pair.

 Since #477 both conversions also hold for an arbitrary diagram
 [K : Parallel ⟶ C], at the pair it names ([parallel_coequalizer_colimit]
 and [parallel_colimit_coequalizer], in the last section), and
 [HasCoequalizers_HasColimitsOfShape] turns a choice of elementary
 coequalizers into a colimit of every such diagram.  Since #481,
 [parallel_cocone_coequalizer_colimit] reads a GIVEN cocone over such
 a diagram as colimiting when its injection over [ParY] is an
 elementary coequalizer of the pair. 

 --------
 nLab:       https://ncatlab.org/nlab/show/coequalizer 
 维基百科:  https://en.wikipedia.org/wiki/Coequaliser 

 给定 C 中的一对平行箭头 f, g : x ~> y，余等化子是一个对象 q，以及一个共等化映射 e : y ~> q，形成该对的“共叉”，

 e ∘ f ≈ e ∘ g，

 并且具备这个性质的普遍性：每个 h : y ~> z 满足
 h ∘ f ≈ h ∘ g 都可以唯一地通过 e 下去，即存在唯一的
 u : q ~> z 使得 u ∘ e ≈ h（维基百科；nLab 将相同的普遍性质表示为平行箭头对的推出式余极限）。

 [Structure/Equalizer.v] 已经将余等化子表示为走动平行箭头的余极限
 ([Coequalizer (APair f g) := Colimit (APair f g)]).  本文件提供了基本的、叉状的表示 [IsCoequalizer]，并且提供了双向转换，显示这两种表示是一致的：- [coequalizer_is_coequalizer] 将 [APair f g] 的一个余极限读取为其顶点处的基本等化器，由 [ParY] 上的余极限注入进行等化；
 - [is_coequalizer_colimit] 从基本数据重建捆绑的余极限。

 等化器对象的唯一性（最多到同构，[coequalizer_unique]）以及经典事实：等化映射是满射（[coequalizer_epic]；维基百科：“每个等化器都是满射”）完成了 API。[HasCoequalizers] 为每一对平行映射打包选择了一个基本等化器。自 #477 起，这两种转换也适用于任意图 [K : Parallel ⟶ C]，在其所指定的对 ([parallel_coequalizer_colimit] 和 [parallel_colimit_coequalizer]，在最后一节中)，并且 [HasCoequalizers_HasColimitsOfShape] 将一个初等共等化器的选择变成每个此类图的余极限。自 #481 起，当 [parallel_cocone_coequalizer_colimit] 读取此类图上的给定锥时，如果其在 [ParY] 上的注入是该对的初等共等化器，则它被视为余极限。
*)

(*
 The elementary universal property: e coforks the pair f, g at q, and
 every coforking map h out of y descends uniquely across e. 

 --------
 基本的泛性质：e 在 q 上对 f、g 形成余共轭，并且每一个从 y 出发的余共轭映射 h 都唯一地沿 e 下降。
*)
Record IsCoequalizer {C : Category} {x y : C} (f g : x ~> y)
  (q : C) (e : y ~> q) := {
  (* the coequalizing map absorbs the parallel pair / 共等化映射吸收平行对 *)
  cofork : e ∘ f ≈ e ∘ g;

  (*
 universal property: every coforking map h descends uniquely through e 

 --------
 泛性质：每个共分叉映射 h 都可以唯一地通过 e 下降
*)
  coeq_desc {z} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
    ∃! u : q ~> z, u ∘ e ≈ h
}.

Arguments cofork {_ _ _ _ _ _ _} _.
Arguments coeq_desc {_ _ _ _ _ _ _} _ {_} _ _.

(*
 A category has all (binary) coequalizers when every parallel pair
 carries an elementary coequalizer.  This is the coequalizer analogue of
 [HasPullbacks] in [Structure/Pullback.v]. 

 --------
 当每一对平行箭头都拥有一个基本的余等化器时，一个范畴就具有所有（二元）余等化器。这是 [Structure/Pullback.v] 中 [HasPullbacks] 的余等化器类比。
*)
Class HasCoequalizers (C : Category) := {
  coeq {x y : C} (f g : x ~> y) : ∃ (q : C) (e : y ~> q), IsCoequalizer f g q e
}.

Section CoequalizerColimit.

Context {C : Category}.
Context {x y : C}.
Context (f g : x ~> y).

(* * ** Coequalizing maps are epimorphisms / * ** 共等化映射是满射 *)

(*
 Wikipedia: "every coequalizer is an epimorphism"; both descents of
 g1 ∘ e agree with the canonical one, so descent uniqueness cancels e on
 the right. 

 --------
 维基百科：“每个等化子都是一个满射”； g1 ∘ e 的两个下行与规范的下行一致，因此下行的唯一性在右边抵消了 e。
*)
Lemma coequalizer_epic {q : C} {e : y ~> q} (E : IsCoequalizer f g q e) :
  Epic e.
Proof.
  constructor.
  intros z g1 g2 Hg.
  assert (Hfork : (g1 ∘ e) ∘ f ≈ (g1 ∘ e) ∘ g).
  { rewrite <- !comp_assoc.
    rewrite (cofork E).
    reflexivity. }
  transitivity (unique_obj (coeq_desc E (g1 ∘ e) Hfork)).
  - symmetry.
    apply (uniqueness (coeq_desc E (g1 ∘ e) Hfork)).
    reflexivity.
  - apply (uniqueness (coeq_desc E (g1 ∘ e) Hfork)).
    symmetry.
    exact Hg.
Qed.

(* * ** Coequalizers are unique up to isomorphism / * ** 共轭化子在同构下是唯一的 *)

(*
 Mirrors [pullback_unique] in [Structure/Pullback.v]: each coequalizer
 descends the other's coequalizing map, and both round-trips descend the
 identity, so descent uniqueness identifies them with id. 

 --------
 镜像 [pullback_unique] 在 [Structure/Pullback.v] 中：每个联合余积下降对方的联合余积映射，并且两个往返都下降恒等映射，因此下降的唯一性将它们与 id 识别。
*)
Lemma coequalizer_unique {q1 q2 : C} {e1 : y ~> q1} {e2 : y ~> q2}
  (E1 : IsCoequalizer f g q1 e1) (E2 : IsCoequalizer f g q2 e2) :
  q1 ≅ q2.
Proof.
  pose proof (coeq_desc E1 e2 (cofork E2)) as D12.
  pose proof (coeq_desc E2 e1 (cofork E1)) as D21.
  pose proof (coeq_desc E1 e1 (cofork E1)) as D11.
  pose proof (coeq_desc E2 e2 (cofork E2)) as D22.
  unshelve refine {| to := unique_obj D12; from := unique_obj D21 |}.
  - (* to ∘ from ≈ id[q2], by uniqueness of descent against D22 / 到 ∘ 从 ≈ id [q2]，由于针对 D22 的下降唯一性 *)
    transitivity (unique_obj D22).
    + symmetry.
      apply (uniqueness D22).
      rewrite <- comp_assoc.
      rewrite (unique_property D21).
      exact (unique_property D12).
    + apply (uniqueness D22).
      apply id_left.
  - (* from ∘ to ≈ id[q1], by uniqueness of descent against D11 / 从 ∘ 到 ≈ id [q1]，由于针对 D11 的下降唯一性 *)
    transitivity (unique_obj D11).
    + symmetry.
      apply (uniqueness D11).
      rewrite <- comp_assoc.
      rewrite (unique_property D12).
      exact (unique_property D21).
    + apply (uniqueness D11).
      apply id_left.
Qed.

(*
   * ** From a coforking map to a cocone over the walking parallel pair 

   --------
   * ** 从共分叉映射到行走平行对上的余锥
*)

(*
 The legs of the cocone induced by a coforking map h: the leg over ParX
 is the common composite h ∘ f, the leg over ParY is h itself. 

 --------
 由共分叉映射 h 诱导的共圆锥的各条腿：位于 ParX 上的腿是公共复合 h ∘ f，位于 ParY 上的腿是 h 本身。
*)
Definition cofork_legs {z : C} (h : y ~> z) (p : ParObj) :
  APair f g p ~{C}~> z :=
  match p return (APair f g p ~{C}~> z) with
  | ParX => h ∘ f
  | ParY => h
  end.

(*
 Leg coherence, phrased covariantly in C: precomposing the leg at the
 codomain of any Parallel arrow with its image recovers the leg at the
 domain.  This statement is definitionally the [cone_coherence] field of
 an [ACone] over (APair f g)^op, since composition and hom-equivalence
 in C^op are those of C, flipped. 

 --------
 腿的相干性，在 C 中以协变方式表述：将任何 Parallel 箭头上的腿在余域处与其像预组合，可以恢复在定义域的腿。这个说法在定义上是定义在 (APair f g)^op 上的 [ACone] 的 [cone_coherence] 场，因为 C^op 中的组合和同态等价是 C 中的组合和同态等价，只是方向相反。
*)
Lemma cofork_legs_coherence {z : C} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
  ∀ (a b : ParObj) (k : b ~{Parallel}~> a),
    cofork_legs h a ∘ fmap[APair f g] k ≈ cofork_legs h b.
Proof.
  intros a b k.
  destruct a, b.
  - (* identity arrow on ParX / ParX 上的身份箭头 *)
    simpl.
    apply id_right.
  - (* an arrow ParY ~> ParX: refuted / 一支箭 ParY ~> ParX：被驳斥 *)
    destruct k as [bb hk].
    destruct (ParHom_Y_X_absurd _ hk).
  - (* the two arrows ParX ~> ParY, sent to f and g / 两个箭头 ParX ~> ParY，发送到 f 和 g *)
    destruct k as [bb hk].
    destruct bb.
    + (* (true; ParOne), sent to f / (真; ParOne), 发送给 f *)
      reflexivity.
    + (* (false; ParTwo), sent to g / (错误；第二部分)，发送给 g *)
      symmetry.
      exact Hh.
  - (* identity arrow on ParY / ParY 上的身份箭头 *)
    simpl.
    apply id_right.
Qed.

(*
 The cocone over APair f g induced by a coforking map. 

 --------
 由共分叉映射诱导的 APair f g 上的余圆锥。
*)
Definition cofork_cocone {z : C} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
  Cocone (APair f g) :=
  @Build_Cone (Parallel^op) (C^op) ((APair f g)^op) z
    (@Build_ACone (Parallel^op) (C^op) z ((APair f g)^op)
       (cofork_legs h) (cofork_legs_coherence h Hh)).

(* * ** From the colimit presentation to the elementary one / * ** 从余极限表示到初等表示 *)

(*
 The colimit injection over ParY coforks the pair: both composites agree
 with the injection over ParX, by leg coherence at the two nonidentity
 arrows of the walking parallel pair. 

 --------
 在 ParY 上的余极限注入共叉该对：通过行连贯性，在平行对行走的两个非恒等箭头上，两个复合都与 ParX 上的注入一致。
*)
Lemma colimit_coequalizes (L : Coequalizer (APair f g)) :
  colimit_inj (colimit_is_acolimit L) ParY ∘ f
    ≈ colimit_inj (colimit_is_acolimit L) ParY ∘ g.
Proof.
  transitivity (colimit_inj (colimit_is_acolimit L) ParX).
  - exact (colimit_inj_coherence (colimit_is_acolimit L)
             ((true; ParOne) : ParX ~{Parallel}~> ParY)).
  - symmetry.
    exact (colimit_inj_coherence (colimit_is_acolimit L)
             ((false; ParTwo) : ParX ~{Parallel}~> ParY)).
Qed.

(*
 Descent through the colimit apex: mediate out of the colimit into the
 cocone induced by the coforking map. 

 --------
 通过余极顶下降：从余极调解到由共分叉映射引起的余锥中。
*)
Lemma colimit_coequalizer_desc (L : Coequalizer (APair f g))
  {z : C} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
  ∃! u : colimit_apex L ~> z,
    u ∘ colimit_inj (colimit_is_acolimit L) ParY ≈ h.
Proof.
  unshelve eapply Build_Unique.
  - exact (colimit_med (colimit_is_acolimit L) (cofork_cocone h Hh)).
  - exact (colimit_med_commutes
             (colimit_is_acolimit L) (cofork_cocone h Hh) ParY).
  - intros v Hv.
    refine (colimit_med_unique
              (colimit_is_acolimit L) (cofork_cocone h Hh) v _).
    intros p.
    destruct p.
    + (* the ParX leg follows from the ParY leg via coherence / ParX 段通过相干性由 ParY 段推导得出 *)
      rewrite <- (colimit_inj_coherence (colimit_is_acolimit L)
                    ((true; ParOne) : ParX ~{Parallel}~> ParY)).
      rewrite comp_assoc.
      rewrite Hv.
      reflexivity.
    + exact Hv.
Qed.

(*
 A colimit of APair f g is an elementary coequalizer at its apex. 

 --------
 APair f g 的余极限在其顶点处是一个基本的等化器。
*)
Definition coequalizer_is_coequalizer (L : Coequalizer (APair f g)) :
  IsCoequalizer f g (colimit_apex L)
    (colimit_inj (colimit_is_acolimit L) ParY) :=
  {| cofork    := colimit_coequalizes L
   ; coeq_desc := fun z h Hh => colimit_coequalizer_desc L h Hh |}.

(* * ** From the elementary presentation back to the colimit / * ** 从基本表示回到余极限 *)

(*
 The colimit cocone of an elementary coequalizer: legs e ∘ f and e over
 ParX and ParY. 

 --------
 一个初等余等化器的余极限余锥：经过 ParX 和 ParY 的 e ∘ f 和 e 两条腿。
*)
Definition is_coequalizer_cocone {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) : Cocone (APair f g) :=
  cofork_cocone e (cofork E).

(*
 The universal property of that cocone, phrased covariantly in C; this
 statement is definitionally the [ump_limits] field of the colimit
 ([Limit ((APair f g)^op)]) whose limit cone is [is_coequalizer_cocone]. 

 --------
 该余锥的泛性质，以C中的协变方式表述；该陈述在定义上是该余极限（[Limit ((APair f g)^op)]）的场（[ump_limits]），其极限锥为[is_coequalizer_cocone]。
*)
Lemma is_coequalizer_cocone_ump {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) (N : Cocone (APair f g)) :
  ∃! u : q ~> vertex_obj[N],
    ∀ p : ParObj, u ∘ cofork_legs e p ≈ cocone_inj N p.
Proof.
  assert (HX1 : cocone_inj N ParY ∘ f ≈ cocone_inj N ParX).
  { exact (cocone_inj_coherence N
             ((true; ParOne) : ParX ~{Parallel}~> ParY)). }
  assert (HX2 : cocone_inj N ParY ∘ g ≈ cocone_inj N ParX).
  { exact (cocone_inj_coherence N
             ((false; ParTwo) : ParX ~{Parallel}~> ParY)). }
  assert (Hfg : cocone_inj N ParY ∘ f ≈ cocone_inj N ParY ∘ g).
  { rewrite HX1.
    rewrite HX2.
    reflexivity. }
  unshelve eapply Build_Unique.
  - exact (unique_obj (coeq_desc E (cocone_inj N ParY) Hfg)).
  - intros p.
    destruct p.
    + (* leg over ParX: u ∘ (e ∘ f) ≈ nX via the ParY triangle / 通过 ParY 三角形的 ParX 上的腿：u ∘ (e ∘ f) ≈ nX *)
      simpl.
      rewrite comp_assoc.
      rewrite (unique_property (coeq_desc E (cocone_inj N ParY) Hfg)).
      exact HX1.
    + exact (unique_property (coeq_desc E (cocone_inj N ParY) Hfg)).
  - intros v Hv.
    apply (uniqueness (coeq_desc E (cocone_inj N ParY) Hfg)).
    exact (Hv ParY).
Qed.

(*
 An elementary coequalizer yields the bundled colimit over the walking
 parallel pair. 

 --------
 一个初等共同化子产生围绕行走的平行对的捆绑余极限。
*)
Definition is_coequalizer_colimit {q : C} {e : y ~> q}
  (E : IsCoequalizer f g q e) : Coequalizer (APair f g) :=
  {| limit_cone := is_coequalizer_cocone E
   ; ump_limits := fun N => is_coequalizer_cocone_ump E N |}.

End CoequalizerColimit.

(* * ** Coequalizers of any diagram of parallel-pair shape / * ** 任意平行对形状图的等同化子 *)

(*
 The section above converts at the diagram [APair f g] that a pair
 determines.  A functor [K : Parallel ⟶ C] need not be such a record on
 the nose -- [U ◯ APair f g] is not [APair (fmap[U] f) (fmap[U] g)] at
 [eq_refl] (Test/ProbeComponents462.v, N9) -- but it names a pair, the
 images under K of the two arrows of [Parallel], and both conversions
 hold for every such K, by case analysis on the two objects (#477):

 - [parallel_coequalizer_colimit]: an elementary coequalizer of the
 pair is a colimiting cocone over K, the cocone
 [parallel_cofork_cocone] of its coforking map;
 - [parallel_colimit_coequalizer]: ANY colimiting cocone over K is an
 elementary coequalizer of the pair at its apex, coequalized by its
 injection over [ParY];
 - [parallel_cocone_coequalizer_colimit], its converse for a GIVEN
 cocone (#481): a cocone over K whose injection over [ParY] is an
 elementary coequalizer of the pair is colimiting, being the
 cocone of the first conversion up to a cone isomorphism whose apex
 map is the identity (its injection over [ParX] agreeing by
 coherence);
 - [HasCoequalizers_HasColimitsOfShape]: chosen elementary
 coequalizers give every such K a colimit.

 At [K := APair f g] the pair is f, g by conversion, and the first two
 have the types of [is_coequalizer_cocone_ump] (as an
 [IsColimitCocone]) and of [coequalizer_is_coequalizer]; at
 [K := U ◯ APair f g] the pair is [fmap[U] f], [fmap[U] g], so a
 colimiting cocone over the image diagram is an elementary coequalizer
 of the image pair with no identification of the two diagrams (all
 three accepted in Test/ProbeAbsolute477.v).  The two conversions above
 keep their own proofs.  [parallel_cofork_cocone] has the legs of
 [cofork_cocone] at [APair f g] by conversion, and its coherence proof
 is its own. 

 --------
 上面的部分将在图 [APair f g] 上进行转换，该图由一对元素确定。函子 [K : Parallel ⟶ C] 不一定要完全是这样的记录——[U ◯ APair f g] 不是 [APair (fmap[U] f) (fmap [U] g)] 在 [eq_refl] (Test/ProbeComponents462.v, N9)——但它命名了一对元素，即 [Parallel] 的两个箭头在 K 下的像，并且对于每一个这样的 K，这两种转换都成立，通过对这两个对象进行情况分析 (#477):- [parallel_coequalizer_colimit]：该对的一个初等余等化器是 K 上的一个余极锥，是其共叉映射的余锥 [parallel_cofork_cocone]；
 - [parallel_colimit_coequalizer]：任何 K 上的余极锥都是该对在其顶点上的一个初等余等化器，由其在 [ParY] 上的注入余等化；
 - [parallel_cocone_coequalizer_colimit]，其逆定理对于给定的余锥 (#481)：K 上的一个余锥，其在 [ParY] 上的注入是该对的初等余等化器，则该余锥是余极锥，为第一个变换的余锥，直到余锥同构，其顶点映射是恒等映射（其在 [ParX] 上的注入由一致性规定）；
 - [HasCoequalizers_HasColimitsOfShape]：选定的初等余等化器为每个这样的 K 提供了一个余极。在 [K := APair f g] 中，这一对通过转换是 f, g，并且前两个具有 [is_coequalizer_cocone_ump] 的类型（作为 [IsColimitCocone]）和 [coequalizer_is_coequalizer] 的类型；在 [K := U ◯ APair f g] 中，这一对是 [fmap[U] f], [fmap[U] g]，因此图像图上的余极限余锥是图像对的一个基本余等化器，并且没有对两个图进行识别（在 Test/ProbeAbsolute477.v 中全部被接受）。上述两个转换保持它们各自的证明。[parallel_cofork_cocone] 在 [APair f g] 上具有 [cofork_cocone] 的边，通过转换，并且其一致性证明是它自己的。
*)

Section ParallelDiagram.

(*
 The shape's hom level is C's, written in the binder as [APair] writes
 it: [Cocone K] identifies the two (Structure/Cone.v), and left to
 Rocq the identification lands in the constraint block as an equation
 instead. 

 --------
 该形状的同调层次为 C 的，在活页夹中写作 [APair]，写作它：[Cocone K] 识别了两个（Structure/Cone.v），并且留给 Rocq 时，识别反而以方程的形式落在约束块中。
*)

Universes co ch po.
Context {C : Category@{co ch ch}}.
Context (K : Parallel@{po ch} ⟶ C).

(*
 The pair K names: the images of the two arrows ParX ~> ParY. 

 --------
 这对 K 名称：两个箭头 ParX ~> ParY 的图像。
*)

Local Notation par1 := (fmap[K] ((true; ParOne) : ParX ~{Parallel}~> ParY)).
Local Notation par2 := (fmap[K] ((false; ParTwo) : ParX ~{Parallel}~> ParY)).

Definition parallel_cofork_legs {z : C} (h : K ParY ~> z) (p : ParObj) :
  K p ~> z :=
  match p return (K p ~> z) with
  | ParX => h ∘ par1
  | ParY => h
  end.

Lemma parallel_cofork_legs_coherence {z : C} (h : K ParY ~> z)
  (Hh : h ∘ par1 ≈ h ∘ par2) :
  ∀ (a b : ParObj) (k : b ~{Parallel}~> a),
    parallel_cofork_legs h a ∘ fmap[K] k ≈ parallel_cofork_legs h b.
Proof.
  intros a b k.
  destruct a, b.
  - (* an endomorphism of ParX: the identity / ParX 的一个自同态：恒等映射 *)
    destruct k as [[|] hk].
    + transitivity (parallel_cofork_legs h ParX ∘ id).
      * apply compose_respects; [reflexivity|].
        rewrite <- fmap_id.
        apply fmap_respects.
        reflexivity.
      * apply id_right.
    + destruct (ParHom_Id_false_absurd _ hk).
  - (* an arrow ParY ~> ParX: refuted / 一支箭 ParY ~> ParX：被驳斥 *)
    destruct k as [bb hk].
    destruct (ParHom_Y_X_absurd _ hk).
  - (* the two arrows ParX ~> ParY / 两个箭头 ParX ~> ParY *)
    destruct k as [[|] hk]; simpl.
    + apply compose_respects; [reflexivity|].
      apply fmap_respects.
      reflexivity.
    + symmetry.
      rewrite Hh.
      apply compose_respects; [reflexivity|].
      apply fmap_respects.
      reflexivity.
  - (* an endomorphism of ParY: the identity / ParY 的一个自同态：恒等映射 *)
    destruct k as [[|] hk].
    + transitivity (parallel_cofork_legs h ParY ∘ id).
      * apply compose_respects; [reflexivity|].
        rewrite <- fmap_id.
        apply fmap_respects.
        reflexivity.
      * apply id_right.
    + destruct (ParHom_Id_false_absurd _ hk).
Qed.

(*
 The cocone over K induced by a coforking map of the pair. 

 --------
 由该对的共分叉映射引起的 K 上的余顶点。
*)

Definition parallel_cofork_cocone {z : C} (h : K ParY ~> z)
  (Hh : h ∘ par1 ≈ h ∘ par2) : Cocone K :=
  @Build_Cone (Parallel^op) (C^op) (K^op) z
    (@Build_ACone (Parallel^op) (C^op) z (K^op)
       (parallel_cofork_legs h) (parallel_cofork_legs_coherence h Hh)).

(*
 An elementary coequalizer of the pair is a colimiting cocone over K. 

 --------
 该对的一个初等共同等化器是 K 上的一个余极限余锥。
*)

Definition parallel_coequalizer_colimit {q : C} {e : K ParY ~> q}
  (E : IsCoequalizer par1 par2 q e) :
  IsColimitCocone (parallel_cofork_cocone e (cofork E)).
Proof.
  intro M.
  assert (HX1 : cocone_inj M ParY ∘ par1 ≈ cocone_inj M ParX).
  { exact (cocone_inj_coherence M
             ((true; ParOne) : ParX ~{Parallel}~> ParY)). }
  assert (HX2 : cocone_inj M ParY ∘ par2 ≈ cocone_inj M ParX).
  { exact (cocone_inj_coherence M
             ((false; ParTwo) : ParX ~{Parallel}~> ParY)). }
  assert (Hfg : cocone_inj M ParY ∘ par1 ≈ cocone_inj M ParY ∘ par2).
  { rewrite HX1, HX2.
    reflexivity. }
  unshelve eapply Build_Unique.
  - exact (unique_obj (coeq_desc E (cocone_inj M ParY) Hfg)).
  - intro p; destruct p.
    + (* the injection over ParX is e ∘ par1 / 在 ParX 上的注入是 e ∘ par1 *)
      change (unique_obj (coeq_desc E (cocone_inj M ParY) Hfg) ∘ (e ∘ par1)
                ≈ cocone_inj M ParX).
      rewrite comp_assoc.
      rewrite (unique_property (coeq_desc E (cocone_inj M ParY) Hfg)).
      exact HX1.
    + exact (unique_property (coeq_desc E (cocone_inj M ParY) Hfg)).
  - intros v Hv.
    apply (uniqueness (coeq_desc E (cocone_inj M ParY) Hfg)).
    exact (Hv ParY).
Defined.

(*
 ANY colimiting cocone over K is an elementary coequalizer of the pair
 at its apex, coequalized by its injection over ParY. 

 --------
 K 上的任何共极限余锥都是其顶点处的一对元共轭器，由其在 ParY 上的注射进行共轭化。
*)

Definition parallel_colimit_coequalizer (N : Cocone K)
  (HN : IsColimitCocone N) :
  IsCoequalizer par1 par2 vertex_obj[N] (cocone_inj N ParY).
Proof.
  unshelve econstructor.
  - (* both composites are the injection over ParX / 两个复合材料都是在 ParX 上的注入 *)
    transitivity (cocone_inj N ParX).
    + exact (cocone_inj_coherence N
               ((true; ParOne) : ParX ~{Parallel}~> ParY)).
    + symmetry.
      exact (cocone_inj_coherence N
               ((false; ParTwo) : ParX ~{Parallel}~> ParY)).
  - intros z h Hh.
    pose (U := colimitcocone_ump HN (parallel_cofork_cocone h Hh)).
    unshelve eapply Build_Unique.
    + exact (unique_obj U).
    + exact (unique_property U ParY).
    + intros v Hv.
      apply (uniqueness U).
      intro p; destruct p.
      * (* the ParX leg follows from the ParY leg by coherence / ParX 段是由 ParY 段通过连贯性得出的 *)
        change (v ∘ cocone_inj N ParX ≈ h ∘ par1).
        rewrite <- (cocone_inj_coherence N
                      ((true; ParOne) : ParX ~{Parallel}~> ParY)).
        rewrite comp_assoc, Hv.
        reflexivity.
      * exact Hv.
Defined.

(*
 The converse of the last for a GIVEN cocone N over K (#481): when N's
 injection over ParY is an elementary coequalizer of the pair, N is
 colimiting.  It is the cocone [parallel_cofork_cocone] of that
 injection up to a cone isomorphism whose apex map is the identity:
 over [ParY] the two injections are one arrow, and over [ParX] N's is
 [cocone_inj N ParY ∘ par1] by coherence.  At [K := T ◯ APair f g] and
 the image cocone of a cofork this is the statement of
 Structure/Coequalizer/Absolute.v's [image_coequalizer_colimit], which
 keeps its own proof. 

 --------
 给定一个在 K 上的余锥 N（#481）的相反情况：当 N 在 ParY 上的注入是该对的初等余等化器时，N 是余极限的。它是该注入的余锥 [parallel_cofork_cocone] 到一个锥同构，其顶点映射是恒等的：在 [ParY] 上，两个注入合为一箭；在 [ParX] 上，N 的注入由相合性是 [cocone_inj N ParY ∘ par1]。在 [K := T ◯ APair f g] 上以及一个余叉的像余锥，这是 Structure/Coequalizer/Absolute.v 中 [image_coequalizer_colimit] 的陈述，它保持自己的证明。
*)

Definition parallel_cocone_coequalizer_colimit (N : Cocone K)
  (E : IsCoequalizer par1 par2 vertex_obj[N] (cocone_inj N ParY)) :
  IsColimitCocone N.
Proof.
  refine (limitcone_transport _ (parallel_coequalizer_colimit E)).
  exists (@iso_id (C^op) vertex_obj[N]).
  intro p; destruct p.
  - (* over ParX, by coherence / 通过一致性，超过 ParX *)
    change (id ∘ cocone_inj N ParX ≈ cocone_inj N ParY ∘ par1).
    rewrite id_left.
    symmetry.
    exact (cocone_inj_coherence N
             ((true; ParOne) : ParX ~{Parallel}~> ParY)).
  - (* over ParY, one arrow / 超过 ParY，一箭 *)
    change (id ∘ cocone_inj N ParY ≈ cocone_inj N ParY).
    apply id_left.
Defined.

End ParallelDiagram.

(*
 The converse Adjunction/Diagonal/Finite.v records as absent for its
 coequalizer row: chosen elementary coequalizers give every diagram of
 parallel-pair shape a colimit.  Its type is that file's
 [HasColimitsOfShape Parallel C] by δ (Adjunction/Diagonal/Limit.v),
 spelled out here so that this file need not require that module
 (accepted at the named type in Test/ProbeAbsolute477.v). 

 --------
 对于它的余等化行，逆伴随/对角线/有限.v 记录为缺失：选定的初等余等化给每个平行对形状的图一个余极限。它的类型是该文件的 [HasColimitsOfShape Parallel C]，由 δ (Adjunction/Diagonal/Limit.v) 定义，在这里详细说明，以便此文件不需要引用该模块（在 Test/ProbeAbsolute477.v 中以命名类型被接受）。
*)

Definition HasCoequalizers_HasColimitsOfShape {C : Category}
  (HC : HasCoequalizers C) : ∀ F : Parallel ⟶ C, Colimit F :=
  fun F =>
    let P := coeq (fmap[F] ((true; ParOne) : ParX ~{Parallel}~> ParY))
                  (fmap[F] ((false; ParTwo) : ParX ~{Parallel}~> ParY)) in
    {| limit_cone := parallel_cofork_cocone F (`1 (`2 P)) (cofork (`2 (`2 P)));
       ump_limits := parallel_coequalizer_colimit F (`2 (`2 P)) |}.
