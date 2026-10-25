Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.One.

Set Universe Polymorphism.

Generalizable All Variables.

(*
   * * Creation of limits in a comma category [=(d) ↓ U] 

   --------
   * * 在逗号范畴 [=(d) ↓ U] 中创建极限
*)

(*
 nLab: https://ncatlab.org/nlab/show/comma+category#limits_and_colimits
 nLab: https://ncatlab.org/nlab/show/created+limit

 Fix a functor [U : C ⟶ D] and an object [d : D].  The comma category
 [=(d) ↓ U] (built with the constant functor [=(d) : 1 ⟶ D] of
 [Functor/Diagonal.v] on the left) has as objects the pairs [(c, h)] of an
 object [c : C] and a morphism [h : d ~> U c], encoded as the dependent pair
 [(( _ , c ); h)] with the first component the point of the terminal category
 [1]; and as morphisms [(c, h) ~> (c', h')] the [g : c ~> c'] with the
 commuting triangle [h' ≈ U g ∘ h] (the constant functor sends every arrow to
 [id[d]], so the general comma square [h' ∘ =(d) f ≈ U g ∘ h] collapses to
 that triangle — this is [comma_square] below).

 Standard fact: if [C] has and [U] preserves [J]-limits, then [=(d) ↓ U] has
 [J]-limits, and the projection [comma_proj2 : =(d) ↓ U ⟶ C] creates them.
 Concretely, given a diagram [K : J ⟶ (=(d) ↓ U)]:

 - its [C]-projection [G := comma_proj2 ◯ K] has a limit [L] in [C];
 - the family [h_j := `2 (K j) : d ~> U (G j)] is a cone over [U ◯ G] with
 apex [d] (the coherence is exactly the collapsed comma square of [K f]);
 - preservation makes the image cone [(U L, fmap[U] π_•)] a limit of
 [U ◯ G], so that cone mediates the [(d, h_•)] cone by a unique
 [φ : d ~> U L];
 - the pair [(L, φ)] with the projected legs [(c := π_j)] is the limit of
 [K] in [=(d) ↓ U]; its universal property is the [C]-universal property
 of [L] on the base component together with the mediating uniqueness of
 the image cone on the [d]-component.

 STATUS / hypothesis form.  The mathematically correct meaning of "U
 preserves the limit of G" is that U carries the *limit cone* to a *limit
 cone* — equivalently, the image cone [(U L, fmap[U] π_•)] is universal.  This
 is precisely what [Adjunction/Continuity.v] establishes for right adjoints:
 its [rapl_is_alimit] is built from [rapl_acone], whose legs
 [rapl_leg x = fmap[U] (limit_leg (limit_is_alimit L) x)] are the image legs.

 The bare class [PreservesLimit] of [Structure/Limit/Preservation.v] records
 only that the *apex object* [U L] carries *some* limit structure of [U ◯ G]
 ([IsALimit (U ◯ G) (U L)]); the legs of that structure are left
 unconstrained and need not be the image legs [fmap[U] π_•].  Two distinct
 cone structures on the same apex can differ by precomposition with a
 non-invertible endomorphism, only one of them being a limit, so apex-only
 preservation does not by itself make the image cone universal — and it is the
 image cone whose universal property is needed to lift both the existence of
 [φ] and the uniqueness of the comma mediator.  We therefore take as the
 preservation hypothesis the honest, cone-level statement [PreservesImageLimit]
 below (the image cone is universal), which is exactly the universal property
 [rapl_ump] delivers.  This is a strengthening to the correct notion of
 preservation, never a weakening of the conclusion [Comma_Complete]. 

 --------
 nLab:  https://ncatlab.org/nlab/show/comma+category#limits_and_colimits 
 nLab:  https://ncatlab.org/nlab/show/created+limit 

 固定函子  [U : C ⟶ D]  和对象  [d : D] 。逗号范畴 [=(d) ↓ U] （用左侧的常值函子 [=(d) : 1 ⟶ D] 构造）其对象为对 [(c, h)] ，由对象 [c : C] 和态射 [h : d ~> U c] 组成，以依赖对 [(( _ , c ); h)] 编码，其第一分量为终对象范畴 [1] 的点；其态射 [(c, h) ~> (c', h')] 为 [g : c ~> c'] ，满足交换三角形 [h' ≈ U g ∘ h] （常值函子将每个箭头映射为 [id[d]），因此一般的逗号方形 [h' ∘ =(d) f ≈ U g ∘ h] 简化为该三角形 — 下面为 [comma_square] 。标准事实：如果 [C] 有并且 [U] 保持 [J]-极限，那么 [=(d) ↓ U] 具有 [J]-极限，并且投影 [comma_proj2 : =(d) ↓ U ⟶ C] 产生它们。具体来说，给定一个图 [K : J ⟶ (=(d) ↓ U)] ：- 它的 [C]-投影 [G := comma_proj2 ◯ K] 在 [C] 中有极限 [L]；
 - 族 [h_j := `2 (K j) : d ~> U (G j)] 是 [U ◯ G] 上的一个锥，顶点为 [d]（相干性正好是 [K f] 的塌陷逗号平方）；
 - 保留性使得像锥 [(U L, fmap[U] π_•)] 成为 [U ◯ G] 的极限，因此该锥通过唯一的 [φ : d ~> U L] 调节 [(d, h_•)] 锥；
 - 对 ([(L, φ)]) 与投影腿 [(c := π_j)] 的对是 [=(d) ↓ U] 中 [K] 的极限；它的普遍性质是基组件上 [L] 的 [C]-普遍性质，以及 [d] 组件上像锥的调节唯一性。状态 / 假设形式。“U 保持 G 的极限”的数学上正确含义是 U 将 *极限锥* 映射到 *极限锥* — 等价地，像锥 [(U L, fmap[U] π_•)] 是普遍的。这正是 [Adjunction/Continuity.v] 为右伴随建立的：它的 [rapl_is_alimit] 构建自 [rapl_acone]，其边 [rapl_leg x = fmap[U]（limit_leg (limit_is_alimit L) x)] 是像边。[Structure/Limit/Preservation.v] 的裸类 [PreservesLimit] 仅记录了 *顶点对象* [U L] 拥有 [U ◯ G] 的 *某种*极限结构 ([IsALimit (U ◯ G) (U L)])；该结构的腿没有约束，也不必是像腿 [fmap[U] π_•]。同一顶点上的两个不同锥体结构可能通过与一个不可逆的自同态的前合成而不同，其中只有一个是极限，因此仅仅保存顶点本身并不能使像锥体具有普遍性 —— 真正需要普遍性的正是像锥体，以提升 [φ] 的存在性和逗号介值的唯一性。因此，我们采取作为保留假设的是真实的、锥体级别的陈述 [PreservesImageLimit]（像锥体是普遍的），这正是 [rapl_ump] 所提供的普遍性质。这是对正确保存概念的加强，绝不是对结论 [Comma_Complete] 的削弱。
*)

Section CommaLimit.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.

(** ** The collapsed comma square / ** 倒塌的逗号广场 *)

(*
 Every morphism of [=(d) ↓ U] has domain-side leg [=(d) f = id[d]], so its
 commuting square is just [`2 Y ≈ fmap[U] (snd `1 m) ∘ `2 X]. 

 --------
 [=(d) ↓ U] 的每个态射在域侧都有腿 [=(d) f = id[d]，所以它的交换平方只是 [`2 Y ≈ fmap[U]（snd `1 m) ∘ ` 2 X]）。
*)
Lemma comma_square {X Y : =(d) ↓ U} (m : X ~{=(d) ↓ U}~> Y) :
  `2 Y ≈ fmap[U] (snd (`1 m)) ∘ `2 X.
Proof.
  transitivity (`2 Y ∘ id[d]).
  - rewrite id_right; reflexivity.
  - exact (`2 m).
Qed.

(* * ** The image cone and the honest preservation hypothesis / * ** 图像锥与诚实保留假说 *)

(*
 The legs of the image cone: [fmap[U]] applied to the legs of a [C]-limit L
 of G.  The codomain [U (G x)] is convertible with [(U ◯ G) x]. 

 --------
 图像锥的腿：[fmap[U]] 适用于 G 的 [C] -极限 L 的腿。陪域 [U (G x)] 可与 [(U ◯ G) x] 互换。
*)
Definition image_leg {J : Category} {G : J ⟶ C} (L : Limit G) (x : J) :
  U L ~{D}~> (U ◯ G) x :=
  fmap[U] (limit_leg (limit_is_alimit L) x).

Lemma image_coherence {J : Category} {G : J ⟶ C} (L : Limit G)
  {x y : J} (f : x ~{J}~> y) :
  fmap[U] (fmap[G] f) ∘ image_leg L x ≈ image_leg L y.
Proof.
  unfold image_leg.
  rewrite <- fmap_comp.
  now rewrite (limit_leg_coherence (limit_is_alimit L) f).
Qed.

Definition image_acone {J : Category} {G : J ⟶ C} (L : Limit G) :
  ACone (U L) (U ◯ G) :=
  @Build_ACone J D (U L) (U ◯ G) (image_leg L) (@image_coherence J G L).

(*
 U preserves limits, cone-faithfully: for every diagram the image cone above
 is a limit of [U ◯ G].  (See the STATUS header for why this — rather than the
 apex-only [PreservesAllLimits] — is the operative hypothesis.) 

 --------
 U 保持极限，保持圆锥的忠实性：对于每个图，上方的图像圆锥是 [U ◯ G] 的一个极限。（参见 STATUS 头部，以了解为什么这是操作性假设——而不是仅仅顶点的 [PreservesAllLimits]。）
*)
Definition PreservesImageLimit : Type :=
  ∀ (J : Category) (G : J ⟶ C) (L : Limit G) (N : Cone (U ◯ G)),
    ∃! φ : vertex_obj[N] ~{D}~> U L,
      ∀ x : J, image_leg L x ∘ φ ≈ cone_leg N x.

(* Packaged apex-pinned limit whose legs are the image legs. / 封装的顶点固定限，其引脚是图像引脚。 *)
Definition image_is_alimit (HU : PreservesImageLimit)
  {J : Category} {G : J ⟶ C} (L : Limit G) : IsALimit (U ◯ G) (U L) :=
  @Build_IsALimit J D (U ◯ G) (U L) (image_acone L) (HU J G L).

(* * ** Creation of the limit of one diagram / * ** 创建一个图表的极限 *)

Section Create.

Context (HU : PreservesImageLimit).
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).

(* The base diagram in C. / C中的基础图 *)
Definition Gdiag : J ⟶ C := comma_proj2 ◯ K.

(*
 GENERALIZED: an arbitrary limit of the base diagram, in place of a
 [Complete C] hypothesis. 

 --------
 广义：基图的一个任意限制，代替 [Complete C] 假设。
*)
Context (Ldiag : Limit Gdiag).

(*
 The cone over [U ◯ Gdiag] with apex [d] built from the [d]-legs of K. 

 --------
 由 K 的 [d] 边构建的 [U ◯ Gdiag] 上的圆锥，其顶点为 [d]。
*)
Definition base_leg (j : J) : d ~{D}~> (U ◯ Gdiag) j := `2 (K j).

Lemma base_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[U] (fmap[Gdiag] f) ∘ base_leg x ≈ base_leg y.
Proof.
  unfold base_leg.
  symmetry.
  transitivity (`2 (K y) ∘ id[d]).
  - rewrite id_right; reflexivity.
  - exact (`2 (fmap[K] f)).
Qed.

Definition base_cone : Cone (U ◯ Gdiag) :=
  @Build_Cone J D (U ◯ Gdiag) d
    (@Build_ACone J D d (U ◯ Gdiag) base_leg (@base_coherence)).

(* The mediating morphism into the preserved (image) limit. / 进入保留（像）极限的中介态射。 *)
Definition phi : d ~{D}~> U Ldiag :=
  limit_med (image_is_alimit HU Ldiag) base_cone.

Lemma phi_commutes (j : J) :
  fmap[U] (limit_leg (limit_is_alimit Ldiag) j) ∘ phi ≈ `2 (K j).
Proof. exact (limit_med_commutes (image_is_alimit HU Ldiag) base_cone j). Qed.

(* The apex object of the comma limit: [(Ldiag, φ)]. / 逗号限制的顶点对象：[(Ldiag, φ)]。 *)
Definition apex_obj : (=(d) ↓ U) := ((ttt, vertex_obj[Ldiag]); phi).

(*
 The legs of the comma limit cone: the projected [C]-legs [π_j], upgraded to
 comma morphisms by the triangle [`2 (K j) ≈ fmap[U] π_j ∘ φ]. 

 --------
 逗号限制锥的腿：投影的 [C] -腿 [π_j]，通过三角形 [`2 (K j) ≈ fmap[U] π_j ∘ φ 升级为逗号态射。
*)
Definition apex_leg (j : J) : apex_obj ~{=(d) ↓ U}~> K j.
Proof.
  unshelve refine ((ttt, limit_leg (limit_is_alimit Ldiag) j); _).
  change (`2 (K j) ∘ id[d]
          ≈ fmap[U] (limit_leg (limit_is_alimit Ldiag) j) ∘ phi).
  rewrite id_right.
  symmetry.
  exact (phi_commutes j).
Defined.

Lemma apex_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ apex_leg x ≈ apex_leg y.
Proof.
  split.
  - reflexivity.
  - exact (limit_leg_coherence (limit_is_alimit Ldiag) f).
Qed.

Definition apex_cone : Cone K :=
  @Build_Cone J (=(d) ↓ U) K apex_obj
    (@Build_ACone J (=(d) ↓ U) apex_obj K apex_leg (@apex_coherence)).

(** *** Universal property / *** 通用属性 *)

(*
 From a competing comma cone N, its [C]-projection is a cone over Gdiag. 

 --------
 从一个竞争的逗号圆锥 N，其 [C] 投影是 Gdiag 上的一个圆锥。
*)
Definition qleg (N : Cone K) (j : J) :
  snd (`1 vertex_obj[N]) ~{C}~> Gdiag j :=
  snd (`1 (cone_leg N j)).

Lemma qcoherence (N : Cone K) {x y : J} (f : x ~{J}~> y) :
  fmap[Gdiag] f ∘ qleg N x ≈ qleg N y.
Proof. exact (snd (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f)). Qed.

Definition qcone (N : Cone K) : Cone Gdiag :=
  @Build_Cone J C Gdiag (snd (`1 vertex_obj[N]))
    (@Build_ACone J C (snd (`1 vertex_obj[N])) Gdiag (qleg N) (@qcoherence N)).

(* The mediating morphism in C. / C 中的中介态射。 *)
Definition wmed (N : Cone K) : snd (`1 vertex_obj[N]) ~{C}~> Ldiag :=
  limit_med (limit_is_alimit Ldiag) (qcone N).

(*
 The comma mediator: [wmed N] upgraded to a comma morphism. 

 --------
 逗号调解器：[wmed N] 升级为逗号同态。
*)
Definition umed (N : Cone K) : vertex_obj[N] ~{=(d) ↓ U}~> apex_obj.
Proof.
  unshelve refine ((ttt, wmed N); _).
  change (phi ∘ id[d] ≈ fmap[U] (wmed N) ∘ `2 vertex_obj[N]).
  rewrite id_right.
  apply (limit_med_eq (image_is_alimit HU Ldiag) base_cone).
  - exact (limit_med_commutes (image_is_alimit HU Ldiag) base_cone).
  - intro j.
    change (fmap[U] (limit_leg (limit_is_alimit Ldiag) j)
              ∘ (fmap[U] (wmed N) ∘ `2 vertex_obj[N]) ≈ `2 (K j)).
    unfold wmed.
    rewrite comp_assoc, <- fmap_comp.
    rewrite (limit_med_commutes (limit_is_alimit Ldiag) (qcone N) j).
    symmetry.
    exact (comma_square (cone_leg N j)).
Defined.

Definition comma_ump (N : Cone K) :
  ∃! u : vertex_obj[N] ~{=(d) ↓ U}~> apex_obj,
    ∀ j : J, apex_leg j ∘ u ≈ cone_leg N j.
Proof.
  unshelve refine {| unique_obj := umed N |}.
  - intro j; split.
    + now destruct (fst (`1 (cone_leg N j))).
    + exact (limit_med_commutes (limit_is_alimit Ldiag) (qcone N) j).
  - intros v Hv; split.
    + now destruct (fst (`1 v)).
    + unfold wmed.
      apply (limit_med_unique (limit_is_alimit Ldiag) (qcone N)).
      intro j.
      exact (snd (Hv j)).
Defined.

Definition comma_limit : Limit K :=
  @Build_Limit J (=(d) ↓ U) K apex_cone comma_ump.

End Create.

(* * ** Completeness of the comma category / * ** 逗号类别的完整性 *)

Definition Comma_Complete
  (HU : PreservesImageLimit) (HC : @Complete C) :
  @Complete (=(d) ↓ U) :=
  fun J K => comma_limit HU K (HC J (Gdiag K)).

End CommaLimit.

(*
   * ** The preservation hypothesis is inhabited by right adjoints 

   --------
   * ** 保存假说由右伴随所支配
*)

Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Continuity.

(*
 Every right adjoint satisfies [PreservesImageLimit]: for an adjunction
 [A : F ⊣ U], RAPL exhibits the image cone over [U L] as universal, and its
 legs [rapl_leg x = fmap[U] (limit_leg (limit_is_alimit L) x)] are exactly the
 image legs [image_leg L x], so [rapl_ump] has, up to conversion, the type
 demanded by [PreservesImageLimit].  This ties the honest cone-level
 hypothesis to the preservation vocabulary of [Structure/Limit/Preservation.v]
 and [Adjunction/Continuity.v]. 

 --------
 每一个右伴随都满足 [PreservesImageLimit]：对于一个伴随 [A : F ⊣ U]，RAPL 将 [U L] 上的像锥展示为普遍的，而它的支腿 [rapl_leg x = fmap[U]（limit_leg (limit_is_alimit L) x）正好是像支腿 [image_leg L x]，所以 [rapl_ump] 在转换后具有 [PreservesImageLimit] 所要求的类型。这将真实的锥级假设与 [Structure/Limit/Preservation.v] 和 [Adjunction/Continuity.v] 的保持词汇联系起来。
*)
Definition right_adjoint_PreservesImageLimit
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) :
  @PreservesImageLimit C D U.
Proof. intros J G L N. exact (rapl_ump A G L N). Defined.

(*
 Capstone: the comma category [=(d) ↓ U] over a right adjoint [U] into a
 complete category [C] is complete. 

 --------
 结题：在一个右伴随  [U] 下，逗号范畴  [=(d) ↓ U] 到一个完备范畴  [C] 是完备的。
*)
Definition Comma_Complete_right_adjoint
  {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U) (d : D)
  (HC : @Complete C) : @Complete (=(d) ↓ U) :=
  Comma_Complete (right_adjoint_PreservesImageLimit A) HC.
