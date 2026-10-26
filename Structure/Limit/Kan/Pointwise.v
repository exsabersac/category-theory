Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.One.

Generalizable All Variables.

(*
   * * The pointwise (co)limit formula for Kan extensions

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §X.3
   “The Kan Extension” (book pp. 237-240): Theorem 1 [maclane:X.3:thm1] —
   the right Kan extension computed pointwise as a limit over the comma
   category — and the dual pointwise colimit formula for the left
   extension [maclane:X.3:def2].
   Riehl, “Category Theory in Context”, §6.2, Theorem 6.2.1 with displays
   (6.2.2)/(6.2.3) [riehl:6.2:thm1]: the same theorem in both
   handednesses, with the unit/counit read off the (co)limit-cone leg at
   the identity and the action on morphisms induced by reindexing.
   nLab: https://ncatlab.org/nlab/show/Kan+extension

   Theory/Kan/Extension.v carries the abstract theory — the global
   extensions as adjoints of the restriction functor [Induced], and the
   local universal properties [LocalRightKan]/[LocalLeftKan] — and its
   header had flagged the pointwise formulas (comma-category and
   coend/end alike) as a bridge not yet formalized.  This file builds
   the COMMA-CATEGORY half of that bridge; the Kelly coend/end route
   through Structure/Coend.v remains open.  The construction is in the
   LOCAL form: the pointwise formula needs exactly one (co)limit per
   object of the target, and Mac Lane's global packaging (Theorem 1's
   “A small, C complete” reading, assembling every local extension into
   the adjoint [RightKan]) is deliberately not attempted here:

   - given F : A ⟶ B, X : A ⟶ C, and a limit of
   X ◯ comma_proj2 : (=(b) ↓ F) ⟶ C for every b : B, the assignment
   R b := Lim (X ◯ comma_proj2) extends to a functor B ⟶ C whose
   counit component at a is the limit-cone leg at (a, id[F a]), and
   ⟨R, ε⟩ inhabits [LocalRightKan F X]  ([Pointwise_LocalRightKan]);

   - dually, colimits of X ◯ comma_proj1 : (F ↓ =(b)) ⟶ C for every b
   assemble into L b := Colim (X ◯ comma_proj1) with unit component
   the injection at (a, id[F a]), and ⟨L, η⟩ inhabits
   [LocalLeftKan F X]  ([Pointwise_LocalLeftKan]).

   THE ACTION ON MORPHISMS is induced by reindexing, exactly as in
   Riehl's proof: a morphism g : b ~> b' of B precomposes the comma
   component, giving [ran_reindex g : (=(b') ↓ F) ⟶ (=(b) ↓ F)] (note
   the flip: limits are contravariant in the shape restriction, so R
   comes out covariant), and dually [lan_reindex g] postcomposes.  The
   reindexing functors here are deliberately minimal — just what
   functoriality needs; the standing issue #1021 will develop the comma
   reindexing calculus in its own right, and nothing here blocks on it.

   TWO WORKHORSES keep every proof short.  The legs of a limit cone are
   JOINTLY MONIC ([ran_jointly_monic]) — two morphisms into the limit
   agreeing under every leg are equal, by factoring both through the
   probe cone they induce — and legs TRANSPORT along the comma morphism
   (id, id) between objects whose components are ≈-equal
   ([ran_leg_transport]): the comma square for (id, id) demands only
   f' ≈ F id ∘ f, so ≈-equal components are connected by a genuine comma
   morphism even though they are distinct objects, and cone coherence
   along it moves a leg from one to the other.  Every functor law and
   every naturality below is “compose with the legs and compute” through
   these two.  The colimit side has the dual pair
   ([lan_jointly_epic], [lan_inj_transport]), phrased through the
   covariant cocone accessors of Structure/Limit/Preservation.v
   ([cocone_inj], [colimitcocone_ump]) so that no TACTIC PROOF below
   manipulates an opposite category.  (The three cocone-building
   definitions on the left side do name (F ↓ =(b))^op — a [Cocone] IS a
   cone over the opposite diagram, and the tree has no covariant cocone
   constructor; the op stays confined to those [Build_Cone] wrappers.)

   WHAT “the counit is the leg at the identity” MEANS FORMALLY: the
   [ran_transform] of [Pointwise_LocalRightKan] is BY CONSTRUCTION the
   family of legs at (a, id[F a]) — recorded as definitional equalities
   in the acceptance tests — and dually for [lan_transform].  This is
   the issue's third work item: the abstract counit/unit of the packaged
   local extension agree with the concrete (co)limit data on the nose. 

   --------
   * * Kan 扩张的逐点 (co)极限公式

   Mac Lane，《面向工作数学家的范畴论》，第二版，第 X.3 节
   《Kan 扩张》（书页 237-240）：定理 1  [maclane:X.3:thm1] — 通过逗号范畴作为极限逐点计算的右 Kan 扩张 — 以及左扩张的对偶逐点余极限公式 [maclane:X.3:def2]。
   Riehl，《上下文中的范畴论》，§6.2，定理 6.2.1，带显示 (6.2.2)/(6.2.3)  [riehl:6.2:thm1]：同一条定理在左右两种情况下，单位/余单位通过在恒等映射处 (co)极限锥的支腿读取，并且对态射的作用由重索引诱导。
   nLab： https://ncatlab.org/nlab/show/Kan+extensionTheory/Kan/Extension.v 包含抽象理论——作为限制函子 [Induced] 的伴随的全局扩张，以及局部的普遍性质 [LocalRightKan] / [LocalLeftKan]——其头文件已经将逐点公式（逗号范畴和余端/端的类似公式）标记为尚未形式化的桥梁。该文件构建了该桥梁的 COMMA-CATEGORY 部分；通过 Structure/Coend.v 的 Kelly 余端/端路线仍然开放。该构造采用局部形式：逐点公式对于目标对象恰好需要一个（余）极限，而 Mac Lane 的全局打包（定理 1 中的“一个小型、C 完备”的解释，将每个局部扩张组装成伴随 [RightKan]）在此处故意未尝试:- 给定 F : A ⟶ B, X : A ⟶ C，并且对于每个 b : B，有 X ◯ comma_proj2 : (=(b) ↓ F) ⟶ C 的极限，则赋值  
   R b := Lim (X ◯ comma_proj2) 扩展为一个函子 B ⟶ C，其余单位分量在 a 处是极限锥在 (a, id [F a]) 处的分支，且  
   ⟨R, ε⟩ 属于 [LocalRightKan F X] ([Pointwise_LocalRightKan])；  

   - 对偶地，对于每个 b 的 X ◯ comma_proj1 : (F ↓ =(b)) ⟶ C 的余极限汇聚成  
   L b := Colim (X ◯ comma_proj1)，其单位分量为 (a, id [F a]) 处的注入，且 ⟨L, η⟩ 属于 [LocalLeftKan F X] ([Pointwise_LocalLeftKan])。对态射的作用是通过重索引引入的，正如 Riehl 的证明中所示：一个 B 中的态射 g : b ~> b' 先复合逗号分量，从而得到 [ran_reindex g : (=(b') ↓ F) ⟶ (=(b) ↓ F)]（注意翻转：极限在形状限制下是反变的，所以 R 变为协变），而对偶地 [lan_reindex g] 后复合。这里的重索引函子故意做得最小——仅满足函子性所需；现存问题 #1021 将会独立发展逗号重索引演算，这里没有任何内容会因此受阻。两个得力助手让每个证明保持简短。极限锥的支脚是联合单态的 ([ran_jointly_monic]) —— 两个指向极限的态射若在每个支脚下都相等，则它们相等，这是通过它们所诱导的探针锥因式分解得到的 —— 并且支脚沿着对象之间成分≈相等的逗号态射 (id, id) 传送 ([ran_leg_transport])：对于 (id, id) 的逗号方形只要求 f' ≈ F id ∘ f，因此≈相等的成分即使是不同的对象，也能由一个真实的逗号态射连接，并且沿其的锥协调性可将一个支脚从一个对象移动到另一个对象。下面的每一个函子定律和自然性都是“与支脚复合并计算”，通过这两个助手完成。余极限侧具有对偶对 ([lan_jointly_epic], [lan_inj_transport])，通过 Structure/Limit/Preservation.v 的协变余锥访问器表述 ([cocone_inj], [colimitcocone_ump])，因此下面没有任何 TACTIC PROOF 操作对偶范畴。（左侧的三个构造余锥的定义确实命名了 (F ↓ =(b))^op — 一个 [Cocone] 是对偶图上的锥，并且该树没有协变余锥构造器；op 保持局限于那些 [Build_Cone] 包装器。）“‘余单位是单位元处的边’正式意味着：[ran_transform] 的 [Pointwise_LocalRightKan] 是通过构造得到的 (a, id [F a]) 处的边的族——在验收测试中以定义性等式记录——[lan_transform] 也类似。 这是此问题的第三个工作项：打包的局部扩展的抽象余单位/单位与具体的 (协)极限数据完全一致。”
*)

#[local] Obligation Tactic := idtac.

(* * ** The right Kan extension as a pointwise limit / * ** 作为逐点极限的右Kan扩张 *)

Section PointwiseRan.

Context {A : Category}.
Context {B : Category}.
Context {F : A ⟶ B}.
Context {C : Category}.
Context (X : A ⟶ C).

(*
 The diagram whose limit computes the extension at b: the comma category
 (=(b) ↓ F) of pairs (a, f : b ~> F a), projected to A and followed by X.
 Mac Lane writes this composite T ∘ Q (§X.3, display before Theorem 1). 

 --------
 该图的极限用于计算 b 处的延拓：逗号范畴 (=(b) ↓ F) 的对 (a, f : b ~> F a)，投射到 A 后再跟随 X。Mac Lane 将此复合表示为 T ∘ Q（§X.3，定理 1 前的图示）。
*)
Definition ran_comma_diagram (b : B) : (=(b) ↓ F) ⟶ C :=
  X ◯ @comma_proj2 _ _ _ =(b) F.

(* The pointwise hypothesis: each comma diagram has a limit. / 逐点假设：每个逗号图都有一个极限。 *)
Context (lim : ∀ b : B, Limit (ran_comma_diagram b)).

Definition ran_obj (b : B) : C := vertex_obj[(@limit_cone _ _ _ (lim b))].

Definition ran_leg {b : B} (x : =(b) ↓ F) :
  ran_obj b ~{C}~> ran_comma_diagram b x :=
  @vertex_map _ _ _ _ (@coneFrom _ _ _ ((@limit_cone _ _ _ (lim b)))) x.

Lemma ran_leg_coherence {b : B} {x y : =(b) ↓ F} (f : x ~{=(b) ↓ F}~> y) :
  fmap[ran_comma_diagram b] f ∘ ran_leg x ≈ ran_leg y.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ ((@limit_cone _ _ _ (lim b)))) x y f).
Qed.

(*
 Legs transport along ≈-equality of the comma component: (id, id) is a
 comma morphism (a, f) ~> (a, f') whenever f ≈ f', and the diagram sends
 it to fmap[X] id ≈ id. 

 --------
 沿着逗号分量的≈-等价传送腿：(id, id) 是一个逗号态射 (a, f) ~> (a, f') 当且仅当 f ≈ f'，并且图将其发送到 fmap [X] id ≈ id。
*)
Lemma ran_leg_transport {b : B} (t : (1 ∏ A)%category) (f f' : b ~> F (snd t)) :
  f ≈ f' →
  ran_leg (existT _ t f) ≈ ran_leg (existT _ t f').
Proof.
  intro Hf.
  assert (sq : f' ∘ fmap[=(b)] (@id 1 (fst t)) ≈ fmap[F] (@id A (snd t)) ∘ f).
  { simpl.
    rewrite fmap_id, id_left, id_right.
    now symmetry. }
  rewrite <- (ran_leg_coherence
                ((((ttt, @id A (snd t)); sq))
                   : existT (fun p : (1 ∏ A)%category => b ~> F (snd p)) t f
                       ~{=(b) ↓ F}~> existT _ t f')).
  simpl.
  now rewrite fmap_id, id_left.
Qed.

(* Any family through the limit legs induces a probe cone, whence the legs are jointly monic. / 通过极限腿的任何族都会引起一个探针锥，因此这些腿是联合单射的。 *)
Program Definition ran_probe_cone {b : B} {c : C} (u : c ~> ran_obj b) :
  Cone (ran_comma_diagram b) :=
  @Build_Cone (=(b) ↓ F) C (ran_comma_diagram b) c
    (@Build_ACone (=(b) ↓ F) C c (ran_comma_diagram b)
       (fun x => ran_leg x ∘ u) _).
Next Obligation.
  intros b c u x y f; simpl.
  rewrite comp_assoc.
  now rewrite (ran_leg_coherence f).
Qed.

Lemma ran_jointly_monic {b : B} {c : C} (u v : c ~> ran_obj b) :
  (∀ x : =(b) ↓ F, ran_leg x ∘ u ≈ ran_leg x ∘ v) →
  u ≈ v.
Proof.
  intro H.
  destruct (@ump_limits _ _ _ (lim b) (ran_probe_cone u)) as [w Hw Huniq].
  transitivity w.
  - symmetry; apply Huniq; intro x; reflexivity.
  - apply Huniq; intro x; symmetry; apply H.
Qed.

(* * *** Reindexing, and the extension functor / * *** 重新索引，以及拓展函子 *)

(*
 g : b ~> b' precomposes the comma component: (a, f : b' ~> F a) becomes
 (a, f ∘ g : b ~> F a).  This is Riehl's reindexing functor, built here
 in the minimal constant-domain case this file needs (issue #1021 owns
 the general calculus). 

 --------
 g : b ~> b' 预组合逗号分量：(a, f : b' ~> F a) 变为 (a, f ∘ g : b ~> F a)。这是 Riehl 的重索引函子，这里在本文件所需的最小常量域情况下构建（一般演算由 issue #1021 负责）。
*)
Program Definition ran_reindex {b b' : B} (g : b ~> b') :
  (=(b') ↓ F) ⟶ (=(b) ↓ F) := {|
  fobj := fun x => existT _ (`1 x) (`2 x ∘ g);
  fmap := fun x y f => (`1 f; _)
|}.
Next Obligation.
  intros b b' g x y f.
  destruct f as [[u v] sq]; simpl in *.
  rewrite id_right in sq.
  rewrite id_right.
  rewrite comp_assoc.
  now rewrite <- sq.
Qed.
Next Obligation.
  intros b b' g x y f f' [e1 e2]; simpl.
  split; assumption.
Qed.
Next Obligation.
  intros b b' g x; simpl.
  split; reflexivity.
Qed.
Next Obligation.
  intros b b' g x y z f f'; simpl.
  split; reflexivity.
Qed.

(*
 The restricted cone: the b-limit's legs at reindexed objects form a
 cone over the b'-diagram (the two composites agree definitionally). 

 --------
 受限圆锥：在重新索引的对象上，b-极限的各条边形成一个圆锥，位于b'-图上（两个复合在定义上是一致的）。
*)
Program Definition ran_restrict_cone {b b' : B} (g : b ~> b') :
  Cone (ran_comma_diagram b') :=
  @Build_Cone (=(b') ↓ F) C (ran_comma_diagram b') (ran_obj b)
    (@Build_ACone (=(b') ↓ F) C (ran_obj b) (ran_comma_diagram b')
       (fun x => ran_leg (ran_reindex g x)) _).
Next Obligation.
  intros b b' g x y f; simpl.
  exact (ran_leg_coherence (fmap[ran_reindex g] f)).
Qed.

Definition ran_fmap {b b' : B} (g : b ~> b') : ran_obj b ~> ran_obj b' :=
  unique_obj (@ump_limits _ _ _ (lim b') (ran_restrict_cone g)).

Lemma ran_fmap_leg {b b' : B} (g : b ~> b') (x : =(b') ↓ F) :
  ran_leg x ∘ ran_fmap g ≈ ran_leg (ran_reindex g x).
Proof.
  exact (unique_property (@ump_limits _ _ _ (lim b') (ran_restrict_cone g)) x).
Qed.

Program Definition Pointwise_Ran : B ⟶ C := {|
  fobj := ran_obj;
  fmap := fun b b' g => ran_fmap g
|}.
Next Obligation.
  intros b b' g g' Hg.
  apply ran_jointly_monic; intro x.
  etransitivity; [ exact (ran_fmap_leg g x) |].
  etransitivity; [| symmetry; exact (ran_fmap_leg g' x) ].
  destruct x as [t f]; simpl.
  apply ran_leg_transport.
  now rewrite Hg.
Qed.
Next Obligation.
  intro b.
  apply ran_jointly_monic; intro x.
  etransitivity; [ exact (ran_fmap_leg id x) |].
  etransitivity; [| symmetry; apply id_right ].
  destruct x as [t f]; simpl.
  apply ran_leg_transport.
  apply id_right.
Qed.
Next Obligation.
  intros b b' b'' g' g.
  apply ran_jointly_monic; intro x.
  etransitivity; [ exact (ran_fmap_leg (g' ∘ g) x) |].
  symmetry.
  etransitivity; [ apply comp_assoc |].
  etransitivity.
  { apply compose_respects; [ exact (ran_fmap_leg g' x) | reflexivity ]. }
  etransitivity; [ exact (ran_fmap_leg g (ran_reindex g' x)) |].
  destruct x as [t f]; simpl.
  apply ran_leg_transport.
  symmetry; apply comp_assoc.
Qed.

(* * *** The counit, and the local universal property / * *** 余单位，以及局部泛性质 *)

(* The identity object (a, id[F a]) of the comma category at F a. / 在 F a 的逗号范畴中的恒等对象 (a, id [F a])。 *)
Definition ran_id_obj (a : A) : =(F a) ↓ F :=
  existT (fun p : 1 ∏ A => F a ~> F (snd p)) (ttt, a) id.

(*
 The counit component at a is the limit-cone leg at the identity —
 Mac Lane's ε_a = λ_{1_{F a}}, Riehl's display (6.2.3). 

 --------
 在 a 处的余单位组件是单位处极限锥的腿——Mac Lane 的 ε_a = λ_{1_{F a}}, Riehl 的显示 (6.2.3)。
*)
Definition ran_counit_component (a : A) :
  Pointwise_Ran (F a) ~> X a := ran_leg (ran_id_obj a).

Program Definition ran_counit : Pointwise_Ran ◯ F ⟹ X :=
  Build_Transform' (F := Pointwise_Ran ◯ F) (G := X)
    ran_counit_component _.
Next Obligation.
  intros a a' v; simpl.
  unfold ran_counit_component.
  (*
 left side: coherence along the comma morphism (ttt, v) from (a, id)
 to (a', F v) in (=(F a) ↓ F) 

 --------
 左侧：沿着从 (a, id) 到 (a', F v) 在 (=(F a) ↓ F) 中的逗号态射 (ttt, v) 的相干性
*)
  assert (sq : fmap[F] v ∘ fmap[=(F a)] (@id 1 ttt)
                 ≈ fmap[F] v ∘ @id B (F a)).
  { simpl; reflexivity. }
  etransitivity.
  { exact (ran_leg_coherence
             ((((ttt, v); sq))
                : ran_id_obj a
                    ~{=(F a) ↓ F}~>
                  existT (fun p : (1 ∏ A)%category => F a ~> F (snd p))
                    (ttt, a') (fmap[F] v))). }
  (* right side: the reindexing property of ran_fmap at (a', id) / 右侧：ran_fmap 在 (a', id) 处的重索引属性 *)
  symmetry.
  etransitivity.
  { exact (ran_fmap_leg (fmap[F] v) (ran_id_obj a')). }
  change (ran_leg (existT (fun p : (1 ∏ A)%category => F a ~> F (snd p))
            (ttt, a') (@id B (F a') ∘ fmap[F] v))
            ≈ ran_leg (existT (fun p : (1 ∏ A)%category => F a ~> F (snd p))
                (ttt, a') (fmap[F] v))).
  apply ran_leg_transport.
  apply id_left.
Qed.

(*
 The mediating cone for the universal property: a transformation
 μ : M ◯ F ⟹ X spreads over the comma category as the cone with legs
 μ_a ∘ M f at (a, f). 

 --------
 关于泛性质的中介锥：一个变换 μ : M ◯ F ⟹ X 在逗号范畴上展开为具有腿 μ_a ∘ M f 于 (a, f) 的锥。
*)
Program Definition ran_ump_cone (M : B ⟶ C) (μ : M ◯ F ⟹ X) (b : B) :
  Cone (ran_comma_diagram b) :=
  @Build_Cone (=(b) ↓ F) C (ran_comma_diagram b) (M b)
    (@Build_ACone (=(b) ↓ F) C (M b) (ran_comma_diagram b)
       (fun x => transform[μ] (snd `1 x) ∘ fmap[M] (`2 x)) _).
Next Obligation.
  intros M μ b x y f; simpl.
  destruct x as [[tx ax] fx], y as [[ty ay] fy], f as [[u v] sq];
    simpl in *.
  rewrite id_right in sq.
  etransitivity; [ apply comp_assoc |].
  srewrite (@naturality _ _ _ _ μ _ _ v).
  etransitivity; [ symmetry; apply comp_assoc |].
  apply compose_respects; [ reflexivity |].
  etransitivity; [ symmetry; apply fmap_comp |].
  apply fmap_respects.
  now rewrite <- sq.
Qed.

Definition ran_ump_delta (M : B ⟶ C) (μ : M ◯ F ⟹ X) (b : B) :
  M b ~> ran_obj b :=
  unique_obj (@ump_limits _ _ _ (lim b) (ran_ump_cone M μ b)).

Lemma ran_ump_delta_leg (M : B ⟶ C) (μ : M ◯ F ⟹ X) (b : B)
  (x : =(b) ↓ F) :
  ran_leg x ∘ ran_ump_delta M μ b
    ≈ transform[μ] (snd `1 x) ∘ fmap[M] (`2 x).
Proof.
  exact (unique_property (@ump_limits _ _ _ (lim b) (ran_ump_cone M μ b)) x).
Qed.

Program Definition ran_ump_transform (M : B ⟶ C) (μ : M ◯ F ⟹ X) :
  M ⟹ Pointwise_Ran :=
  Build_Transform' (F := M) (G := Pointwise_Ran)
    (ran_ump_delta M μ) _.
Next Obligation.
  intros M μ b b' g; simpl.
  apply ran_jointly_monic; intro x.
  etransitivity.
  { etransitivity; [ apply comp_assoc |].
    apply compose_respects; [ exact (ran_fmap_leg g x) | reflexivity ]. }
  etransitivity; [ exact (ran_ump_delta_leg M μ b (ran_reindex g x)) |].
  change (transform[μ] (snd `1 x) ∘ fmap[M] (`2 x ∘ g)
            ≈ ran_leg x ∘ (ran_ump_delta M μ b' ∘ fmap[M] g)).
  symmetry.
  etransitivity; [ apply comp_assoc |].
  etransitivity.
  { apply compose_respects; [ exact (ran_ump_delta_leg M μ b' x) | reflexivity ]. }
  etransitivity; [ symmetry; apply comp_assoc |].
  apply compose_respects; [ reflexivity |].
  symmetry; exact (@fmap_comp _ _ M _ _ _ (`2 x) g).
Qed.

#[export] Program Instance Pointwise_LocalRightKan : LocalRightKan F X := {|
  LocalRan := Pointwise_Ran;
  ran_transform := ran_counit
|}.
Next Obligation.
  intros M μ.
  unshelve refine {| unique_obj := ran_ump_transform M μ |}.
  - (* factorization: μ_a ≈ ε_a ∘ δ_{F a} / 分解：μ_a ≈ ε_a ∘ δ_{F a} *)
    intro a; simpl.
    unfold ran_counit_component.
    symmetry.
    etransitivity; [ exact (ran_ump_delta_leg M μ (F a) (ran_id_obj a)) |].
    simpl.
    now rewrite fmap_id, id_right.
  - (* uniqueness / 独特性 *)
    intros v Hv b.
    apply ran_jointly_monic; intro x.
    etransitivity; [ exact (ran_ump_delta_leg M μ b x) |].
    destruct x as [[t a] f]; destruct t; simpl.
    (*
 μ_a ∘ M f ≈ ran_leg ((ttt,a); f) ∘ v_b, through the factorization
 hypothesis, naturality of v, and the leg at the identity 

 --------
 μ_a ∘ M f ≈ ran_leg ((ttt,a); f) ∘ v_b，通过分解假设、v 的自然性，以及单位元素处的 leg
*)
    etransitivity.
    { apply compose_respects; [ exact (Hv a) | reflexivity ]. }
    etransitivity; [ symmetry; apply comp_assoc |].
    etransitivity.
    { apply compose_respects; [ reflexivity |].
      symmetry; exact (@naturality _ _ _ _ v _ _ f). }
    etransitivity; [ apply comp_assoc |].
    symmetry.
    apply compose_respects; [| reflexivity ].
    unfold ran_counit_component.
    etransitivity.
    { apply (ran_leg_transport (ttt, a) f (id ∘ f)).
      now rewrite id_left. }
    symmetry.
    exact (ran_fmap_leg f (ran_id_obj a)).
Qed.

(* * *** Acceptance: the counit is the leg at the identity, on the nose / * *** 接受：余单位是在恒等元处的腿，完全准确 *)

Example ran_counit_is_identity_leg (a : A) :
  transform[@ran_transform _ _ _ _ _ Pointwise_LocalRightKan] a
    = ran_leg (ran_id_obj a) := eq_refl.

Example ran_extension_is_pointwise_limit (b : B) :
  @LocalRan _ _ F _ X Pointwise_LocalRightKan b
    = vertex_obj[(@limit_cone _ _ _ (lim b))] := eq_refl.

End PointwiseRan.

(* * ** The left Kan extension as a pointwise colimit / * ** 左Kan扩展作为逐点余极限 *)

Section PointwiseLan.

Context {A : Category}.
Context {B : Category}.
Context {F : A ⟶ B}.
Context {C : Category}.
Context (X : A ⟶ C).

(*
 The diagram whose colimit computes the extension at b: the comma
 category (F ↓ =(b)) of pairs (a, f : F a ~> b), projected to A and
 followed by X. 

 --------
 计算在 b 处扩展的余极限的图：逗号范畴 (F ↓ =(b))，由对 (a, f : F a ~> b) 构成，投影到 A 并随后到 X。
*)
Definition lan_comma_diagram (b : B) : (F ↓ =(b)) ⟶ C :=
  X ◯ @comma_proj1 _ _ _ F =(b).

Context (colim : ∀ b : B, Colimit (lan_comma_diagram b)).

Definition lan_obj (b : B) : C :=
  vertex_obj[@limit_cone _ _ _ (colim b)].

(* The colimit cone of [Colimit K = Limit K^op] is a Cocone K; its legs, read covariantly, are the injections. / [Colimit K = Limit K^op] 的余极锥是一个余锥 K；它的“腿”，按照协变方式读取，是注入映射。 *)
Definition lan_inj {b : B} (x : F ↓ =(b)) :
  lan_comma_diagram b x ~{C}~> lan_obj b :=
  cocone_inj (@limit_cone _ _ _ (colim b)) x.

Lemma lan_inj_coherence {b : B} {x y : F ↓ =(b)} (f : x ~{F ↓ =(b)}~> y) :
  lan_inj y ∘ fmap[lan_comma_diagram b] f ≈ lan_inj x.
Proof.
  exact (cocone_inj_coherence (@limit_cone _ _ _ (colim b)) f).
Qed.

Lemma lan_inj_transport {b : B} (t : (A ∏ 1)%category) (f f' : F (fst t) ~> b) :
  f ≈ f' →
  lan_inj (existT _ t f) ≈ lan_inj (existT _ t f').
Proof.
  intro Hf.
  assert (sq : f' ∘ fmap[F] (@id A (fst t)) ≈ fmap[=(b)] (@id 1 (snd t)) ∘ f).
  { simpl.
    rewrite fmap_id, id_left, id_right.
    now symmetry. }
  rewrite <- (lan_inj_coherence
                ((((@id A (fst t), ttt); sq))
                   : existT (fun p : (A ∏ 1)%category => F (fst p) ~> b) t f
                       ~{F ↓ =(b)}~> existT _ t f')).
  simpl.
  now rewrite fmap_id, id_right.
Qed.

(* The dual probe: a family out of the injections is a cocone, whence the injections are jointly epic. / 双探针：一个没有注射的族是一个余锥，因此这些注射是联合上射的。 *)
Program Definition lan_probe_cocone {b : B} {c : C} (u : lan_obj b ~> c) :
  Cocone (lan_comma_diagram b) :=
  @Build_Cone ((F ↓ =(b))^op) (C^op) ((lan_comma_diagram b)^op) c
    (@Build_ACone ((F ↓ =(b))^op) (C^op) c ((lan_comma_diagram b)^op)
       (fun x => u ∘ lan_inj x) _).
Next Obligation.
  intros b c u x y f; simpl.
  rewrite <- comp_assoc.
  now rewrite (lan_inj_coherence f).
Qed.

Lemma lan_jointly_epic {b : B} {c : C} (u v : lan_obj b ~> c) :
  (∀ x : F ↓ =(b), u ∘ lan_inj x ≈ v ∘ lan_inj x) →
  u ≈ v.
Proof.
  intro H.
  pose proof (colimitcocone_ump
                (colimit_colimitcocone (colim b)) (lan_probe_cocone u)) as U.
  transitivity (unique_obj U).
  - symmetry; apply (uniqueness U); intro x; reflexivity.
  - apply (uniqueness U); intro x; symmetry; apply H.
Qed.

(* * *** Reindexing, and the extension functor / * *** 重新索引，以及拓展函子 *)

(*
 g : b ~> b' postcomposes the comma component: (a, f : F a ~> b) becomes
 (a, g ∘ f : F a ~> b'). 

 --------
 g : b ~> b' 后组成逗号分量：(a, f : F a ~> b) 变为 (a, g ∘ f : F a ~> b')。
*)
Program Definition lan_reindex {b b' : B} (g : b ~> b') :
  (F ↓ =(b)) ⟶ (F ↓ =(b')) := {|
  fobj := fun x => existT _ (`1 x) (g ∘ `2 x);
  fmap := fun x y f => (`1 f; _)
|}.
Next Obligation.
  intros b b' g x y f.
  destruct f as [[u v] sq]; simpl in *.
  rewrite id_left in sq.
  rewrite id_left.
  rewrite <- comp_assoc.
  now rewrite sq.
Qed.
Next Obligation.
  intros b b' g x y f f' [e1 e2]; simpl.
  split; assumption.
Qed.
Next Obligation.
  intros b b' g x; simpl.
  split; reflexivity.
Qed.
Next Obligation.
  intros b b' g x y z f f'; simpl.
  split; reflexivity.
Qed.

(*
 The restricted cocone: the b'-injections at reindexed objects form a
 cocone over the b-diagram. 

 --------
 受限余锥：在重索引对象上的 b'-注入形成 b-图上的余锥。
*)
Program Definition lan_restrict_cocone {b b' : B} (g : b ~> b') :
  Cocone (lan_comma_diagram b) :=
  @Build_Cone ((F ↓ =(b))^op) (C^op) ((lan_comma_diagram b)^op)
    (lan_obj b')
    (@Build_ACone ((F ↓ =(b))^op) (C^op) (lan_obj b')
       ((lan_comma_diagram b)^op)
       (fun x => lan_inj (lan_reindex g x)) _).
Next Obligation.
  intros b b' g x y f; simpl.
  exact (lan_inj_coherence (fmap[lan_reindex g] f)).
Qed.

Definition lan_fmap {b b' : B} (g : b ~> b') : lan_obj b ~> lan_obj b' :=
  unique_obj (colimitcocone_ump (colimit_colimitcocone (colim b))
                (lan_restrict_cocone g)).

Lemma lan_fmap_inj {b b' : B} (g : b ~> b') (x : F ↓ =(b)) :
  lan_fmap g ∘ lan_inj x ≈ lan_inj (lan_reindex g x).
Proof.
  exact (unique_property
           (colimitcocone_ump (colimit_colimitcocone (colim b))
              (lan_restrict_cocone g)) x).
Qed.

Program Definition Pointwise_Lan : B ⟶ C := {|
  fobj := lan_obj;
  fmap := fun b b' g => lan_fmap g
|}.
Next Obligation.
  intros b b' g g' Hg.
  apply lan_jointly_epic; intro x.
  etransitivity; [ exact (lan_fmap_inj g x) |].
  etransitivity; [| symmetry; exact (lan_fmap_inj g' x) ].
  destruct x as [t f]; simpl.
  apply lan_inj_transport.
  now rewrite Hg.
Qed.
Next Obligation.
  intro b.
  apply lan_jointly_epic; intro x.
  etransitivity; [ exact (lan_fmap_inj id x) |].
  etransitivity; [| symmetry; apply id_left ].
  destruct x as [t f]; simpl.
  apply lan_inj_transport.
  apply id_left.
Qed.
Next Obligation.
  intros b b' b'' g' g.
  apply lan_jointly_epic; intro x.
  etransitivity; [ exact (lan_fmap_inj (g' ∘ g) x) |].
  symmetry.
  etransitivity; [ symmetry; apply comp_assoc |].
  etransitivity.
  { apply compose_respects; [ reflexivity | exact (lan_fmap_inj g x) ]. }
  etransitivity; [ exact (lan_fmap_inj g' (lan_reindex g x)) |].
  destruct x as [t f]; simpl.
  apply lan_inj_transport.
  apply comp_assoc.
Qed.

(* * *** The unit, and the local universal property / * *** 单位，以及局部泛性质 *)

Definition lan_id_obj (a : A) : F ↓ =(F a) :=
  existT (fun p : A ∏ 1 => F (fst p) ~> F a) (a, ttt) id.

(*
 The unit component at a is the colimit injection at the identity —
 Riehl's display (6.2.2). 

 --------
 在 a 处的单位分量是恒等映射的余极限注入——Riehl 的展示 (6.2.2)。
*)
Definition lan_unit_component (a : A) :
  X a ~> Pointwise_Lan (F a) := lan_inj (lan_id_obj a).

Program Definition lan_unit : X ⟹ Pointwise_Lan ◯ F :=
  Build_Transform' (F := X) (G := Pointwise_Lan ◯ F)
    lan_unit_component _.
Next Obligation.
  intros a a' v; simpl.
  unfold lan_unit_component.
  (*
 left side: the reindexing property of lan_fmap at (a, id); right
 side: coherence along the comma morphism (v, ttt) from (a, F v) to
 (a', id) in (F ↓ =(F a')) 

 --------
 左侧：在 (a, id) 处的 lan_fmap 的重新索引性质；右侧：沿从 (a, F v) 到 (a', id) 的逗号态射 (v, ttt) 在 (F ↓ =(F a')) 中的相干性
*)
  assert (sq : @id B (F a') ∘ fmap[F] v
                 ≈ fmap[=(F a')] (@id 1 ttt) ∘ fmap[F] v).
  { simpl; reflexivity. }
  etransitivity; [ exact (lan_fmap_inj (fmap[F] v) (lan_id_obj a)) |].
  symmetry.
  etransitivity.
  { exact (lan_inj_coherence
             ((((v, ttt); sq))
                : existT (fun p : (A ∏ 1)%category => F (fst p) ~> F a')
                    (a, ttt) (fmap[F] v)
                    ~{F ↓ =(F a')}~> lan_id_obj a')). }
  change (lan_inj (existT (fun p : (A ∏ 1)%category => F (fst p) ~> F a')
            (a, ttt) (fmap[F] v))
            ≈ lan_inj (existT (fun p : (A ∏ 1)%category => F (fst p) ~> F a')
                (a, ttt) (fmap[F] v ∘ @id B (F a)))).
  apply lan_inj_transport.
  now rewrite id_right.
Qed.

(*
 The mediating cocone for the universal property: a transformation
 ε : X ⟹ M ◯ F spreads over the comma category as the cocone with legs
 M f ∘ ε_a at (a, f). 

 --------
 通用性质的中介余锥：一个变换
 ε : X ⟹ M ◯ F 在逗号范畴上展开为余锥，其余锥的边是
 在 (a, f) 处的 M f ∘ ε_a。
*)
Program Definition lan_ump_cocone (M : B ⟶ C) (ε : X ⟹ M ◯ F) (b : B) :
  Cocone (lan_comma_diagram b) :=
  @Build_Cone ((F ↓ =(b))^op) (C^op) ((lan_comma_diagram b)^op) (M b)
    (@Build_ACone ((F ↓ =(b))^op) (C^op) (M b) ((lan_comma_diagram b)^op)
       (fun x => fmap[M] (`2 x) ∘ transform[ε] (fst `1 x)) _).
Next Obligation.
  intros M ε b x y f; simpl.
  destruct x as [[ax tx] fx], y as [[ay ty] fy], f as [[u v] sq];
    simpl in *.
  rewrite id_left in sq.
  etransitivity; [ symmetry; apply comp_assoc |].
  srewrite_r (@naturality _ _ _ _ ε _ _ u).
  etransitivity; [ apply comp_assoc |].
  apply compose_respects; [| reflexivity ].
  etransitivity; [ symmetry; exact (@fmap_comp _ _ M _ _ _ fx (fmap[F] u)) |].
  apply fmap_respects.
  now rewrite sq.
Qed.

Definition lan_ump_delta (M : B ⟶ C) (ε : X ⟹ M ◯ F) (b : B) :
  lan_obj b ~> M b :=
  unique_obj (colimitcocone_ump (colimit_colimitcocone (colim b))
                (lan_ump_cocone M ε b)).

Lemma lan_ump_delta_inj (M : B ⟶ C) (ε : X ⟹ M ◯ F) (b : B)
  (x : F ↓ =(b)) :
  lan_ump_delta M ε b ∘ lan_inj x
    ≈ fmap[M] (`2 x) ∘ transform[ε] (fst `1 x).
Proof.
  exact (unique_property
           (colimitcocone_ump (colimit_colimitcocone (colim b))
              (lan_ump_cocone M ε b)) x).
Qed.

Program Definition lan_ump_transform (M : B ⟶ C) (ε : X ⟹ M ◯ F) :
  Pointwise_Lan ⟹ M :=
  Build_Transform' (F := Pointwise_Lan) (G := M)
    (lan_ump_delta M ε) _.
Next Obligation.
  intros M ε b b' g; simpl.
  apply lan_jointly_epic; intro x.
  etransitivity; [ symmetry; apply comp_assoc |].
  etransitivity.
  { apply compose_respects; [ reflexivity | exact (lan_ump_delta_inj M ε b x) ]. }
  etransitivity; [ apply comp_assoc |].
  etransitivity.
  { apply compose_respects;
      [ symmetry; exact (@fmap_comp _ _ M _ _ _ g (`2 x)) | reflexivity ]. }
  symmetry.
  etransitivity; [ symmetry; apply comp_assoc |].
  etransitivity.
  { apply compose_respects; [ reflexivity | exact (lan_fmap_inj g x) ]. }
  etransitivity; [ exact (lan_ump_delta_inj M ε b' (lan_reindex g x)) |].
  reflexivity.
Qed.

#[export] Program Instance Pointwise_LocalLeftKan : LocalLeftKan F X := {|
  LocalLan := Pointwise_Lan;
  lan_transform := lan_unit
|}.
Next Obligation.
  intros M ε.
  unshelve refine {| unique_obj := lan_ump_transform M ε |}.
  - (* factorization: ε_a ≈ δ_{F a} ∘ η_a / 分解：ε_a ≈ δ_{F a} ∘ η_a *)
    intro a; simpl.
    unfold lan_unit_component.
    symmetry.
    etransitivity; [ exact (lan_ump_delta_inj M ε (F a) (lan_id_obj a)) |].
    simpl.
    now rewrite fmap_id, id_left.
  - (* uniqueness / 独特性 *)
    intros v Hv b.
    apply lan_jointly_epic; intro x.
    etransitivity; [ exact (lan_ump_delta_inj M ε b x) |].
    destruct x as [[a t] f]; destruct t; simpl.
    (*
 M f ∘ ε_a ≈ v_b ∘ lan_inj ((a,ttt); f), through the factorization
 hypothesis, naturality of v, and the injection at the identity 

 --------
 M f ∘ ε_a ≈ v_b ∘ lan_inj ((a,ttt); f)，通过分解假设、v 的自然性，以及在恒等映射处的注入
*)
    symmetry.
    etransitivity.
    { apply compose_respects; [ reflexivity |].
      etransitivity.
      { apply (lan_inj_transport (a, ttt) f (f ∘ id)).
        now rewrite id_right. }
      symmetry.
      exact (lan_fmap_inj f (lan_id_obj a)). }
    etransitivity; [ apply comp_assoc |].
    etransitivity.
    { apply compose_respects;
        [ symmetry; exact (@naturality _ _ _ _ v _ _ f) | reflexivity ]. }
    etransitivity; [ symmetry; apply comp_assoc |].
    apply compose_respects; [ reflexivity |].
    symmetry; exact (Hv a).
Qed.

(* * *** Acceptance: the unit is the injection at the identity, on the nose / * *** 接受性：该单位是在同一元素处的注入，完全一致 *)

Example lan_unit_is_identity_inj (a : A) :
  transform[@lan_transform _ _ _ _ _ Pointwise_LocalLeftKan] a
    = lan_inj (lan_id_obj a) := eq_refl.

Example lan_extension_is_pointwise_colimit (b : B) :
  @LocalLan _ _ F _ X Pointwise_LocalLeftKan b
    = vertex_obj[@limit_cone _ _ _ (colim b)] := eq_refl.

End PointwiseLan.
