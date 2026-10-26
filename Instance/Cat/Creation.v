Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Theory.Equivalence.Creation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Slice.Adjunction.
Require Import Category.Construction.Slice.Creation.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Pullback.
Require Import Category.Instance.Adjoints.
Require Import Category.Adjunction.Continuity.

Set Universe Polymorphism.

Generalizable All Variables.

(* * * Creation of limits is stable under the fibre product of categories / * * 极限的构造在范畴的纤维积下是稳定的 *)

(*
 nLab: https://ncatlab.org/nlab/show/created+limit
 nLab: https://ncatlab.org/nlab/show/pullback

 Mac Lane §V.6 Exercises 3 and 4 (book p. 125).  Exercise 3 asks that
 creation of limits be stable under pullback in [Cat]: given a cospan
 [F : A ⟶ C], [G : B ⟶ C] and the pullback [P] of the two, if [F] creates
 the limits [G] preserves then the projection [P ⟶ B] creates them.
 Exercise 4 asks that the comma category be recovered as such a pullback,
 giving a second proof that its projection creates limits.

 READ THE FIRST WORD OF THAT PRECISELY, because the tree already refutes
 the naive reading.  Instance/Cat/Pullback.v proves
 [FibreProduct_not_Cat_pullback]: the fibre product of categories is NOT a
 pullback in [Cat].  Read THAT narrowly in turn, as its own file insists
 (Instance/Cat/Pullback.v): it is a refutation AT ONE
 COSPAN, [1 --true--> Indiscrete bool <--false-- 1], where the apex is
 object-empty; the same cospan does have a [Cat] pullback, and nothing in
 the tree refutes [FibreProduct (Coslice_Proj d) U] as a [Cat] pullback of
 ITS cospan.  (An earlier revision of this header, of the commit message
 and of the docs/INDEX.md bullet said the coslice apex was “refuted for
 this object”; measured, the refutation is at the [Indiscrete bool]
 cospan and says nothing about the coslice one.)  What the fibre product
 is is a pullback in [StrictCat], and even there only under [ObjUIP C]
 ([FibreProduct_IsPullback]); whether [Cat] has pullbacks at all is
 neither proved nor refuted anywhere.  So the honest Exercise 3 is a
 theorem about [FibreProduct] — the object that IS the pullback where the
 tree can say so — and that is what is proved here.  Nothing below asserts
 a pullback square in [Cat].

 Two things are worth naming before the statements.

 First, this proof needs NO [ObjUIP].  It never touches
 [FibreProduct_IsPullback]; it works with the apex's own data, the stored
 equality [`2 (K j) : F (KA j) = G (KB j)] and the stored cast condition
 on arrows, both of which are definitional.  The printed type of
 [fp_snd_StrictlyCreatesLimit] carries no [uip] argument.

 Second, what it DOES need is that the bottom functor create limits
 STRICTLY, not merely up to isomorphism.  The created apex pairs the
 upstairs lift's vertex with the given cone's and stores [slift_eq] as its
 third component, and that component must be a Leibniz [=] because that is
 what an object of a fibre product stores; an isomorphism will not go in
 its place.
 Test/ProbeCatCreation439.v's negative n3 records the refusal against the
 accepted control beside it.  In exchange the conclusion is strict too:
 both [StrictLift] fields come out [eq_refl] and [reflexivity], at every
 limiting cone downstairs.

 The generic kit — [CreatesLimit_transport] and the [IsLimitCone]
 transport it rests on — is not about [Cat] at all, and its natural home
 is Structure/Limit/Creation.v, where appending is line-neutral for all
 fifteen of that file's citations (the highest of them is the upper
 endpoint of the range cited at doc/plan/books/qa; an earlier revision of
 this sentence named the highest single-line citation instead, and both
 are inside the 518-line file).  It lives here instead, for this change,
 because that costs no rebuild of that file's large reverse-dependency
 set and because it is where #428 put the analogous
 [PreservesLimitCone_transport] (Functor/Hom/Continuous.v).  A later
 move costs nothing.

 Of the two [IsLimitCone] transports below only [islimitcone_dtransport_inv]
 is consumed; [islimitcone_dtransport] is its mirror image, shipped for
 symmetry with NO consumer in this file or anywhere in the tree.  An
 earlier revision of this sentence said the kit rests on both.

 Two further disclosures of prior art, neither of them reuse.
 [fp_square_iso] re-derives a fact Instance/Cat/Pullback.v already
 carries as [FP_commutes_cat : F ∘[Cat] FP_fst ≈[Cat] G ∘[Cat] FP_snd]:
 whiskering that with this file's own [fun_equiv_whisker_r] typechecks at
 exactly [fp_square_iso]'s type, though the two terms are not convertible.
 And [fun_equiv_whisker_r] itself is written as a tactic proof for a
 version reason recorded at its definition. 

 --------
 nLab：https://ncatlab.org/nlab/show/created+limit 
 nLab：https://ncatlab.org/nlab/show/pullback 

 Mac Lane §V.6 练习 3 和 4（书本第 125 页）。练习 3 要求在 [Cat] 中，极限的构造在拉回下保持稳定：给定一个余叉 [F : A ⟶ C]、[G : B ⟶ C] 及它们的拉回 [P]，如果 [F] 创造了 [G] 的极限并且被保存，那么投影 [P ⟶ B] 也创造它们。练习 4 要求将逗号范畴作为这样的拉回重建，从而提供其投影创造极限的第二种证明。精确地阅读那个第一个词，因为该树已经驳斥了天真的解读。Instance/Cat/Pullback.v 证明了 [FibreProduct_not_Cat_pullback]：范畴的纤维积在 [Cat] 中**不是**一个拉回。依次狭义地阅读它，正如它自己的文件（Instance/Cat/Pullback.v）所坚持的：它是在一个余叉 [1 --true--> Indiscrete bool <--false-- 1] 上的驳斥，其中顶点是对象为空；同一个余叉确实有 [Cat] 拉回，并且树中的内容没有驳斥 [FibreProduct (Coslice_Proj d) U] 作为其余叉的 [Cat] 拉回。(这个标题、提交信息以及 docs/INDEX.md 项目符号的早期版本曾说余片顶点对“这个对象是被驳斥的”；实际上，这种驳斥出现在 [Indiscrete bool] 的余积图上，并没有涉及余片的情况。) 纤维积是什么，是 [StrictCat] 中的拉回，即使在那里也只在 [ObjUIP C]（[FibreProduct_IsPullback]）的条件下存在；是否 [Cat] 中存在拉回，在任何地方都没有被证明或驳斥。所以，诚实的练习 3 是关于 [FibreProduct] 的定理——这是可以称为拉回的对象——这正是在这里被证明的。下面没有任何内容断言 [Cat] 中存在拉回方形。

 在陈述之前，有两件事情值得说明。首先，这个证明不需要 [ObjUIP]。它从不接触 [FibreProduct_IsPullback]；它使用的是顶点自身的数据、存储的等式 [`2 (K j) : F (KA j) = G (KB j)] 以及箭头上的存储强制条件，这两者都是定义性的。ZWZ25WZZ 的打印类型不包含 [uip] 参数。其次，它确实需要的是底层函子严格地创建极限，而不仅仅是同构意义上的。创建的顶点将上层提升的顶点与给定锥的顶点配对，并将 [slift_eq] 作为其第三个分量存储，而该分量必须是 Leibniz [=]，因为这正是一个纤维积对象所存储的；同构不能取代它。Test/ProbeCatCreation439.v 中的负例 n3 记录了对旁边已接受控制的拒绝。作为交换，结论也是严格的：两个 [StrictLift] 字段在每个底层极限锥处分别输出 [eq_refl] 和 [reflexivity]。通用套件 —— [CreatesLimit_transport] 以及 [IsLimitCone] 所依赖的传输 —— 完全与 [Cat] 无关，其自然归属是 Structure/Limit/Creation.v，对于该文件的所有十五条引用（其中最高的是在 doc/plan/books/qa 中引用范围的上端点；这句话的早期版本则命名了最高单行引用，两者都在 518 行的文件内） 添加操作对行是中性的。这个变化使它放在这里，是因为这样不需要重建该文件的大量反向依赖集，并且因为 #428 将类似的 [PreservesLimitCone_transport]（Functor/Hom/Continuous.v） 放在了这里。之后移动也不会有任何成本。在下面的两个 [IsLimitCone] 传输中，只有 [islimitcone_dtransport_inv] 被消耗；[islimitcone_dtransport] 是它的镜像，为了对称而发送，在此文件或整个树中没有消费者。该句的早期版本说套件依赖于两者。

 另外披露了两条先前技术，其中都没有重用。[fp_square_iso] 重新推导了一个事实 Instance/Cat/Pullback.v 已经承载的作为 [FP_commutes_cat : F ∘[Cat] FP_fst ≈ [Cat] G ∘ [Cat] FP_snd 的事实：用该文件自身的 [fun_equiv_whisker_r] 处理后类型精确为 [fp_square_iso] 的类型，尽管这两个项不可转换。而 [fun_equiv_whisker_r] 本身则以策略证明的方式书写，用于其定义中记录的版本原因。
*)

(* * ** Cast algebra, with all endpoints variables / * ** 强制类型转换代数，包含所有端点变量 *)

Lemma cast_solve {C : Category} {a b a' b' : C} (ex : a = a') (ey : b = b')
  (u : a ~{C}~> b) (v : a' ~{C}~> b') :
  id_cast ey ∘ u ∘ id_cast (eq_sym ex) ≈ v →
  u ≈ id_cast (eq_sym ey) ∘ v ∘ id_cast ex.
Proof.
  destruct ex, ey; simpl; intro H.
  rewrite id_left, id_right in H.
  rewrite id_left, id_right.
  now symmetry.
Qed.

Lemma cast_from_rew {C : Category} {a b c d : C} (p : a = b) (q : c = d)
  (u : a ~{C}~> c) (v : b ~{C}~> d) :
  hom_rew p u ≈ id_cast (eq_sym q) ∘ v → hom_cast p q u ≈ v.
Proof.
  destruct p, q; simpl; intro H.
  rewrite id_left in H.
  exact H.
Qed.

Lemma cast_shuffle {C : Category} {a b c d : C} (p : a = b) (q : c = d)
  (u : a ~{C}~> c) (v : b ~{C}~> d) :
  id_cast q ∘ u ∘ id_cast (eq_sym p) ≈ v →
  u ∘ id_cast (eq_sym p) ≈ id_cast (eq_sym q) ∘ v.
Proof.
  destruct p, q; simpl; intro H.
  rewrite id_left, id_right in H.
  rewrite !id_right, id_left.
  now symmetry.
Qed.

Lemma cast_unit_cod {C : Category} {a b : C} (e : a = b) :
  hom_cast eq_refl e (id_cast (eq_sym e)) ≈ id.
Proof. destruct e; simpl; reflexivity. Qed.

Lemma cast_unit_dom {C : Category} {a b : C} (e : a = b) :
  hom_cast e eq_refl (id_cast e) ≈ id.
Proof. destruct e; simpl; reflexivity. Qed.

Lemma cast_transfer {C : Category} {a b a' b' t : C}
  (e : a = a') (e' : b = b') (k : a ~{C}~> b) (u : t ~{C}~> a)
  (v : t ~{C}~> b) (m : a' ~{C}~> b') :
  v ≈ k ∘ u → id_cast e' ∘ k ∘ id_cast (eq_sym e) ≈ m →
  id_cast e' ∘ v ≈ m ∘ (id_cast e ∘ u).
Proof.
  destruct e, e'; simpl; intros H1 H2.
  rewrite id_left, id_right in H2.
  rewrite !id_left.
  now rewrite H1, <- H2.
Qed.

(* * ** A limiting cone stays limiting along an isomorphism of diagrams / * ** 限制圆锥在图的同构下仍然是限制圆锥 *)

Section DiagTransport.

Context {J C : Category}.
Context {G G' : J ⟶ C}.
Context (e : G ≈ G').

Definition islimitcone_dtransport {N : Cone G} (HN : IsLimitCone N) :
  IsLimitCone (cone_transport e N).
Proof.
  intro M.
  unshelve refine {| unique_obj := unique_obj (HN (cone_transport_inv e M)) |}.
  - intro x.
    change (to (`1 e x) ∘ cone_leg N x
              ∘ unique_obj (HN (cone_transport_inv e M)) ≈ cone_leg M x).
    rewrite <- comp_assoc.
    rewrite (unique_property (HN (cone_transport_inv e M)) x).
    change (to (`1 e x) ∘ (from (`1 e x) ∘ cone_leg M x) ≈ cone_leg M x).
    rewrite comp_assoc, iso_to_from.
    now rewrite id_left.
  - intros v Hv.
    apply (uniqueness (HN (cone_transport_inv e M))).
    intro x.
    change (cone_leg N x ∘ v ≈ from (`1 e x) ∘ cone_leg M x).
    rewrite <- (Hv x).
    change (cone_leg N x ∘ v
              ≈ from (`1 e x) ∘ (to (`1 e x) ∘ cone_leg N x ∘ v)).
    rewrite !comp_assoc, iso_from_to.
    now rewrite id_left.
Defined.

Definition islimitcone_dtransport_inv {N : Cone G'} (HN : IsLimitCone N) :
  IsLimitCone (cone_transport_inv e N).
Proof.
  intro M.
  unshelve refine {| unique_obj := unique_obj (HN (cone_transport e M)) |}.
  - intro x.
    change (from (`1 e x) ∘ cone_leg N x
              ∘ unique_obj (HN (cone_transport e M)) ≈ cone_leg M x).
    rewrite <- comp_assoc.
    rewrite (unique_property (HN (cone_transport e M)) x).
    change (from (`1 e x) ∘ (to (`1 e x) ∘ cone_leg M x) ≈ cone_leg M x).
    rewrite comp_assoc, iso_from_to.
    now rewrite id_left.
  - intros v Hv.
    apply (uniqueness (HN (cone_transport e M))).
    intro x.
    change (cone_leg N x ∘ v ≈ to (`1 e x) ∘ cone_leg M x).
    rewrite <- (Hv x).
    change (cone_leg N x ∘ v
              ≈ to (`1 e x) ∘ (from (`1 e x) ∘ cone_leg N x ∘ v)).
    rewrite !comp_assoc, iso_to_from.
    now rewrite id_left.
Defined.

End DiagTransport.

(* * ** Creation transports along an isomorphism of the functor / * ** 创建沿着函子同构进行传输 *)

(*
 The creation analogue of Functor/Hom/Continuous.v's
 [PreservesLimitCone_transport].  It carries CREATION, not strictness:
 there is still no [StrictlyCreatesLimit_transport] and none is claimed. 

 --------
 Functor/Hom/Continuous.v 的创建类似物 [PreservesLimitCone_transport]。它承载的是 CREATION，而不是严格性：仍然没有 [StrictlyCreatesLimit_transport]，也没有声明存在。
*)

#[local] Obligation Tactic := idtac.

(*
 Written as a tactic proof rather than as the anonymous-constructor term
 [(fun j => `1 e (K j); fun x y f => `2 e _ _ (fmap[K] f))], which Rocq 9.1
 accepts but Coq 8.19 and 8.20 refuse: checking that pair against the
 expected type, their elaborator compares [fmap[F ◯ K] f] with
 [fmap[F] (fmap[K] f)] by unification rather than by conversion and
 reports “cannot unify”.  [exact] uses full conversion and is accepted by
 all three.  The [Defined] is load-bearing: [CreatesLimit_transport]'s
 proof does a [change] through this definition's first component, and
 [Qed] here stops the file at that step with “Not convertible”. 

 --------
 作为战术证明而不是匿名构造项 [(fun j => `1 e (K j); fun x y f => `2 e _ _ (fmap[K]  f))] 编写，Rocq 9.1 接受，但 Coq 8.19 和 8.20 拒绝：在将 pair 与预期类型进行检查时，它们的展开器通过统一而不是通过转换来比较 [fmap[F ◯ K]  f] 和 [fmap[F]  (fmap [K]  f)] 并报告“无法统一”。 [exact] 使用完全转换，并被所有三个版本接受。 [Defined] 是承重的：[CreatesLimit_transport] 的证明通过该定义的第一个分量进行 [change]，而 [Qed] 在此处以“不可转换”停止了文件处理。
*)

Definition fun_equiv_whisker_r {J C D : Category} {F F' : C ⟶ D}
  (e : F ≈ F') (K : J ⟶ C) : (F ◯ K) ≈ (F' ◯ K).
Proof.
  exists (fun j => `1 e (K j)).
  intros x y f.
  exact (`2 e _ _ (fmap[K] f)).
Defined.

Section CreatesTransport.

Context {J C D : Category}.
Context {K : J ⟶ C}.
Context {F F' : C ⟶ D}.
Context (e : F ≈ F').
Context (CR : CreatesLimit K F).

Notation w := (fun_equiv_whisker_r e K).

Definition ctr_lift (N : Cone (F' ◯ K)) (HN : IsLimitCone N) : Cone K :=
  creates_lift (cone_transport_inv w N) (islimitcone_dtransport_inv w HN).

Program Definition ctr_over (N : Cone (F' ◯ K)) (HN : IsLimitCone N) :
  ConeIso (FCone F' (ctr_lift N HN)) N :=
  (iso_compose
     `1 (creates_lift_over (cone_transport_inv w N)
           (islimitcone_dtransport_inv w HN))
     (iso_sym (`1 e (vertex_obj[ctr_lift N HN]))); _).
Next Obligation.
  intros N HN x.
  pose proof (`2 (creates_lift_over (cone_transport_inv w N)
                    (islimitcone_dtransport_inv w HN)) x) as Hx.
  cbv beta in Hx.
  change (cone_leg (cone_transport_inv w N) x)
    with (from (`1 e (K x)) ∘ cone_leg N x) in Hx.
  simpl.
  rewrite comp_assoc.
  assert (Hy : cone_leg N x
                 ∘ to `1 (creates_lift_over (cone_transport_inv w N)
                            (islimitcone_dtransport_inv w HN))
               ≈ to (`1 e (K x)) ∘ fmap[F] (cone_leg (ctr_lift N HN) x)).
  { rewrite <- Hx.
    rewrite !comp_assoc, iso_to_from.
    now rewrite id_left. }
  rewrite Hy.
  rewrite <- comp_assoc.
  rewrite (fun_equiv_fmap_from e _ _ (cone_leg (ctr_lift N HN) x)).
  rewrite comp_assoc, iso_to_from.
  now rewrite id_left.
Qed.

Program Definition ctr_fcone_iso (M : Cone K) :
  ConeIso (cone_transport_inv w (FCone F' M)) (FCone F M) :=
  (iso_sym (`1 e (vertex_obj[M])); _).
Next Obligation.
  intros M x.
  simpl.
  exact (fun_equiv_fmap_from e _ _ (cone_leg M x)).
Qed.

Definition ctr_reflect (M : Cone K) (H : IsLimitCone (FCone F' M)) :
  IsLimitCone M :=
  creates_reflect M
    (limitcone_transport (ctr_fcone_iso M)
       (islimitcone_dtransport_inv w H)).

Definition CreatesLimit_transport : CreatesLimit K F' :=
  {| creates_lift      := ctr_lift;
     creates_lift_over := ctr_over;
     creates_reflect   := ctr_reflect |}.

End CreatesTransport.

(** ** Mac Lane §V.6 Exercise 3 / ** 马克·莱恩 §V.6 练习 3 *)

Section Ex3.

Context {A B C : Category}.
Context (F : A ⟶ C) (G : B ⟶ C).
Context {J : Category}.
Context (K : J ⟶ FibreProduct F G).

Notation P  := (FibreProduct F G).
Notation p1 := (FP_fst F G).
Notation p2 := (FP_snd F G).
Notation KA := (p1 ◯ K).
Notation KB := (p2 ◯ K).

(* The square commutes definitionally: both components are the fibre product's own stored data, read off the diagram. / 这个方格在定义上是交换的：两个分量都是纤维积自身存储的数据，从图中读取。 *)

Definition fp_square_obj (j : J) : F (KA j) = G (KB j) := `2 (K j).

Definition fp_square_hom {x y : J} (f : x ~{J}~> y) :
  hom_cast (fp_square_obj x) (fp_square_obj y) (fmap[F ◯ KA] f) ≈ fmap[G ◯ KB] f
  := `2 (fmap[K] f).

Program Definition fp_square_iso : (F ◯ KA) ≈ (G ◯ KB) :=
  (fun j => id_cast_iso (fp_square_obj j); _).
Next Obligation.
  intros x y f.
  pose proof (fp_square_hom f) as Hf; cbv beta in Hf.
  rewrite hom_cast_decompose in Hf.
  exact (cast_solve _ _ _ _ Hf).
Qed.

(* The [F]-image of the [A]-projection of a cone is limiting as soon as the [G]-image of its [B]-projection is — the square, read as a transport. / 锥体的 [F] 图像在其 [A] 投影是极限时就是极限——其 [G] 图像在 [B] 投影是极限时——该平方，作为一种运输来解读。 *)

Section FImage.

Context (W : Cone K).
Context (HW : IsLimitCone (FCone G (FCone p2 W))).

Program Definition fp_F_image_coneiso :
  ConeIso (cone_transport_inv fp_square_iso (FCone G (FCone p2 W)))
          (FCone F (FCone p1 W)) :=
  (id_cast_iso (eq_sym (`2 vertex_obj[W])); _).
Next Obligation.
  intro x.
  pose proof (`2 (cone_leg W x)) as Hx; cbv beta in Hx.
  rewrite hom_cast_decompose in Hx.
  exact (cast_shuffle _ _ _ _ Hx).
Qed.

Definition fp_F_image_limiting : IsLimitCone (FCone F (FCone p1 W)) :=
  limitcone_transport fp_F_image_coneiso
    (islimitcone_dtransport_inv fp_square_iso HW).

End FImage.

(* * ** Pairing the two coordinate mediators / * ** 配对两个协调调解者 *)

Section Pairing.

Context (W : Cone K).
Context (H1 : IsLimitCone (FCone p1 W)).
Context (H2 : IsLimitCone (FCone p2 W)).
Context (H3 : IsLimitCone (FCone G (FCone p2 W))).

Section AtCompetitor.

Context (Q : Cone K).

(* The fibre product's side condition on the paired mediator is not extra data: it is uniqueness in [C], both sides mediating the same cone. / 纤维积在配对中介上的附加条件不是额外数据：它是在 [C] 中的唯一性，即双方都调解相同的锥。 *)

Lemma fp_med_cast :
  hom_cast (`2 vertex_obj[Q]) (`2 vertex_obj[W])
    (fmap[F] (unique_obj (H1 (FCone p1 Q))))
  ≈ fmap[G] (unique_obj (H2 (FCone p2 Q))).
Proof using H1 H2 H3.
  transitivity (unique_obj (H3 (FCone G (FCone p2 Q)))).
  - symmetry.
    apply (uniqueness (H3 (FCone G (FCone p2 Q)))).
    intro j.
    change (fmap[G] (fmap[p2] (cone_leg W j))
              ∘ hom_cast (`2 vertex_obj[Q]) (`2 vertex_obj[W])
                  (fmap[F] (unique_obj (H1 (FCone p1 Q))))
            ≈ fmap[G] (fmap[p2] (cone_leg Q j))).
    rewrite <- (`2 (cone_leg W j)).
    rewrite hom_cast_comp.
    rewrite <- fmap_comp.
    rewrite (unique_property (H1 (FCone p1 Q)) j).
    exact (`2 (cone_leg Q j)).
  - apply (uniqueness (H3 (FCone G (FCone p2 Q)))).
    intro j.
    change (fmap[G] (fmap[p2] (cone_leg W j))
              ∘ fmap[G] (unique_obj (H2 (FCone p2 Q)))
            ≈ fmap[G] (fmap[p2] (cone_leg Q j))).
    rewrite <- fmap_comp.
    apply fmap_respects.
    exact (unique_property (H2 (FCone p2 Q)) j).
Qed.

Definition fp_med : vertex_obj[Q] ~{P}~> vertex_obj[W] :=
  ((unique_obj (H1 (FCone p1 Q)), unique_obj (H2 (FCone p2 Q))); fp_med_cast).

End AtCompetitor.

Definition fp_islimitcone : IsLimitCone W.
Proof using H1 H2 H3.
  intro Q.
  unshelve refine {| unique_obj := fp_med Q |}.
  - intro j.
    split.
    + exact (unique_property (H1 (FCone p1 Q)) j).
    + exact (unique_property (H2 (FCone p2 Q)) j).
  - intros v Hv.
    split.
    + apply (uniqueness (H1 (FCone p1 Q))).
      intro j. exact (fst (Hv j)).
    + apply (uniqueness (H2 (FCone p2 Q))).
      intro j. exact (snd (Hv j)).
Defined.

End Pairing.

(** ** The exercise itself / ** 练习本身 *)

Section Create.

Context (SC : StrictlyCreatesLimit KA F).
Context (HG : PreservesLimitCone KB G).

Section AtCone.

Context (N : Cone KB).
Context (HN : IsLimitCone N).

Definition fp_image_cone : Cone (F ◯ KA) :=
  cone_transport_inv fp_square_iso (FCone G N).

Definition fp_image_limiting_at : IsLimitCone fp_image_cone :=
  islimitcone_dtransport_inv fp_square_iso (HG N HN).

Definition fp_upstairs_lift : StrictLift KA F fp_image_cone := screates fp_image_cone fp_image_limiting_at.

(*
 Here, and only here, is the bottom functor's strictness spent: the third
 component of a fibre-product object is a Leibniz equality. 

 --------
 在这里，也只有在这里，底函子的严格性才被消耗：纤维积对象的第三个分量是莱布尼茨等式。
*)

Definition fp_lift_apex : P :=
  ((vertex_obj[slift_cone fp_upstairs_lift], vertex_obj[N]); slift_eq fp_upstairs_lift).

Definition fp_lift_leg (j : J) : fp_lift_apex ~{P}~> K j.
Proof using.
  refine ((cone_leg (slift_cone fp_upstairs_lift) j, cone_leg N j); _).
  apply cast_from_rew.
  exact (slift_legs fp_upstairs_lift j).
Defined.

Lemma fp_lift_coh {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ fp_lift_leg x ≈ fp_lift_leg y.
Proof using.
  split.
  - exact (cone_leg_coh (slift_cone fp_upstairs_lift) f).
  - exact (cone_leg_coh N f).
Qed.

Definition fp_lift_cone : Cone K :=
  @Build_Cone J P K fp_lift_apex
    (@Build_ACone J P fp_lift_apex K fp_lift_leg (@fp_lift_coh)).

Definition fp_strict_lift : StrictLift K p2 N :=
  @Build_StrictLift J P B K p2 N fp_lift_cone eq_refl (fun x => reflexivity _).

Definition fp_lift_limiting : IsLimitCone fp_lift_cone :=
  fp_islimitcone fp_lift_cone (screates_limiting fp_image_cone fp_image_limiting_at) HN (HG N HN).

End AtCone.

Definition fp_reflect (Mc : Cone K) (H : IsLimitCone (FCone p2 Mc)) :
  IsLimitCone Mc :=
  fp_islimitcone Mc
    (screates_reflect (FCone p1 Mc)
       (fp_F_image_limiting Mc (HG (FCone p2 Mc) H)))
    H (HG (FCone p2 Mc) H).

Definition fp_snd_StrictlyCreatesLimit : StrictlyCreatesLimit K p2 :=
  {| screates          := fp_strict_lift;
     screates_limiting := fp_lift_limiting;
     screates_reflect  := fp_reflect |}.

Definition fp_snd_CreatesLimit : CreatesLimit K p2 :=
  StrictlyCreatesLimit_CreatesLimit fp_snd_StrictlyCreatesLimit.

End Create.

End Ex3.

(*
 The all-shapes packaging comes in both strengths, and the strict one is
 the same term: [fp_snd_StrictlyCreatesLimit] is already strict at every
 diagram, so quantifying over shapes costs nothing.  An earlier revision
 shipped only [fp_snd_CreatesAllLimits], silently dropping the strictness
 the per-diagram theorem has. 

 --------
 全形状包装有两种强度，而严格版本使用相同的术语：[fp_snd_StrictlyCreatesLimit] 在每个图表上已经是严格的，因此对形状进行量化不花费额外代价。早期版本只发布了 [fp_snd_CreatesAllLimits]，悄悄地放弃了每个图表定理所具有的严格性。
*)

Definition fp_snd_StrictlyCreatesLimits
  {A B C : Category} (F : A ⟶ C) (G : B ⟶ C)
  (SF : StrictlyCreatesLimits F) (HG : ContinuousFunctor G) :
  StrictlyCreatesLimits (FP_snd F G) :=
  fun J K => fp_snd_StrictlyCreatesLimit F G K (SF J _) (HG J _).

Definition fp_snd_CreatesAllLimits
  {A B C : Category} (F : A ⟶ C) (G : B ⟶ C)
  (SF : StrictlyCreatesLimits F) (HG : ContinuousFunctor G) :
  CreatesAllLimits (FP_snd F G) :=
  fun J K => fp_snd_CreatesLimit F G K (SF J _) (HG J _).

(* The issue's Verification block audits this name. / 该问题的验证模块审核此名称。 *)

Definition creation_pullback_stable {A B C : Category} (F : A ⟶ C)
  (G : B ⟶ C) {J : Category} (K : J ⟶ FibreProduct F G)
  (SC : StrictlyCreatesLimit (FP_fst F G ◯ K) F)
  (HG : PreservesLimitCone (FP_snd F G ◯ K) G) :
  StrictlyCreatesLimit K (FP_snd F G) :=
  fp_snd_StrictlyCreatesLimit F G K SC HG.

(* * ** Mac Lane §V.6 Exercise 4: the comma category as the fibre product / * ** 麦克莱恩 §V.6 练习 4：逗号范畴作为纤维积 *)

#[local] Set Transparent Obligations.

Section CommaAsFibreProduct.

Context {C D : Category}.
Context (U : C ⟶ D).
Context (d : D).

Notation FP := (FibreProduct (@Coslice_Proj D d) U).

Program Definition Comma_to_FP : (=(d) ↓ U) ⟶ FP := {|
  fobj := fun x => (((U (snd ``x); `2 x), snd ``x); eq_refl);
  fmap := fun x y f => ((( fmap[U] (snd ``f) ; _), snd ``f); _)
|}.
Next Obligation.
  intros x y f; simpl.
  pose proof (`2 f) as Hf; simpl in Hf.
  rewrite id_right in Hf.
  exact Hf.
Defined.
Next Obligation. intros x y f; simpl; reflexivity. Defined.
Next Obligation.
  intros x y f g [Hf1 Hf2]; simpl in *.
  split; simpl.
  - now rewrite Hf2.
  - exact Hf2.
Qed.
Next Obligation. intros x; simpl; split; simpl; [ apply fmap_id | reflexivity ]. Qed.
Next Obligation.
  intros x y z f g; simpl; split; simpl.
  - apply fmap_comp.
  - reflexivity.
Qed.

Program Definition FP_to_Comma : FP ⟶ (=(d) ↓ U) := {|
  fobj := fun x => ((ttt, snd ``x); id_cast (`2 x) ∘ `2 (fst ``x));
  fmap := fun x y f => ((ttt, snd ``f); _)
|}.
Next Obligation.
  intros x y f; simpl.
  pose proof (`2 (fst ``f)) as Hk; simpl in Hk.
  pose proof (`2 f) as Hc; simpl in Hc.
  rewrite hom_cast_decompose in Hc.
  rewrite id_right.
  exact (cast_transfer _ _ _ _ _ _ Hk Hc).
Defined.
Next Obligation.
  intros x y f g [Hf1 Hf2]; simpl in *.
  split; simpl; [ reflexivity | exact Hf2 ].
Qed.
Next Obligation. intros x; simpl; split; simpl; reflexivity. Qed.
Next Obligation. intros x y z f g; simpl; split; simpl; reflexivity. Qed.

(** ** The two round trips / ** 两次往返 *)

Program Definition FP_round_to (x : FP) :
  Comma_to_FP (FP_to_Comma x) ~{FP}~> x :=
  (((id_cast (eq_sym (`2 x)); _), id); _).
Next Obligation.
  intros x; simpl.
  rewrite comp_assoc, id_cast_inv_l.
  now rewrite id_left.
Defined.
Next Obligation.
  intros x; cbv beta.
  rewrite fmap_id.
  apply cast_unit_cod.
Defined.

Program Definition FP_round_from (x : FP) :
  x ~{FP}~> Comma_to_FP (FP_to_Comma x) :=
  (((id_cast (`2 x); _), id); _).
Next Obligation. intros x; simpl; reflexivity. Defined.
Next Obligation.
  intros x; cbv beta.
  rewrite fmap_id.
  apply cast_unit_dom.
Defined.

Program Definition FP_round_iso (x : FP) :
  Comma_to_FP (FP_to_Comma x) ≅[FP] x := {|
  to := FP_round_to x; from := FP_round_from x
|}.
Next Obligation.
  intros x; split; simpl.
  - apply id_cast_inv_l.
  - apply id_left.
Qed.
Next Obligation.
  intros x; split; simpl.
  - apply id_cast_inv_r.
  - apply id_left.
Qed.

Program Definition FP_round : (Comma_to_FP ◯ FP_to_Comma) ≈ Id[FP] :=
  (FP_round_iso; _).
Next Obligation.
  intros x y f; split; simpl.
  - pose proof (`2 f) as Hf; simpl in Hf.
    rewrite hom_cast_decompose in Hf.
    now symmetry.
  - rewrite id_left; now rewrite id_right.
Qed.

Program Definition Comma_round_to (x : (=(d) ↓ U)) :
  FP_to_Comma (Comma_to_FP x) ~{(=(d) ↓ U)}~> x := ((ttt, id); _).
Next Obligation.
  intros x; cbv beta; simpl.
  rewrite fmap_id; cat.
Defined.

Program Definition Comma_round_from (x : (=(d) ↓ U)) :
  x ~{(=(d) ↓ U)}~> FP_to_Comma (Comma_to_FP x) := ((ttt, id); _).
Next Obligation.
  intros x; cbv beta; simpl.
  rewrite fmap_id; cat.
Defined.

Program Definition Comma_round_iso (x : (=(d) ↓ U)) :
  FP_to_Comma (Comma_to_FP x) ≅[(=(d) ↓ U)] x := {|
  to := Comma_round_to x; from := Comma_round_from x
|}.
Next Obligation. intros x; split; simpl; [ reflexivity | apply id_left ]. Qed.
Next Obligation. intros x; split; simpl; [ reflexivity | apply id_left ]. Qed.

Program Definition Comma_round :
  (FP_to_Comma ◯ Comma_to_FP) ≈ Id[(=(d) ↓ U)] :=
  (Comma_round_iso; _).
Next Obligation.
  intros x y f; split; simpl.
  - reflexivity.
  - rewrite id_left.
    symmetry; apply id_right.
Qed.

(*
 An ISOMORPHISM in [Cat].  Not a pullback in [Cat]: the tree refutes the
 fibre product as a [Cat] pullback at one cospan (the [Indiscrete bool]
 one), and nothing here establishes or refutes it at this cospan.  And
 THIS ROUTE does not yield a pullback in [StrictCat] either, since the
 round trip carries [id ∘ φ] rather than [φ] and so does not transport
 [FibreProduct_IsPullback] across — that is this comparison coming up
 short, not a proof that no comparison works. 

 --------
 在 [Cat] 中的同构。在 [Cat] 中不是一个拉回：该树在一个余锥（[Indiscrete bool]）处否定了纤维积作为 [Cat] 的拉回，并且这里没有任何内容能够在这个余锥上建立或否定它。而且，这条路径在 [StrictCat] 中也不会产生拉回，因为往返会携带 [id ∘ φ] 而不是 [φ]，因此不会跨越 [FibreProduct_IsPullback]——也就是说，这次比较没有成功，而不是证明没有比较可行。
*)

Program Definition Comma_FP_iso : (=(d) ↓ U) ≅[Cat] FP := {|
  to := Comma_to_FP; from := FP_to_Comma
|}.
Next Obligation. exact FP_round. Defined.
Next Obligation. exact Comma_round. Defined.

Definition Comma_FP_Equivalence :
  @EquivalenceOfCategories (=(d) ↓ U) FP Comma_to_FP :=
  Cat_Iso_to_Equivalence Comma_FP_iso.

End CommaAsFibreProduct.

(* * ** Exercise 4: the comma projection creates limits, by that route / * ** 练习 4：逗号投影通过那条路线创建限制 *)

(*
 This reaches the conclusion #438's [comma_CreatesAllLimits] already
 reaches, by a different argument.  It is a CROSS-CHECK, not a
 strengthening — but state the comparison against the right constant.

 Against [comma_CreatesAllLimits] (Construction/Comma/Creation.v) the
 two are of EQUAL strength.  That one takes [PreservesImageLimit], which
 quantifies over every shape just as [ContinuousFunctor U] does — indeed
 the two premises are interderivable by identity functions in that very
 file, [PreservesImageLimit_Continuous] and
 [Continuous_PreservesImageLimit] — and it concludes
 [CreatesAllLimits], which is pointwise [CreatesLimit], not
 [StrictlyCreatesLimit].

 The “weaker in both directions” comparison is true, and is true only, of
 #438's [comma_StrictlyCreatesLimit], which takes the per-diagram
 [PreservesLimitCone (Gdiag K) U] and concludes [StrictlyCreatesLimit].
 An earlier revision of this comment, of the commit message and of the
 docs/INDEX.md bullet made that comparison against
 [comma_CreatesAllLimits], which has neither that premise nor that
 conclusion; measured with [Check], the claim was false in both halves,
 and it under-sold this route while over-stating that constant. 

 --------
 这一结论已经被 #438 的 [comma_CreatesAllLimits] 以不同的论证方式得出。这是一个交叉检查，而不是加强，但要针对正确的常数进行比较。

 与 [comma_CreatesAllLimits]（Construction/Comma/Creation.v）相比，这两个结论的强度相等。那个结论采用了 [PreservesImageLimit]，它对每种形状都进行了量化，就像 [ContinuousFunctor U] 一样——实际上，这两个前提在同一个文件中通过恒等函数 [PreservesImageLimit_Continuous] 和 [Continuous_PreservesImageLimit] 是可以互相推导的——并且它得出 [CreatesAllLimits]，这在每一点上是 [CreatesLimit]，而不是 [StrictlyCreatesLimit]。“在两个方向上都更弱”的比较是正确的，并且仅对#438的[comma_StrictlyCreatesLimit]正确，它采用每个图表的[PreservesLimitCone (Gdiag K) U]并得出[StrictlyCreatesLimit]的结论。 这条评论、提交信息和docs/INDEX.md中之前版本的闪点对[comma_CreatesAllLimits]进行了比较，而[comma_CreatesAllLimits]既没有那个前提也没有那个结论；用[Check]来衡量时，这个说法在两半部分都是错误的，它低估了这条路径，同时夸大了那个常量。
*)

Section Ex4.

Context {C D : Category}.
Context (U : C ⟶ D).
Context (d : D).

Notation FP := (FibreProduct (@Coslice_Proj D d) U).
Notation E  := (Comma_to_FP U d).

Program Definition ex4_functor_iso :
  (FP_snd (@Coslice_Proj D d) U ◯ E) ≈ (@comma_proj2 _1 C D (=(d)) U) :=
  (fun x => iso_id; _).
Next Obligation.
  intros x y f; simpl.
  rewrite id_left; symmetry; apply id_right.
Qed.

Context (HU : ContinuousFunctor U).
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).

Definition ex4_fp_creates :
  StrictlyCreatesLimit (E ◯ K) (FP_snd (@Coslice_Proj D d) U) :=
  fp_snd_StrictlyCreatesLimit (@Coslice_Proj D d) U (E ◯ K)
    (Coslice_Proj_StrictlyCreatesLimit d _)
    (HU _ _).

Definition ex4_composite :
  CreatesLimit K (FP_snd (@Coslice_Proj D d) U ◯ E) :=
  CreatesLimit_compose
    (equivalence_CreatesAllLimits (Comma_FP_Equivalence U d) J K)
    (StrictlyCreatesLimit_CreatesLimit ex4_fp_creates).

Definition comma_proj2_creates_second :
  CreatesLimit K (@comma_proj2 _1 C D (=(d)) U) :=
  CreatesLimit_transport ex4_functor_iso ex4_composite.

End Ex4.

Definition comma_proj2_CreatesAllLimits_via_pullback
  {C D : Category} (U : C ⟶ D) (d : D) (HU : ContinuousFunctor U) :
  CreatesAllLimits (@comma_proj2 _1 C D (=(d)) U) :=
  fun J K => comma_proj2_creates_second U d HU K.

Definition comma_Complete_via_pullback
  {C D : Category} (U : C ⟶ D) (d : D) (HU : ContinuousFunctor U)
  (HC : @Complete C) : @Complete (=(d) ↓ U) :=
  creates_limits_Complete comma_proj2 HC
    (comma_proj2_CreatesAllLimits_via_pullback U d HU).

(* The issue's Verification block audits this name too. / 该问题的验证区块也会审核此名称。 *)

Definition comma_creates_limits_second_proof {C D : Category} (U : C ⟶ D)
  (d : D) (HU : ContinuousFunctor U) {J : Category} (K : J ⟶ (=(d) ↓ U)) :
  CreatesLimit K (@comma_proj2 _1 C D (=(d)) U) :=
  comma_proj2_creates_second U d HU K.

(* * ** The premise of Exercise 4 is inhabited, with nothing assumed / * ** 练习4的前提是可居住的，没有任何假设 *)

(*
 [Id] is its own right adjoint and a right adjoint is continuous, so
 [ContinuousFunctor Id] holds for EVERY category with no hypothesis —
 the same shape as Construction/Slice/Creation.v's
 [Id_PreservesImageLimit].  So the coslice-as-comma reading of Exercise 4
 is an unconditional theorem, and the results above are not vacuous. 

 --------
 [Id] 本身是它自己的右伴随，而右伴随是连续的，所以 [ContinuousFunctor Id] 对于没有假设的每一个范畴都成立——其形状与 Construction/Slice/Creation.v 的 [Id_PreservesImageLimit] 相同。因此，习题 4 中的余切-作为逗号的解读是无条件的定理，上述结果并非空洞。
*)

Definition Id_ContinuousFunctor {C : Category} : ContinuousFunctor (@Id C) :=
  @right_adjoint_Continuous C C Id Id (@adj_id C).

Definition coslice_comma_proj2_creates_via_pullback {C : Category} (c : C)
  {J : Category} (K : J ⟶ (=(c) ↓ Id)) :
  CreatesLimit K (@comma_proj2 _1 C C (=(c)) Id) :=
  comma_proj2_creates_second Id c Id_ContinuousFunctor K.

Definition coslice_comma_Complete_via_pullback {C : Category} (c : C)
  (HC : @Complete C) : @Complete (=(c) ↓ Id) :=
  comma_Complete_via_pullback Id c Id_ContinuousFunctor HC.
