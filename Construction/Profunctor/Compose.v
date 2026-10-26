Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Coend.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Coend.
Require Import Category.Theory.Profunctor.

Generalizable All Variables.

(*
 Discharge every [Program] obligation by hand: the default [cat_simpl] would
 destructure the product-category objects, renaming the variables the proofs
 below refer to. 

 --------
 通过手动履行每一个 [Program] 义务：默认的 [cat_simpl] 会解构产品类别对象，重命名下面证明中提到的变量。
*)
#[local] Obligation Tactic := idtac.

(* * * Composition of profunctors by coends / * * 通过共端的仿函子组合 *)

(*
 nLab:      https://ncatlab.org/nlab/show/profunctor
 Wikipedia: https://en.wikipedia.org/wiki/Profunctor

 Profunctors `P : C ⇸ D` and `Q : D ⇸ E` (Theory/Profunctor.v, i.e. functors
 `C^op ∏ D ⟶ Sets` and `D^op ∏ E ⟶ Sets`) compose by the coend

 (Q ∘ P)(c, e)  :=  ∫^d  P(c, d) × Q(d, e).

 For a fixed pair `(c, e)` the integrand is the bifunctor

 prof_integrand c e : D^op ∏ D ⟶ Sets,   (d', d) ↦ P(c, d) × Q(d', e),

 contravariant in `d'` (through `Q`) and covariant in `d` (through `P`); the
 diagonal `prof_integrand c e (d, d) = P(c, d) × Q(d, e)` is exactly the
 integrand summand, and the coend `SetsCoend (prof_integrand c e)`
 (Instance/Sets/Coend.v) glues those summands along the dinaturality of `P`
 and `Q`. The composite `prof_compose P Q : C ⇸ E` sends `(c, e)` to the coend
 apex; its action on a morphism `(fc, fe)` of `C^op ∏ E` is the unique
 mediator out of the source coend produced by the coend universal property
 `coend_med`/`coend_med_eq` of Structure/Coend.v.

 The integrand is written directly rather than assembled from the product of
 the partial functors `P(c, -)`, `Q(-, e)` and the Sets tensor: the direct
 form makes `fmap[prof_integrand c e]` compute definitionally to the pointwise
 pair map `(p, q) ↦ (fmap[P] (id, ψ) p, fmap[Q] (φ, id) q)`, so every coend
 obligation below reduces to the functoriality of `P` and `Q` with no tower of
 product/tensor combinators to unfold. The setoid product is the categorical
 product of setoids `prod_setoid` (Lib/Datatypes.v), which is precisely the
 carrier of the cartesian tensor of Sets.

 The three functor laws of `prof_compose` are all discharged through the coend
 uniqueness principle `coend_med_eq`: two mediators that agree on every
 injection are equal. Their agreement is read off the mediator computation
 rule `coend_med_inj` together with the fact that the family of “change of
 `(c, e)`” maps `prof_theta` assembles into a natural transformation of
 integrands, whence the dinaturality (cowedge) condition of the transported
 legs follows from the target coend's own cowedge law `coend_cowedge`.

 The unit for this composition is the identity profunctor `prof_id := Hom C`
 (Functor/Hom.v); the unitors and associator up to natural isomorphism live in
 the companion module Construction/Profunctor/Laws.v. Everything here is kept
 Sets-valued and per-pair: no category of all profunctors is formed. 

 --------
 nLab：       https://ncatlab.org/nlab/show/profunctor
 维基百科：  https://en.wikipedia.org/wiki/Profunctor

 仿函子  `P : C ⇸ D`  和  `Q : D ⇸ E`  （Theory/Profunctor.v，即函子
 `C^op ∏ D ⟶ Sets`  和  `D^op ∏ E ⟶ Sets`）通过余端组合

 (Q ∘ P)(c, e)  :=  ∫^d  P(c, d) × Q(d, e)。

 对于固定的对  `(c, e)`，积分式是双函子

 prof_integrand c e : D^op ∏ D ⟶ 集合,   (d', d) ↦ P(c, d) × Q(d', e)，在 `d'`（通过 `Q`）上是逆变的，在 `d`（通过 `P`）上是协变的；对角线 `prof_integrand c e (d, d) = P(c, d) × Q(d, e)` 恰好是被积和子项，而余端 `SetsCoend (prof_integrand c e)`（Instance/Sets/Coend.v）沿着 `P` 和 `Q` 的双自然性将这些子项粘合起来。复合 `prof_compose P Q : C ⇸ E` 将 `(c, e)` 发送到余端顶点；它在 `C^op ∏ E` 的态射 `(fc, fe)` 上的作用是由余端普遍性 `coend_med` / `coend_med_eq`（Structure/Coend.v）产生的源余端的唯一中介。被积函数是直接写出的，而不是由偏函子 `P(c, -)`、`Q(-, e)` 以及集合张量的乘积组装而成：直接形式使得 `fmap [prof_integrand c e]ZZ ` 按定义计算到逐点对映射 `(p, q) ↦ (fmap [P]ZZ  (id, ψ) p, fmap [Q]ZZ  (φ, id) q)`，因此下面的每个余端义务都简化为 `P` 和 `Q` 的函子性，而无需展开乘积/张量组合器的层级。集合同构积是集合同构 `prod_setoid`（Lib/Datatypes.v）的范畴积，它正好是集合笛卡尔张量的载体。`prof_compose` 的三个函子律都通过共端唯一性原理 `coend_med_eq` 得以实现：在每个注入上都一致的两个中介器是相等的。它们的一致性可以通过中介器计算规则 `coend_med_inj` 读取，同时结合“变换 `(c, e)`”映射族 `prof_theta` 组装成被积函数的自然变换，由此被传输腿的二自然性（共楔）条件便从目标共端自身的共楔律 `coend_cowedge` 推出。

 此复合的单位是恒等拟函子 `prof_id := Hom C` (Functor/Hom.v)；单位子和结合子直到自然同构的存在位于伴随模块 Construction/Profunctor/Laws.v 中。此处所有内容均保持取值为集合并按对处理：未构造所有拟函子的范畴。
*)

Section ProfCompose.

Context {C D E : Category}.
Context (P : C ⇸ D).
Context (Q : D ⇸ E).

(*
 Pointwise readings of the functor laws for Sets-valued functors. Every coend
 obligation below reduces to the functoriality of `P` and `Q` at a point, and
 these three lemmas apply those laws under an evaluated setoid map. 

 --------
 集合值函子定律的逐点读法。下面的每一个共端要求都简化为  `P`  和  `Q`  在某一点处的函子性，并且这三个引理在已求值的集合等价映射下应用了这些定律。
*)
Lemma fmap_pt {A : Category} (F : A ⟶ Sets) {x y : A}
  (m m' : x ~{A}~> y) (Hm : m ≈ m') (a : F x) :
  fmap[F] m a ≈ fmap[F] m' a.
Proof. exact (@fmap_respects _ _ F x y m m' Hm a). Qed.

Lemma fmap_id_pt {A : Category} (F : A ⟶ Sets) {x : A} (a : F x) :
  fmap[F] (id[x]) a ≈ a.
Proof. exact (@fmap_id _ _ F x a). Qed.

Lemma fmap_comp_pt {A : Category} (F : A ⟶ Sets) {x y z : A}
  (m2 : y ~{A}~> z) (m1 : x ~{A}~> y) (a : F x) :
  fmap[F] (m2 ∘ m1) a ≈ fmap[F] m2 (fmap[F] m1 a).
Proof. exact (@fmap_comp _ _ F x y z m2 m1 a). Qed.

(* * ** The integrand bifunctor at a fixed pair / * ** 在固定对上的被积双函子 *)

(*
 `prof_integrand c e : D^op ∏ D ⟶ Sets`, `(d', d) ↦ P(c, d) × Q(d', e)`. The
 action on `(φ, ψ) : (d1', d1) ~> (d2', d2)` post-composes with `Q(φ, e)` on
 the contravariant factor and with `P(c, ψ)` on the covariant factor. 

 --------
 `prof_integrand c e : D^op ∏ D ⟶ Sets`，`(d', d) ↦ P(c, d) × Q(d', e)`。`(φ, ψ) : (d1', d1) ~> (d2', d2)`上的动作在逆变因子上与`Q(φ, e)`后合成，在协变因子上与`P(c, ψ)`后合成。
*)
Program Definition prof_integrand (c : C) (e : E) : (D^op ∏ D) ⟶ Sets := {|
  fobj := fun p =>
    {| carrier   := carrier (P (c, snd p)) * carrier (Q (fst p, e))
     ; is_setoid := prod_setoid |};
  fmap := fun x y f =>
    {| morphism := fun pq =>
         (@fmap (C^op ∏ D) Sets P (c, snd x) (c, snd y) (id, snd f) (fst pq),
          @fmap (D^op ∏ E) Sets Q (fst x, e) (fst y, e) (fst f, id) (snd pq)) |}
|}.
Next Obligation.
  intros c e x y f [a1 b1] [a2 b2] [Ha Hb]; split; simpl in *.
  - now rewrite Ha.
  - now rewrite Hb.
Qed.
Next Obligation.
  intros c e x y f g [Hf Hg] [a b]; split; simpl in *.
  - apply (fmap_pt P); split; [ reflexivity | exact Hg ].
  - apply (fmap_pt Q); split; [ exact Hf | reflexivity ].
Qed.
Next Obligation.
  intros c e x [a b]; split; simpl in *.
  - exact (fmap_id_pt P a).
  - exact (fmap_id_pt Q b).
Qed.
Next Obligation.
  intros c e x y z f g [a b]; split; simpl in *.
  - rewrite <- (fmap_comp_pt P (x:=(c, snd x)) (y:=(c, snd y)) (z:=(c, snd z))
                 (id, snd f) (id, snd g) a).
    apply (fmap_pt P); split; simpl; cat.
  - rewrite <- (fmap_comp_pt Q (x:=(fst x, e)) (y:=(fst y, e)) (z:=(fst z, e))
                 (fst f, id) (fst g, id) b).
    apply (fmap_pt Q); split; simpl; cat.
Qed.

(*
   * ** Change of the fixed pair as a natural transformation of integrands 

   --------
   * ** 固定对作为被积函数的自然变换的改变
*)

(*
 The component map at `(d', d)` sending `P(c1, d) × Q(d', e1)` to
 `P(c2, d) × Q(d', e2)` by acting with `P(fc, -)` and `Q(-, fe)`. 

 --------
 在 `(d', d)` 的组件映射将 `P(c1, d) × Q(d', e1)` 通过作用 `P(fc, -)` 和 `Q(-, fe)` 映射到 `P(c2, d) × Q(d', e2)`。
*)
Program Definition prof_theta_map (c1 c2 : C) (e1 e2 : E)
  (fc : c1 ~{C^op}~> c2) (fe : e1 ~{E}~> e2) (de : D^op ∏ D)
  : prof_integrand c1 e1 de ~{Sets}~> prof_integrand c2 e2 de := {|
  morphism := fun pq =>
    (@fmap (C^op ∏ D) Sets P (c1, snd de) (c2, snd de) (fc, id) (fst pq),
     @fmap (D^op ∏ E) Sets Q (fst de, e1) (fst de, e2) (id, fe) (snd pq)) |}.
Next Obligation.
  intros c1 c2 e1 e2 fc fe de [a1 b1] [a2 b2] [Ha Hb]; split; simpl in *.
  - now rewrite Ha.
  - now rewrite Hb.
Qed.

(*
 Naturality of `prof_theta_map` in `(d', d)`: acting with `P(fc, -)`,
 `Q(-, fe)` commutes with the integrand action, by the interchange law
 (`fmap_comp`) of `P` and `Q`. 

 --------
 `prof_theta_map` 在 `(d', d)` 中的自然性：与 `P(fc, -)` 一起作用，`Q(-, fe)` 与被积函数作用交换，依据 `P` 和 `Q` 的互换律（`fmap_comp`）。
*)
Lemma prof_theta_natural (c1 c2 : C) (e1 e2 : E)
  (fc : c1 ~{C^op}~> c2) (fe : e1 ~{E}~> e2) :
  ∀ (x y : D^op ∏ D) (m : x ~{D^op ∏ D}~> y),
    fmap[prof_integrand c2 e2] m ∘ prof_theta_map c1 c2 e1 e2 fc fe x
      ≈ prof_theta_map c1 c2 e1 e2 fc fe y ∘ fmap[prof_integrand c1 e1] m.
Proof.
  intros x y m [p q]; split; simpl.
  - rewrite <- (fmap_comp_pt P (x:=(c1, snd x)) (y:=(c2, snd x)) (z:=(c2, snd y))
                 (id, snd m) (fc, id) p).
    rewrite <- (fmap_comp_pt P (x:=(c1, snd x)) (y:=(c1, snd y)) (z:=(c2, snd y))
                 (fc, id) (id, snd m) p).
    apply (fmap_pt P); split; simpl; cat.
  - rewrite <- (fmap_comp_pt Q (x:=(fst x, e1)) (y:=(fst x, e2)) (z:=(fst y, e2))
                 (fst m, id) (id, fe) q).
    rewrite <- (fmap_comp_pt Q (x:=(fst x, e1)) (y:=(fst y, e1)) (z:=(fst y, e2))
                 (id, fe) (fst m, id) q).
    apply (fmap_pt Q); split; simpl; cat.
Qed.

Definition prof_theta (c1 c2 : C) (e1 e2 : E)
  (fc : c1 ~{C^op}~> c2) (fe : e1 ~{E}~> e2)
  : prof_integrand c1 e1 ⟹ prof_integrand c2 e2 :=
  Build_Transform' (prof_theta_map c1 c2 e1 e2 fc fe)
                   (prof_theta_natural c1 c2 e1 e2 fc fe).

(* * ** Diagonal composition laws of `prof_theta` / * ** `prof_theta` 的对角组合律 *)

(*
 On the diagonal `prof_theta` for the identity morphism is the identity. 

 --------
 在对角线 `prof_theta` 上，对于恒等态射是恒等的。
*)
Lemma prof_theta_id (c : C) (e : E) (d : D) :
  transform[prof_theta c c e e id id] (d, d) ≈ id.
Proof.
  intros [p q]; split; simpl.
  - exact (fmap_id_pt P p).
  - exact (fmap_id_pt Q q).
Qed.

(*
 On the diagonal `prof_theta` sends a composite to the composite. 

 --------
 在对角线上，`prof_theta` 将复合数发送到复合数。
*)
Lemma prof_theta_comp (c1 c2 c3 : C) (e1 e2 e3 : E)
  (fc1 : c1 ~{C^op}~> c2) (fc2 : c2 ~{C^op}~> c3)
  (fe1 : e1 ~{E}~> e2) (fe2 : e2 ~{E}~> e3) (d : D) :
  transform[prof_theta c2 c3 e2 e3 fc2 fe2] (d, d)
    ∘ transform[prof_theta c1 c2 e1 e2 fc1 fe1] (d, d)
  ≈ transform[prof_theta c1 c3 e1 e3 (fc2 ∘ fc1) (fe2 ∘ fe1)] (d, d).
Proof.
  intros [p q]; split; simpl.
  - rewrite <- (fmap_comp_pt P (x:=(c1, d)) (y:=(c2, d)) (z:=(c3, d))
                 (fc2, id) (fc1, id) p).
    apply (fmap_pt P); split; simpl; cat.
  - rewrite <- (fmap_comp_pt Q (x:=(d, e1)) (y:=(d, e2)) (z:=(d, e3))
                 (id, fe2) (id, fe1) q).
    apply (fmap_pt Q); split; simpl; cat.
Qed.

(*
 On the diagonal `prof_theta` respects equivalence of the pair morphism. 

 --------
 在对角线上 `prof_theta` 尊重对偶态射的等价性。
*)
Lemma prof_theta_respects (c1 c2 : C) (e1 e2 : E)
  (fc fc' : c1 ~{C^op}~> c2) (fe fe' : e1 ~{E}~> e2) (d : D) :
  fc ≈ fc' -> fe ≈ fe' ->
  transform[prof_theta c1 c2 e1 e2 fc fe] (d, d)
    ≈ transform[prof_theta c1 c2 e1 e2 fc' fe'] (d, d).
Proof.
  intros Hc He [p q]; split; simpl.
  - apply (fmap_pt P); split; [ exact Hc | reflexivity ].
  - apply (fmap_pt Q); split; [ reflexivity | exact He ].
Qed.

(*
   * ** The dinaturality (cowedge) condition of the transported legs 

   --------
   * ** 搬运腿的二自然性（cowedge）条件
*)

(*
 The legs `coend_inj ∘ prof_theta (d, d)` into the target coend form a cowedge
 over the source integrand. This is naturality of `prof_theta` composed with
 the target coend's own cowedge condition. 

 --------
 腿 `coend_inj ∘ prof_theta (d, d)` 在目标共端中形成一个在源积分上方的共楔。这是 `prof_theta` 与目标共端自身共楔条件组合的自然性。
*)
Lemma prof_leg_cowedge (c1 c2 : C) (e1 e2 : E)
  (fc : c1 ~{C^op}~> c2) (fe : e1 ~{E}~> e2) :
  Cowedge_cond (prof_integrand c1 e1)
    (coend_obj (SetsCoend (prof_integrand c2 e2)))
    (fun d => coend_inj (SetsCoend (prof_integrand c2 e2))
              ∘ transform[prof_theta c1 c2 e1 e2 fc fe] (d, d)).
Proof.
  intros x y g.
  pose proof (coend_cowedge (SetsCoend (prof_integrand c2 e2)) g) as Hcw.
  unfold bimap in *.
  rewrite <- comp_assoc.
  rewrite (naturality_sym (prof_theta c1 c2 e1 e2 fc fe) (y, x) (x, x) (op g, id)).
  rewrite comp_assoc.
  rewrite Hcw.
  symmetry.
  rewrite <- comp_assoc.
  rewrite (naturality_sym (prof_theta c1 c2 e1 e2 fc fe) (y, x) (y, y) (id, g)).
  rewrite comp_assoc.
  reflexivity.
Qed.

(*
   * ** The mediator: the action of `prof_compose` on morphisms 

   --------
   * ** 调解者：`prof_compose` 对态射的作用
*)

Definition prof_compose_map (c1 c2 : C) (e1 e2 : E)
  (fc : c1 ~{C^op}~> c2) (fe : e1 ~{E}~> e2)
  : coend_obj (SetsCoend (prof_integrand c1 e1))
    ~{Sets}~> coend_obj (SetsCoend (prof_integrand c2 e2)) :=
  coend_med (SetsCoend (prof_integrand c1 e1))
            (coend_obj (SetsCoend (prof_integrand c2 e2)))
            (fun d => coend_inj (SetsCoend (prof_integrand c2 e2))
                      ∘ transform[prof_theta c1 c2 e1 e2 fc fe] (d, d))
            (prof_leg_cowedge c1 c2 e1 e2 fc fe).

(*
 The mediator computation rule: it recovers each transported leg. 

 --------
 中介计算规则：它恢复每个运输环节。
*)
Lemma prof_compose_map_inj (c1 c2 : C) (e1 e2 : E)
  (fc : c1 ~{C^op}~> c2) (fe : e1 ~{E}~> e2) (d : D) :
  prof_compose_map c1 c2 e1 e2 fc fe ∘ coend_inj (SetsCoend (prof_integrand c1 e1))
    ≈ coend_inj (SetsCoend (prof_integrand c2 e2))
      ∘ transform[prof_theta c1 c2 e1 e2 fc fe] (d, d).
Proof.
  exact (coend_med_inj (SetsCoend (prof_integrand c1 e1))
           (coend_obj (SetsCoend (prof_integrand c2 e2)))
           (fun d => coend_inj (SetsCoend (prof_integrand c2 e2))
                     ∘ transform[prof_theta c1 c2 e1 e2 fc fe] (d, d))
           (prof_leg_cowedge c1 c2 e1 e2 fc fe) d).
Qed.

(** ** The composite profunctor / ** 复合概函 *)

Program Definition prof_compose : C ⇸ E := {|
  fobj := fun ce => coend_obj (SetsCoend (prof_integrand (fst ce) (snd ce)));
  fmap := fun x y f =>
    prof_compose_map (fst x) (fst y) (snd x) (snd y) (fst f) (snd f)
|}.
Next Obligation.
  (*
 fmap_respects: two mediators agreeing on all injections are equal. 

 --------
 fmap_respects：两个调解者在所有注入上达成一致则相等。
*)
  intros x y f g H.
  apply (coend_med_eq (SetsCoend (prof_integrand (fst x) (snd x)))
           (coend_obj (SetsCoend (prof_integrand (fst y) (snd y))))
           (fun d => coend_inj (SetsCoend (prof_integrand (fst y) (snd y)))
                     ∘ transform[prof_theta (fst x) (fst y) (snd x) (snd y)
                                   (fst g) (snd g)] (d, d))
           (prof_leg_cowedge (fst x) (fst y) (snd x) (snd y) (fst g) (snd g))).
  - intro d.
    transitivity (coend_inj (SetsCoend (prof_integrand (fst y) (snd y)))
                  ∘ transform[prof_theta (fst x) (fst y) (snd x) (snd y)
                                (fst f) (snd f)] (d, d)).
    + exact (prof_compose_map_inj (fst x) (fst y) (snd x) (snd y)
               (fst f) (snd f) d).
    + rewrite (prof_theta_respects (fst x) (fst y) (snd x) (snd y)
                 (fst f) (fst g) (snd f) (snd g) d (fst H) (snd H)).
      reflexivity.
  - intro d.
    exact (prof_compose_map_inj (fst x) (fst y) (snd x) (snd y)
             (fst g) (snd g) d).
Qed.
Next Obligation.
  (* fmap_id: the mediator of the identity legs is the identity. / fmap_id：身份边的中介是身份。 *)
  intros [c e].
  apply (coend_med_eq (SetsCoend (prof_integrand c e))
           (coend_obj (SetsCoend (prof_integrand c e)))
           (fun d => coend_inj (SetsCoend (prof_integrand c e))
                     ∘ transform[prof_theta c c e e id id] (d, d))
           (prof_leg_cowedge c c e e id id)).
  - intro d.
    exact (prof_compose_map_inj c c e e id id d).
  - intro d.
    rewrite id_left.
    rewrite (prof_theta_id c e d).
    rewrite id_right.
    reflexivity.
Qed.
Next Obligation.
  (*
 fmap_comp: the mediator of a composite equals the composite of mediators. 

 --------
 fmap_comp：复合的中介等于中介的复合。
*)
  intros x y z f g.
  apply (coend_med_eq (SetsCoend (prof_integrand (fst x) (snd x)))
           (coend_obj (SetsCoend (prof_integrand (fst z) (snd z))))
           (fun d => coend_inj (SetsCoend (prof_integrand (fst z) (snd z)))
                     ∘ transform[prof_theta (fst x) (fst z) (snd x) (snd z)
                                   (fst f ∘ fst g) (snd f ∘ snd g)] (d, d))
           (prof_leg_cowedge (fst x) (fst z) (snd x) (snd z)
              (fst f ∘ fst g) (snd f ∘ snd g))).
  - intro d.
    exact (prof_compose_map_inj (fst x) (fst z) (snd x) (snd z)
             (fst f ∘ fst g) (snd f ∘ snd g) d).
  - intro d.
    rewrite <- comp_assoc.
    rewrite (prof_compose_map_inj (fst x) (fst y) (snd x) (snd y)
               (fst g) (snd g) d).
    rewrite comp_assoc.
    rewrite (prof_compose_map_inj (fst y) (fst z) (snd y) (snd z)
               (fst f) (snd f) d).
    rewrite <- comp_assoc.
    rewrite (prof_theta_comp (fst x) (fst y) (fst z) (snd x) (snd y) (snd z)
               (fst g) (fst f) (snd g) (snd f) d).
    reflexivity.
Qed.

End ProfCompose.

(** ** The identity profunctor / ** 恒等泛函子 *)

(*
 The unit for profunctor composition is the hom-bifunctor `Hom C`, viewed as a
 profunctor `C ⇸ C` (Functor/Hom.v, Theory/Profunctor.v). 

 --------
 Profunctor 组合的单位是同态双函子 `Hom C`，视为一个 profunctor `C ⇸ C`（Functor/Hom.v，Theory/Profunctor.v）。
*)
Definition prof_id {C : Category} : C ⇸ C := Hom C.
