Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Strong.
Require Import Category.Functor.Construction.Product.
Require Import Category.Structure.Monoidal.Product.
Require Import Category.Structure.Monoidal.Heunen_Vicary.

Generalizable All Variables.

(** The product of strong functors is strong  / 强函子的乘积是强的*)

(*
nLab: https://ncatlab.org/nlab/show/tensorial+strength
   Wikipedia: https://en.wikipedia.org/wiki/Strong_monad

   If F, G : C ⟶ C are strong (each carries a left tensorial strength
   strength[x,y] : x ⨂ F y ~> F (x ⨂ y), see Functor/Strong.v), then their
   componentwise product F ∏⟶ G : C ∏ C ⟶ C ∏ C is strong for the product
   monoidal structure on C ∏ C (Structure/Monoidal/Product.v), where the
   tensor and unit act factorwise. The strength of F ∏⟶ G at a pair of objects
   is built componentwise from the two given strengths,

     strength[(x₁,x₂),(y₁,y₂)] = (strength[F]_{x₁,y₁}, strength[G]_{x₂,y₂}),

   and naturality together with both coherence laws (unit law w.r.t. λ and
   associativity law w.r.t. α) hold in C ∏ C because equivalence there is the
   componentwise conjunction, so each obligation splits into the F-part and the
   G-part and is discharged factorwise. This needs only that C be monoidal; the
   cartesian structure is not used. ProductFunctor_Strong_proj1/proj2 are the
   converse projections, recovering a strength on each factor from a strength on
   F ∏⟶ G by fixing the other coordinate at the unit I. 

--------
nLab：https://ncatlab.org/nlab/show/tensorial+strength
 维基百科：https://en.wikipedia.org/wiki/Strong_monad

如果 F, G : C ⟶ C 很强（每个都带有左张量强度
 Strength[x,y] : x ⨂ F y ~> F (x ⨂ y)，参见 Functor/Strong.v)，然后它们
 分量乘积 F ∏⟶ G : C ∏ C ⟶ C ∏ C 对于乘积来说是强的
 C ∏ C 上的幺半群结构 (Structure/Monoidal/Product.v)，其中
 张量和单位按因子起作用。 一对物体处 F ∏⟶ G 的强度
 由两个给定的强度组成，

强度[(x₁,x₂),(y₁,y₂)] = (强度[F]_{x₁,y₁}, 强度[G]_{x2,y2}),

和自然性以及相干律（单位律 w.r.t. λ 和
 结合律 α) 在 C ∏ C 中成立，因为等价于
 成分连接，因此每个义务分为 F 部分和
 G 部分并按因子排出。 这仅需要 C 是幺半群的； 的
 不使用笛卡尔结构。 ProductFunctor_Strong_proj1/proj2 是
 逆向预测，从某个因素的强度恢复每个因素的强度
 F ∏⟶ G 通过将另一个坐标固定在单位 I 上。 
*)

Section ProductFunctorStrong.

Context `{@Monoidal C}.
Context {F : C ⟶ C}.
Context {G : C ⟶ C}.

Program Definition ProductFunctor_Strong
  `{!StrongFunctor F} `{!StrongFunctor G} : StrongFunctor (F ∏⟶ G) := {|
  strength := fun _ _ => (strength[F], strength[G]);  (* componentwise strength *)
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation. split; apply strength_natural. Qed.   (* naturality, each factor  / 自然性，每个因素*)
Next Obligation. split; apply strength_id_left. Qed.   (* unit law, each factor  / 单位律，每个因子*)
Next Obligation. split; apply strength_assoc. Qed.     (* assoc law, each factor  / 关联法则，每个因素*)

(*
Recover a strength on the first factor F from one on F ∏⟶ G: fix the second
   coordinate at the unit I and project the first component. The unit and assoc
   laws follow by transporting the product strength's naturality along the unit
   isomorphism I ≅ I ⨂ I before invoking the corresponding product law. 

--------
从 F ∏⟶ G 上恢复第一个因子 F 上的强度：修复第二个因子
 在单元 I 处进行坐标并投影第一个分量。 单位及关联单位
 通过沿着单元传输产品强度的自然性来遵循法律
 同构 I ≅ I ⨂ I 在调用相应的乘积定律之前。 
*)
Program Definition ProductFunctor_Strong_proj1 :
  StrongFunctor (F ∏⟶ G) → StrongFunctor F := fun P => {|
  strength := fun x y => fst (@strength _ _ _ P (x, I) (y, I));  (* fst at y₂ = I *)
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation.
  exact (fst (@strength_natural _ _ _ P (x, I) (y, I) (g, id)
                                (z, I) (w, I) (h, id))).
Defined.
Next Obligation.
  exact (fst (@strength_id_left _ _ _ P (x, I))).
Qed.
Next Obligation.
  pose proof (@unit_left C _ I) as X0.
  pose proof (fst (@strength_natural _ _ _ P
                     (x, I) (x, I) (id[x], id[I])
                     (y ⨂ z, I)%object (y ⨂ z, I ⨂ I)%object
                     (id[y ⨂ z], from X0))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrites.
  pose proof (fst (@strength_natural _ _ _ P
                     (x ⨂ y, I)%object (x ⨂ y, I ⨂ I)%object
                     (id[x ⨂ y], from X0)
                     (z, I) (z, I) (id[z], id[I]))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrites.
  exact (fst (@strength_assoc _ _ _ P (x, I) (y, I) (z, I))).
Qed.

(*
Dual of proj1: recover a strength on the second factor G by fixing the first
   coordinate at the unit I and projecting the second component. 

--------
proj1 的对偶：通过修复第一个因素来恢复第二个因素 G 的强度
 坐标在单元 I 并投影第二个分量。 
*)
Program Definition ProductFunctor_Strong_proj2 :
  StrongFunctor (F ∏⟶ G) → StrongFunctor G := fun P => {|
  strength := fun x y => snd (@strength _ _ _ P (I, x) (I, y));  (* snd at x₁ = I *)
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation.
  exact (snd (@strength_natural _ _ _ P (I, x) (I, y) (id, g)
                                (I, z) (I, w) (id, h))).
Defined.
Next Obligation.
  exact (snd (@strength_id_left _ _ _ P (I, x))).
Qed.
Next Obligation.
  pose proof (@unit_left C _ I) as X0.
  pose proof (snd (@strength_natural _ _ _ P
                     (I, x) (I, x) (id[I], id[x])
                     (I, y ⨂ z)%object (I ⨂ I, y ⨂ z)%object
                     (from X0, id[y ⨂ z]))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrites.
  pose proof (snd (@strength_natural _ _ _ P
                     (I, x ⨂ y)%object (I ⨂ I, x ⨂ y)%object
                     (from X0, id[x ⨂ y])
                     (I, z) (I, z) (id[I], id[z]))) as X1.
  simpl in X1.
  rewrite bimap_id_id in X1.
  rewrite !fmap_id in X1.
  rewrite id_left in X1.
  rewrite bimap_id_id in X1.
  rewrite id_left, !id_right in X1.
  rewrites.
  exact (snd (@strength_assoc _ _ _ P (I, x) (I, y) (I, z))).
Qed.

End ProductFunctorStrong.
