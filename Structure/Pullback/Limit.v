Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Span.
Require Import Category.Structure.Pullback.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Roof.

Generalizable All Variables.

(*
 This file connects the universal-property definition of a pullback (see
 [Structure/Pullback.v]) with the general theory of limits (see
 [Structure/Limit.v]), realizing the standard fact that a pullback is the
 limit of a cospan diagram.

 nLab:      https://ncatlab.org/nlab/show/pullback
 Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)
 https://ncatlab.org/nlab/show/limit

 A cospan in C is a functor [F : Roof^op ⟶ C] (see [Structure/Span.v]). Since
 the non-identity arrows of [Roof] are [ZeroNeg : RZero ~> RNeg] and
 [ZeroPos : RZero ~> RPos], in [Roof^op] they flip to [ZeroNeg : RNeg ~> RZero]
 and [ZeroPos : RPos ~> RZero], so [F] picks out the cospan

 F RNeg --(fmap ZeroNeg)--> F RZero <--(fmap ZeroPos)-- F RPos

 i.e. a diagram of shape `b → a ← c` with a = F RZero, b = F RNeg,
 c = F RPos. (The [unop] coercions below merely re-read these C-morphisms
 through the [op]/[unop] discipline; they leave the underlying arrow
 unchanged, as [unop f := f].)

 The pullback ↔ limit-of-cospan correspondence, in this library's notation:

 - a [Cone F] over the cospan is an apex with legs ψ_RNeg, ψ_RZero, ψ_RPos
 satisfying cone coherence; coherence at ZeroNeg/ZeroPos forces the
 commuting square fmap[F] ZeroNeg ∘ ψ_RNeg ≈ ψ_RZero ≈
 fmap[F] ZeroPos ∘ ψ_RPos (the diagonal ψ_RZero being determined);

 - the limit's legs over the apex are exactly the pullback projections:
 vertex_map RNeg = pullback_fst and vertex_map RPos = pullback_snd;

 - the limit's universal property (every cone factors through a unique
 mediating morphism) is exactly the pullback's [ump_pullbacks].

 [Pullback_to_Universal] and [Pullback_from_Universal] below make this
 correspondence explicit in both directions. 

 --------
 此文件将拉回的通用性质定义（见 [Structure/Pullback.v]）与极限的一般理论（见 [Structure/Limit.v]）联系起来，实现了拉回是余叉图极限的标准事实。

 nLab: https://ncatlab.org/nlab/show/pullback
 Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)
 https://ncatlab.org/nlab/show/limit

 C 中的余叉是一个函子 [F : Roof^op ⟶ C]（见 [Structure/Span.v]）。由于 [Roof] 的非同一箭头是 [ZeroNeg : RZero ~> RNeg] 和 [ZeroPos : RZero ~> RPos]，在 [Roof^op] 中它们翻转为 [ZeroNeg : RNeg ~> RZero] 和 [ZeroPos : RPos ~> RZero]，因此 [F] 选出余叉

 F RNeg --(fmap ZeroNeg)--> F RZero <--(fmap ZeroPos)-- F RPos即形状 `b → a ← c` 的图，其中 a = F RZero，b = F RNeg，c = F RPos。（下面的 [unop] 强制转换仅重新通过 [op] / [unop] 规范读取这些 C-态射；它们保持底层箭头不变，如 [unop f := f] 所示。）

 在此库的符号中，拉回 ↔ 共跨极限的对应关系：

 - a [Cone F] 在共跨上是一个顶点，并带有腿 ψ_RNeg、ψ_RZero、ψ_RPos，满足圆锥一致性；在 ZeroNeg/ZeroPos 的一致性强制了交换方阵 fmap [F] ZeroNeg ∘ ψ_RNeg ≈ ψ_RZero ≈ fmap [F] ZeroPos ∘ ψ_RPos（对角线 ψ_RZero 被确定）；

 - 极限在顶点上的边正是拉回投影：vertex_map RNeg = pullback_fst 以及 vertex_map RPos = pullback_snd；- 极限的泛性质（每一个锥都通过唯一的中介态射分解）正是拉回的  [ump_pullbacks] 。

 下面的 [Pullback_to_Universal] 和 [Pullback_from_Universal] 使这种对应在两个方向上都显式化。
*)

(* A pullback of a cospan F is just the limit of F. This is a definitional alias introduced to name the cospan-limit and to read its legs/UMP as pullback data in the lemmas below. / 余积范围 F 的拉回只是 F 的极限。这是一个定义上的别名，用于命名余积极限，并在下面的引理中将其两条腿/通用性质（UMP）作为拉回数据来读取。 *)
Definition Pullback_Limit {C : Category} (F : Cospan C) := Limit F.
Arguments Pullback_Limit {_%_category} F%_functor /.

(*
 Dually, a pushout of a span F is the colimit of F (a limit of F^op, see
 [Structure/Limit.v]). Named [Pushout_Limit] to parallel [Pullback_Limit];
 it is a colimit, not a limit. 

 --------
 同样地，跨度 F 的推出是 F 的余极限（F^op 的极限，参见 [Structure/Limit.v]）。命名为 [Pushout_Limit]，以平行 [Pullback_Limit]；它是余极限，而不是极限。
*)
Definition Pushout_Limit {C : Category} (F : Span C) := Colimit F.
Arguments Pushout_Limit {_%_category} F%_functor /.

(*
 From the limit of a cospan, recover the universal-property pullback: the
 pullback object is the limit apex, and the two projections are the limit
 legs at RNeg and RPos. The square commutes by cone coherence, and the
 pullback UMP is the limit UMP applied to the cone built from a competing
 square (Q, q1, q2). 

 --------
 从余跨度的极限，恢复普适性质的拉回：拉回对象是极限顶点，两个投影是 RNeg 和 RPos 的极限边。由于圆锥的一致性，方形图交换，并且拉回的普适性质是应用于由竞争方形图 (Q, q1, q2) 构建的圆锥的极限普适性质。
*)
Program Definition Pullback_to_Universal {C : Category}
        (F : Cospan C) (P : Pullback_Limit F) :
  Pullback (unop (fmap[F] ZeroNeg)) (unop (fmap[F] ZeroPos)) := {|
  Pull := P;
  pullback_fst := (vertex_map _);   (* leg at RNeg / 右膝腿 *)
  pullback_snd := (vertex_map _)    (* leg at RPos / 右侧位置的腿 *)
|}.
Next Obligation.
  unfold unop.
  now rewrite 2 cone_coherence.
Qed.
Next Obligation.
  given (cone : Cone F). {
    unshelve (refine {| vertex_obj := Q |}); unshelve econstructor; intros.
    - destruct x; auto.
      exact (unop (fmap[F] ZeroPos) ∘ q2).
    - simpl;
      destruct x, y; auto with roof_laws; simpl in f;
      rewrite (RoofHom_inv _ _ f); cat.
  }
  destruct P, limit_cone; simpl in *.
  exists (unique_obj (ump_limits cone)). {
    split;
    [ pose proof (unique_property (ump_limits cone) RNeg)
    | pose proof (unique_property (ump_limits cone) RPos) ];
    unfold cone in *; simpl in *; clear cone;
    rewrites; reflexivity.
  }
  intros.
  apply (uniqueness (ump_limits cone)); intros.
  simpl in *.
  destruct x, X0; simpl; auto.
  rewrites.
  rewrite comp_assoc.
  unfold unop.
  rewrite cone_coherence.
  reflexivity.
Qed.

(*
 Conversely, a universal-property pullback of f and g yields the limit of the
 corresponding cospan. The cospan is presented as [(ASpan f g in C^op)^op]:
 a span `z ← · → z` of f, g in C^op is a cospan `· → z ← ·` in C, with
 F RNeg = x, F RZero = z, F RPos = y. The limit cone has apex [Pull P], legs
 pullback_fst at RNeg, pullback_snd at RPos, and the diagonal f ∘ pullback_fst
 at RZero; its universal property is exactly [ump_pullbacks]. 

 --------
 相反，f 和 g 的一个通用性质的拉回给出了相应余锥的极限。余锥表示为 [(ASpan f g in C^op)^op]：C^op 中 f、g 的一个跨度 `z ← · → z` 是 C 中的一个余锥 `· → z ← ·`，且 F RNeg = x，F RZero = z，F RPos = y。极限锥的顶点为 [Pull P]，腿分别为 RNeg 处的 pullback_fst，RPos 处的 pullback_snd，以及 RZero 处的对角线 f ∘ pullback_fst；它的通用性质正是 [ump_pullbacks]。
*)
Program Definition Pullback_from_Universal {C : Category}
        {x y z : C} (f : x ~> z) (g : y ~> z) (P : Pullback f g) :
  Pullback_Limit (@ASpan (C^op) _ _ _ f g)^op := {|
  limit_cone := {| vertex_obj := P ; coneFrom := {| vertex_map := _; cone_coherence := _ |} |}
|}.
Next Obligation.
  destruct x0;
    destruct P; simpl in *; auto.
  exact (f ∘ pullback_fst).
Defined.
Next Obligation.
  destruct x0, y0;
  destruct P; simpl in *; auto with roof_laws; cat.
Qed.
Next Obligation.
  destruct P, N, coneFrom; simpl in *.
  assert (eqv : f ∘ (vertex_map RNeg) ≈
                  g ∘ (vertex_map RPos)). {
    rewrite (cone_coherence RNeg RZero ZeroNeg).
    rewrite (cone_coherence RPos RZero ZeroPos).
    reflexivity.
  }
  unfold Pullback_from_Universal_obligation_1; simpl.
  destruct (ump_pullbacks vertex_obj (vertex_map RNeg) (vertex_map RPos) eqv).
  construct; simplify; auto.
  - destruct x0; auto.
    rewrite <- comp_assoc.
    rewrite unique_property.
    apply (cone_coherence RNeg RZero ZeroNeg).
  - apply uniqueness.
    split.
    + apply (X RNeg).
    + apply (X RPos).
Defined.
