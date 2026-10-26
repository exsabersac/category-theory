Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/funny+tensor+product
 Mark Weber, “Free products of higher operad algebras”, TAC 28:2 (2013), §2.

 The internal hom [⟦B, E⟧] of the funny tensor product on Cat: its objects
 are functors [B ⟶ E], but its morphisms [F ~> G] are UNNATURAL (or “mere”)
 transformations — families [τ : ∀ b, F b ~{E}~> G b] of E-morphisms
 subject to NO naturality condition.  Weber §2: “These components φ_a are
 not required to satisfy the usual naturality condition.”  By the theorem
 of Foltz, Kelly and Lair (1980) there are, up to isomorphism, exactly two
 biclosed monoidal structures on Cat: the cartesian one, whose internal hom
 [Instance/Fun.v] takes natural transformations, and the funny one, whose
 internal hom is this category.

 Structurally this is [Theory/Natural/Transformation.v] minus [naturality]
 and [naturality_sym]: identities and composition are componentwise, the
 hom-setoid is componentwise [≈] in E, and every category law holds
 componentwise, inherited from E.  No [_sym] companion field is needed
 here: with the naturality square gone, no remaining law has a dual
 orientation beyond the category laws themselves, which already come in
 [comp_assoc]/[comp_assoc_sym] pairs. 

 --------
 nLab:  https://ncatlab.org/nlab/show/funny+tensor+product
 Mark Weber, 《高阶运算代数的自由积》, TAC 28:2 (2013), §2.

 在 Cat 上有趣的张量积的内部 Hom: 它的对象是函子 [B ⟶ E]，但它的态射 [F ~> G] 是不自然的（或“普通的”）变换——E-态射族 [τ : ∀ b, F b ~{E}~> G b]，没有任何自然性条件。Weber §2: “这些分量 φ_a 不要求满足通常的自然性条件。”根据 Foltz、Kelly 和 Lair (1980) 的定理，在 Cat 上最多同构存在恰好两种双闭单模结构：笛卡尔结构，其内部 Hom [Instance/Fun.v] 取自然变换，以及有趣的结构，其内部 Hom 是这个范畴。从结构上讲，这是 [Theory/Natural/Transformation.v] 减去 [naturality] 和 [naturality_sym]：恒等式和组合是分量式的，hom-同类集合是 E 中的分量式 [≈]，并且每个范畴定律都是分量式的，继承自 E。在这里不需要 [_sym] 伴随域：随着自然性方框消失，没有剩余的定律具有超过范畴定律本身的对偶方向，而范畴定律本身已经成 [comp_assoc] / [comp_assoc_sym] 对出现。
*)

Program Definition UFun (B E : Category) : Category := {|
  obj     := B ⟶ E;                    (* objects are functors B ⟶ E / 对象是函子 B ⟶ E *)
  hom     := fun F G =>                 (* unnatural transformations: / 不自然的变换： *)
    ∀ b : B, F b ~{E}~> G b;           (* components only, no square / 仅限组件，不要方形 *)
  homset  := fun F G =>                 (* componentwise equivalence / 分量等价 *)
    {| equiv := fun τ σ => ∀ b, τ b ≈ σ b |};
  id      := fun _ _ => id;             (* identity, componentwise / 恒等，按分量 *)
  compose := fun _ _ _ τ σ b => τ b ∘ σ b  (* composition, componentwise / 组合，按分量 *)
|}.
Next Obligation.
  (*
 The componentwise equivalence relation; the remaining five obligations
 (properness of composition and the category laws, all componentwise in
 E) are discharged by the global [cat_simpl] obligation tactic once this
 setoid is in place. 

 --------
 分量对应的等价关系；剩下的五个义务（复合的适当性和范畴律，在 E 中都是按分量的）一旦这个集合族就位，就可以通过全局 [cat_simpl] 义务策略来完成。
*)
  equivalence.
  now transitivity (y b).
Qed.

(*
 Level 0, like the repo's other closed-delimiter notations (e.g. [⟦ n ⟧]
 in Construction/PROP.v): a self-delimited production must be usable in
 function-argument position, which a level-90 production is not. 

 --------
 等级0，像仓库中的其他闭合定界符记法（例如 Construction/PROP.v 中的 [⟦ n ⟧]）：自我定界的产生式必须可以在函数参数位置使用，而等级90的产生式则不能。
*)
Notation "⟦ B , E ⟧" := (UFun B E)
  (at level 0, format "⟦ B ,  E ⟧") : category_scope.
