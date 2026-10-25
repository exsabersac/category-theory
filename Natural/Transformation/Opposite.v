Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(** * The opposite (dual) of a natural transformation.  / * 自然变换的对偶（相反）*)

(*
nLab: https://ncatlab.org/nlab/show/opposite+functor
   Wikipedia: https://en.wikipedia.org/wiki/Opposite_category

   Oppositization is covariant on functors but reverses 2-cells: a natural
   transformation `N : F ⟹ G` between `F G : C ⟶ D` yields the opposite
   transformation `N^op : G^op ⟹ F^op` (note the swap of source and target).
   The component of `N^op` at `x` is `N x` itself, only reread through the
   duality: `N x : F x ~> G x` in `D` is the same morphism as `G^op x ~> F^op x`
   in `D^op`. Accordingly the naturality square of `N^op` is just the naturality
   square of `N` with its two orientations swapped, so the `naturality` field of
   `N^op` is `N`'s `naturality_sym` (and vice versa) with object indices
   transposed — no rewriting is needed, matching the built-in duality of
   [Transform]. This makes op the 2-functor `Cat^co ⟶ Cat`: a natural
   transformation `F^op ⟹ G^op` corresponds to one `G ⟹ F`, not `F ⟹ G`. 

--------
nLab：https://ncatlab.org/nlab/show/opposite+functor
 维基百科：https://en.wikipedia.org/wiki/Opposite_category

 对立在函子上是协变的，但反转 2 单元：自然
 `F G : C ⟶ D` 之间的变换 `N : F ⟹ G` 产生相反的结果
 转换`N^op : G^op ⟹ F^op`（注意源和目标的交换）。 
`x` 处 `N^op` 的分量是 `N x` 本身，只需通过
 对偶性：“D”中的“N x : F x ~> G x”与“G^op x ~> F^op x”具有相同的态射
 在“D^op”中。 因此，“N^op”的自然度平方就是自然度
 “N”的平方，其两个方向交换，因此“自然性”场
 `N^op` 是具有对象索引的 `N` 的 `naturality_sym`（反之亦然）
 转置——无需重写，匹配内置的对偶性
 [Transform]。 这使得 op 成为 2-函子 `Cat^co ⟶ Cat`：一个自然的
 变换`F^op ⟹ G^op`对应于一个`G ⟹ F`，而不是`F ⟹ G`。 
*)

Definition Opposite_Transform `{F : C ⟶ D} {G : C ⟶ D} `(N : F ⟹ G) :
  G^op ⟹ F^op :=
  @Build_Transform (C^op) (D^op) (G^op) (F^op) N
    (λ (x y : (C ^op)%category) (f : x ~{C^op}~> y),
      @naturality_sym C D F G N y x f)
    (λ (x y : (C ^op)%category) (f : x ~{C^op}~> y),
      @naturality C D F G N y x f).

Notation "N ^op" := (@Opposite_Transform _ _ _ _ N)
  (at level 7, format "N ^op", left associativity) : transform_scope.

Open Scope transform_scope.

(*
The op functor is an involution on natural transformations: applying it twice
   recovers `N` definitionally, since (C^op)^op = C and (F^op)^op = F hold by
   reflexivity and `N^op` reuses `N`'s components. 

--------
op 函子是自然变换的对合：应用它两次
 从定义上恢复“N”，因为 (C^op)^op = C 且 (F^op)^op = F 成立
 自反性和“N^op”重用了“N”的组件。 
*)

Corollary Opposite_Transform_invol `{F : C ⟶ D} {G : C ⟶ D} `(N : F ⟹ G) :
  (N^op)^op = N.
Proof. reflexivity. Qed.
