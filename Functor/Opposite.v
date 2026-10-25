Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** The opposite (dual) functor F^op : C^op ⟶ D^op.  / 相反（对偶）函子 F^op ：C^op ⟶ D^op。*)

(*
nLab: https://ncatlab.org/nlab/show/opposite+functor
   Wikipedia: https://en.wikipedia.org/wiki/Opposite_category

   Given F : C ⟶ D, the opposite functor F^op : C^op ⟶ D^op acts the same as
   F on both objects and morphisms; only the (formally reversed) source and
   target categories change. On objects (F^op) x := F x, and a morphism
   f : x ~{C^op}~> y (that is, f : y ~> x in C) is sent to fmap[F] f, read as a
   morphism F x ~{D^op}~> F y. The functoriality fields are the corresponding
   fields of F with their object indices swapped, and fmap_comp is reindexed to
   match the reversed composition of C^op (g ∘ f there is f ∘ g in C).

   Because the underlying duality is built in so that (C^op)^op = C holds by
   reflexivity, and F^op reuses the same object/morphism maps as F, the
   construction is involutive: (F^op)^op = F, provable by [reflexivity] (see
   Opposite_Functor_invol below). A contravariant functor C ⟶ D is, by
   definition, an ordinary functor out of C^op; see [contramap] at the end.

   On 1-cells (functors) oppositization is covariant, but note that on 2-cells
   (natural transformations) it reverses direction: a natural transformation
   F^op ⟹ G^op corresponds to one G ⟹ F, so op is the 2-functor Cat^co ⟶ Cat. 

--------
nLab: https://ncatlab.org/nlab/show/opposite+functor
   Wikipedia: https://en.wikipedia.org/wiki/Opposite_category

   给定 F : C ⟶ D，对偶函子 F^op : C^op ⟶ D^op 在对象与态射上与 F 作用相同；仅
   （形式反向的）源与目标范畴改变。对象上 (F^op) x := F x；态射 f : x ~{C^op}~> y
   （即 C 中 f : y ~> x）被送到 fmap[F] f，读作态射 F x ~{D^op}~> F y。函子性字段是
   F 的对应字段，对象指标交换，fmap_comp 重指标以匹配 C^op 的反向复合（彼处 g ∘ f
   是 C 中的 f ∘ g）。

   因底层对偶使 (C^op)^op = C 由 reflexivity 成立，且 F^op 复用与 F 相同的对象/态射映射，
   构造对合：(F^op)^op = F，可由 [reflexivity] 证明（见下文 Opposite_Functor_invol）。
   反变函子 C ⟶ D 按定义是出自 C^op 的普通函子；见文末 [contramap]。

   在 1-胞（函子）上对偶化共变，但注意在 2-胞（自然变换）上方向反转：自然变换
   F^op ⟹ G^op 对应 G ⟹ F，故 op 是 2-函子 Cat^co ⟶ Cat。 
*)

(*
   【Opposite_Functor 定义展开】/ Definition walkthrough
   （口吻对齐 Theory/Functor.v @ c826572；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      F^op : C^op ⟶ D^op 与 F 在对象/态射数据上相同，只是源/靶范畴形式对偶。
      F^op reuses F's object/morphism maps; only formal opposites change.
      Haskell 对照：contramap / Contravariant；本库用「出自 C^op 的普通函子」
      表达反变，文末 contramap 把 C-箭头读成 C^op-箭头再 fmap。
      Haskell analogy: Contravariant/contramap; here contravariance = Functor
      out of C^op; contramap below reads C-arrows as C^op-arrows.

   2) 关键点 / Key points
      - fmap_comp 指标对调，以匹配 C^op 的反向复合。
        / fmap_comp reindexed for reversed composition in C^op.
      - (F^op)^op = F（对合，reflexivity）/ involution on the nose.
      - 定律仍对 ≈（来自 F 的 fmap_respects / fmap_id / fmap_comp）。
        / laws still up to ≈, inherited from F.

   阅读顺序：Opposite_Functor → ^op 记法 → contramap。
   Reading order: Opposite_Functor → ^op notation → contramap.
*)

Definition Opposite_Functor `(F : C ⟶ D) : C^op ⟶ D^op :=
  @Build_Functor (C^op) (D^op) F
    (λ (x y : C ^op) (f : x ~{ C ^op }~> y), @fmap C D F y x f)
    (λ (x y : C ^op) (f g : x ~{ C ^op }~> y), @fmap_respects _ _ F y x f g)
    (λ x : C ^op, fmap_id)
    (λ (x y z : C ^op) (f : y ~{ C ^op }~> z)
      (g : x ~{ C ^op }~> y), @fmap_comp _ _ F _ _ _ g f).

(* Mirrors the C^op notation on categories, at the same level/scope.  / 在同一级别/范围上反映类别上的 C^op 表示法。*)

Notation "F ^op" := (@Opposite_Functor _ _ F)
  (at level 7, format "F ^op", left associativity) : functor_scope.

Open Scope functor_scope.

(*
The op functor is an involution on functors: applying it twice recovers F
   on the nose. Both sources state (C^op)^op = C, and F^op reuses F's maps. 

--------
op 函子是函子的对合：应用它两次可以恢复 F
 在鼻子上。 两个来源都表明 (C^op)^op = C，并且 F^op 重用 F 的映射。 
*)

Corollary Opposite_Functor_invol `{F : C ⟶ D} : (F^op)^op = F.
Proof. reflexivity. Qed.

(*
A functor F : C^op ⟶ D is a contravariant functor on C: it reverses the
   direction of morphisms. [contramap] applies it to a C-arrow f : x ~> y by
   reading f as the C^op-arrow (op f), yielding F y ~> F x in D. 

--------
函子 F : C^op ⟶ D 是 C 上的逆变函子：它反转
 态射的方向。 [contramap] 将其应用于 C 箭头 f : x ~> y
 将 f 读作 C^op 箭头 (op f)，产生 D 中的 F y ~> F x。 
*)

Definition contramap `{F : C^op ⟶ D} `(f : x ~{C}~> y) :
  F y ~{D}~> F x := fmap (op f).

(*
The fullness and faithfulness rows of Mac Lane §IV.3 Exercise 1's
   dualization table, for an ARBITRARY functor — previously reachable
   only through the equivalence detour of Theory/Equivalence/Limit.v.
   The op-functor's hom-action at (x, y) is the original's at (y, x), so
   each property transports by reindexing, in both directions; every
   obligation is an [exact] at the swapped indices. 

--------
Mac Lane §IV.3 练习 1 的完整行和忠实行
 对偶表，用于任意函子 - 以前可达
 只能通过 Theory/Equivalence/Limit.v 的等价迂回。 
运算函子在 (x, y) 处的 hom-action 是原始函子在 (y, x) 处的 hom-action，所以
 每个属性都通过重新索引在两个方向上进行传输； 每个
 义务是交换索引处的 [exact]。 
*)

#[local] Obligation Tactic := idtac.

Program Definition Full_op `{F : C ⟶ D} (H : Full F) : Full (F^op) := {|
  prefmap := fun x y g => @prefmap _ _ F H y x g
|}.
Next Obligation.
  intros; exact (@fmap_sur _ _ F H y x g).
Qed.

Program Definition Full_of_op `{F : C ⟶ D} (H : Full (F^op)) : Full F := {|
  prefmap := fun x y g => @prefmap _ _ (F^op) H y x g
|}.
Next Obligation.
  intros; exact (@fmap_sur _ _ (F^op) H y x g).
Qed.

Program Definition Faithful_op `{F : C ⟶ D} (H : Faithful F) :
  Faithful (F^op) := {|
  fmap_inj := fun x y f g => @fmap_inj _ _ F H y x f g
|}.

Program Definition Faithful_of_op `{F : C ⟶ D} (H : Faithful (F^op)) :
  Faithful F := {|
  fmap_inj := fun x y f g => @fmap_inj _ _ (F^op) H y x f g
|}.
