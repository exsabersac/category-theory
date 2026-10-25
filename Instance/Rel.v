Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Coq.
Require Import Coq.Sets.Ensembles.

Generalizable All Variables.

Local Set Warnings "-intuition-auto-with-star".

(** The category REL of sets and binary relations. / 集合和二元关系的范畴 REL。 *)

(*
 nLab: https://ncatlab.org/nlab/show/Rel
 Wikipedia: https://en.wikipedia.org/wiki/Category_of_relations

 REL has sets (here Coq types, via [obj Coq]) as objects, and a morphism
 `A ~> B` is a heterogeneous binary relation `R ⊆ A × B`. We curry this as
 `A → Ensemble B` (equivalently `A → B → Prop`), so `R a b` means
 `(a, b) ∈ R`. Two relations are equivalent when they are pointwise
 logically equivalent, `f ≈ g := ∀ x y, f x y ↔ g x y` (Prop-valued, so `↔`
 is the right notion of equality on homs).

 objects               Coq types (sets)
 arrows                relations `R ⊆ A × B`, as `A → Ensemble B`
 arrow equivalence     pointwise `↔`
 identity              the diagonal/equality relation `Δ = { (a, a) }`
 composition           relational composition via an existential witness

 Identity is [Singleton]: `id A a = Singleton a`, so `In (id A a) b` holds
 iff `b = a` — the diagonal Δ_A. Composition of `R : A ~> B` then `S : B ~> C`
 is `(S ∘ R) a c = ∃ b, R a b ∧ S b c`, the standard existential-witness
 relational composite (note the diagrammatic order: [compose f g] applies
 `g` first, then `f`).

 REL is a dagger category: the converse `R† = { (b, a) | (a, b) ∈ R }` is an
 involution with `(S ∘ R)† = R† ∘ S†`, and the dagger witnesses the
 self-duality `Rel ≅ Rel^op`. It is moreover locally posetal (relations
 ordered by inclusion) and dagger-compact closed. This file constructs the
 bare category, its initial object, and the wide embedding `Coq ⟶ Rel` of
 functions as relations; the converse/dagger structure, the self-duality
 in Cat, the faithfulness of the embedding, and the terminal/zero-object
 completion live in Instance/Rel/Dagger.v (over Structure/Dagger.v's
 [DaggerCategory] class). Local posetality and compact closure remain
 unformalized. The category laws hold with no axioms. 

 --------
 nLab:  https://ncatlab.org/nlab/show/Rel 
 维基百科:  https://en.wikipedia.org/wiki/Category_of_relations 

 REL 的对象是集合（这里是 Coq 类型，通过  [obj Coq] ），而一个态射
 `A ~> B`  是一个异质二元关系  `R ⊆ A × B` 。我们把它柯里化为
 `A → Ensemble B`  （等价于  `A → B → Prop` ），所以 `R a b` 意味着
 `(a, b) ∈ R` 。当两个关系在每一点上逻辑等价时，它们是等价的，ZWZ12WZZ  （取值为 Prop，因此 `↔` 
 是在同态上的正确等价概念）。

 对象                Coq 类型（集合）
 态射                关系 `R ⊆ A × B` ，作为 `A → Ensemble B` 
 态射等价            每点 `↔` 
 恒等态射            对角/等式关系 `Δ = { (a, a) }` 
 组合                通过存在性证明的关系复合恒等式是 [Singleton] : `id A a = Singleton a`，因此 `In (id A a) b` 当且仅当 `b = a` — 对角线 Δ_A。然后 `R : A ~> B` 与 `S : B ~> C` 的复合是 `(S ∘ R) a c = ∃ b, R a b ∧ S b c`，标准的存在证据关系复合（注意图示顺序：[compose f g] 首先应用 `g`，然后是 `f`）。REL 是一个 dagger 范畴：共轭 `R† = { (b, a) | (a, b) ∈ R }` 是一个带有 `(S ∘ R)† = R† ∘ S†` 的逆元，而 dagger 见证了自对偶 `Rel ≅ Rel^op`。此外，它在局部上是偏序的（关系按包含顺序排列）并且是 dagger-紧闭的。该文件构建了裸范畴、它的初始对象，以及函数作为关系的广义嵌入 `Coq ⟶ Rel`；共轭/dagger 结构、Cat 中的自对偶、嵌入的忠实性以及终端/零对象的完备性都位于 Instance/Rel/Dagger.v（基于 Structure/Dagger.v 的 [DaggerCategory] 类）。局部偏序性和紧闭性仍未形式化。范畴定律在没有公理的情况下成立。
*)

(*
   【Rel 范畴实例展开】/ Rel instance walkthrough
   （口吻对齐 Theory/Functor.v；受众：Coq 小白 + Haskell）

   1) 这是什么 / What this is
      Rel = 关系范畴：对象同 Coq 类型；态射是关系 R ⊆ A×B（写成 A → Ensemble B）。
      Rel = relations; objects = Coq types; homs = relations A→Ensemble B.
      Haskell 对照：像多值/不确定计算（a → Set b），复合是「存在中间点」。
      dagger：转置 R†；自对偶 Rel ≅ Rel^op（详见 Rel/Dagger.v）。
      Analogy: a→Set b; compose via ∃. Dagger = converse (see Dagger.v).

   2) 关键字段 / Key fields
      - obj := obj[Coq]；hom := A ~> Ensemble B
      - ≈ := 逐点 ↔；id := Singleton（对角线）；compose := ∃e, g a e ∧ f e b

   阅读：Rel 记录 → Rel_Initial → Relation_Functor : Coq ⟶ Rel。
   Read: Rel → Rel_Initial → Relation_Functor.
*)
Program Definition Rel : Category := {|
  obj     := @obj Coq;                  (* objects are Coq types (sets) / 对象是 Coq 类型（集合） *)
  hom     := fun A B => A ~> Ensemble B; (* a relation `R ⊆ A × B`, curried / 一个关系 `R ⊆ A × B`，柯里化 *)
  homset  := fun P Q =>                 (* hom-equivalence: pointwise `↔` / hom-等价：逐点 `↔` *)
               {| equiv := fun f g => ∀ x y, f x y ↔ g x y |};
  id      := Singleton;                 (* diagonal: `id a = { b | b = a }` / 对角线：`id a = { b | b = a }` *)
  compose := fun x y z f g a b =>       (* `(f ∘ g) a b = ∃ e, g a e ∧ f e b` / `(f ∘ g) a b = ∃ e, g a e ∧ f e b` *)
               (exists e : y, In y (g a) e ∧ In z (f e) b)%type
|}.
Next Obligation.
  equivalence.
  - apply X; assumption.
  - apply X; assumption.
  - apply X0, X; assumption.
  - apply X, X0; assumption.
Qed.
Next Obligation.
  proper;
  destruct H as [w [H1 H2]];
  exists w; firstorder.
Qed.
Next Obligation.
  split; intros.
  - destruct H as [? [? H2]].
    destruct H2; assumption.
  - exists y0.
    intuition; auto with *.
Qed.
Next Obligation.
  split; intros.
  - destruct H as [? [H1 ?]].
    destruct H1; assumption.
  - exists x0.
    intuition; auto with *.
Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.

(*
 The initial object of REL is the empty set [False]: the only relation
 `∅ ~> A` is the empty relation, and it is forced. (Dually the empty set is
 also terminal, so it is in fact a zero object; the terminal half and the
 bundled [ZeroObject] are Instance/Rel/Dagger.v's [Rel_Terminal] and
 [Rel_Zero].) Since [Initial Rel] unfolds to [Terminal (Rel^op)], the
 primitive field names below are the C^op-side [terminal_obj]/[one]; the
 C-side names [initial_obj]/[zero] are recovered by Structure/Initial.v. 

 --------
 REL 的初始对象是空集 [False]：唯一的关系 `∅ ~> A` 是空关系，并且它是强制的。（对偶地，空集也是终对象，所以实际上它是一个零对象；终对象部分和捆绑的 [ZeroObject] 是 Instance/Rel/Dagger.v 的 [Rel_Terminal] 和 [Rel_Zero]。）由于 [Initial Rel] 展开为 [Terminal (Rel^op)]，下面的原始字段名是 C^op 侧的 [terminal_obj] / [one]；C 侧的名称 [initial_obj] / [zero] 可以通过 Structure/Initial.v 恢复。
*)
#[export]
Program Instance Rel_Initial : @Initial Rel := {
  terminal_obj := False;
  one := fun _ _ => False_rect _ _
}.
Next Obligation. contradiction. Qed.

(*
   Program Instance Rel_Cartesian : @Cartesian Rel := {
   product_obj := @Prod Coq _;
   fork := fun _ _ _ f g x y => f x (fst y) ∧ g x (snd y);
   exl  := fun _ _ p x => In _ (Singleton _ (fst p)) x;
   exr  := fun _ _ p x => In _ (Singleton _ (snd p)) x
   }.
   Next Obligation.
   proper.
   split; intros.
   destruct H.
   split; intros.
   apply X0; assumption.
   apply X1; assumption.
   destruct H.
   split; intros.
   apply X0; assumption.
   apply X1; assumption.
   Qed.
   Next Obligation.
   firstorder.
   - destruct H1.
   apply H, H0.
   - eexists (y, _).
   split.
   apply H; simpl.
   split.
   assumption.
   apply H.
   Qed.

   Program Instance Rel_Cocartesian : @Cocartesian Rel := {
   product_obj := or;
   fork := fun _ _ _ f g x =>
   match x with
   | or_introl v => f v
   | or_intror v => g v
   end;
   exl  := fun _ _ p => or_introl p;
   exr  := fun _ _ p => or_intror p
   }.
   Obligation 1. proper; autounfold in *; apply proof_irrelevance. Qed.
   Obligation 2.
   autounfold in *.
   split; intros.
   split; intros;
   apply proof_irrelevance.
   apply proof_irrelevance.
   Qed.

   Program Instance Rel_Closed : @Closed Rel _ := {
   exponent_obj := Basics.impl;
   exp_iso := fun _ _ _ =>
   {| to   := {| morphism := fun f a b => f (conj a b) |}
   ; from := {| morphism := fun f p => f (proj1 p) (proj2 p) |} |}
   }.
   Next Obligation. proper; autounfold in *; apply proof_irrelevance. Qed.
   Next Obligation. proper; autounfold in *; apply proof_irrelevance. Qed.
   Next Obligation. autounfold in *; apply proof_irrelevance. Qed.
   Next Obligation. autounfold in *; apply proof_irrelevance. Qed.
   Next Obligation. autounfold in *; apply proof_irrelevance. Qed.

   --------
   程序实例 Rel_Cartesian : @Cartesian Rel := {
   product_obj := @Prod Coq _;
   fork := fun _ _ _ f g x y => f x (fst y) ∧ g x (snd y);
   exl  := fun _ _ p x => In _ (Singleton _ (fst p)) x;
   exr  := fun _ _ p x => In _ (Singleton _ (snd p)) x
   }.
   下一个义务。
   proper.
   分割; 假设.
   分解 H.
   分割; 假设.
   应用 X0; 假设.
   应用 X1; 假设.
   分解 H.
   分割; 假设.
   应用 X0; 假设.
   应用 X1; 假设.
   证毕.
   下一个义务。
   firstorder.
   - 分解 H1.
   应用 H, H0.
   - 存在 (y, _).
   分割.
   应用 H; 简化.
   分割.
   假设.
   应用 H.程序实例 Rel_Cocartesian : @Cocartesian Rel := {
   product_obj := or;
   fork := fun _ _ _ f g x =>
   match x with
   | or_introl v => f v
   | or_intror v => g v
   end;
   exl  := fun _ _ p => or_introl p;
   exr  := fun _ _ p => or_intror p
   }.
   义务 1. proper; autounfold in *; apply proof_irrelevance. 已完成.
   义务 2.
   autounfold in *.
   split; intros.
   split; intros;
   apply proof_irrelevance.
   apply proof_irrelevance.
   已完成.程序实例 Rel_Closed : @Closed Rel _ := {
   exponent_obj := Basics.impl;
   exp_iso := fun _ _ _ =>
   {| to   := {| morphism := fun f a b => f (conj a b) |}
   ; from := {| morphism := fun f p => f (proj1 p) (proj2 p) |} |}
   }.
   下一个义务。proper; autounfold in *; apply proof_irrelevance. 结束。
   下一个义务。proper; autounfold in *; apply proof_irrelevance. 结束。
   下一个义务。autounfold in *; apply proof_irrelevance. 结束。
   下一个义务。autounfold in *; apply proof_irrelevance. 结束。
   下一个义务。autounfold in *; apply proof_irrelevance. 结束。
*)

(*
 A sample non-functional morphism: the strict-order relation `<` on nat,
 a genuine relation of REL that is not the graph of any function. 

 --------
 一个非功能性态射的示例：自然数上的严格顺序关系 `<`，REL 的一个真正关系，但不是任何函数的图像。
*)
Definition some_number : nat ~{Rel}~> nat := fun x y => (x < y)%nat.

(*
 The wide embedding of functions as relations, `Coq ⟶ Rel`: a function `f`
 is sent to its graph `{ (x, y) | f x = y }`. It is the identity on objects
 and faithful, exhibiting Coq (Set) as a wide subcategory of REL. 

 --------
 函数作为关系的广泛嵌入，`Coq ⟶ Rel`: 一个函数`f` 被发送到它的图`{ (x, y) | f x = y }`。它在对象上是恒等的且忠实的，将 Coq (Set) 展示为 REL 的广泛子范畴。
*)
#[export]
Program Instance Relation_Functor : Coq ⟶ Rel := {
  fobj := fun x => x;
  fmap := fun x y (f : x ~{Coq}~> y) x y => In _ (Singleton _ (f x)) y
}.
Next Obligation. proper; congruence. Qed.
Next Obligation.
  simplify; firstorder.
  destruct a, b; constructor.
Qed.
