Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.FAlg.
Require Import Category.Instance.Omega.
Require Import Category.Construction.Chain.
Require Import Category.Theory.Adamek.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Corollaries of Adámek's initial-algebra theorem / * Adámek 初代数定理的推论 *)

(*
nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
   Wikipedia: https://en.wikipedia.org/wiki/Initial_algebra

   Adámek's theorem (Theory/Adamek.v) builds the initial [F]-algebra as the
   colimit of the ω-chain

       0 --¡--> F 0 --F¡--> F² 0 --F²¡--> ...

   ([Construction/Chain.v], [Chain F : Omega ⟶ C]).  The theorem [adamek]
   there consumes a [Colimit (Chain F)] together with the honest hypothesis
   [AdamekData F L] recording that [F A] carries a colimit of the shifted
   diagram [F ◯ Chain F] whose injections are exactly the image legs
   [fmap[F] (colimit_inj HL n)].

   This file records the standard packaging corollary: in a *cocomplete*
   category the colimit [Colimit (Chain F)] is available for free — it is the
   colimit that cocompleteness furnishes for the ω-shaped diagram [Chain F] —
   so one need only supply the [AdamekData] leg-agreement to obtain the initial
   [F]-algebra.  A worked instance of the endofunctor side is recorded as
   [NatF], the option endofunctor on COQ.

   Ledger 17 / outstanding: the discharge [PreservesColimit -> AdamekData] is
   not carried here either.  As explained in the header of Theory/Adamek.v, an
   abstract [PreservesColimit] witness only records that [F A] carries SOME
   colimit of [F ◯ Chain F]; two colimit cocones at the shared apex [F A]
   differ by a free apex-automorphism, so it does not expose the leg agreement
   [colimit_inj (F-image colimit) n ≈ fmap[F] (colimit_inj HL n)] that the
   initiality argument consumes.  That leg-agreement bridge therefore remains a
   fast-follow; the [AdamekData] interface is the load-bearing contract in the
   interim and is threaded unchanged through the cocomplete corollary below.

--------
nLab：https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
维基百科：https://en.wikipedia.org/wiki/Initial_algebra

Adámek 定理 (Theory/Adamek.v) 将初始 [F]-代数构建为 ω 链的余极限

0 --¡--> F 0 --F¡--> F² 0 --F²¡--> ...

([Construction/Chain.v]，[Chain F : Omega ⟶ C])。定理 [adamek] 在那里使用了 [Colimit (Chain F)] 以及诚实假设 [AdamekData F L]，记录了 [F A] 携带了偏移图 [F ◯ Chain F] 的余极限，其注入正是像的腿 [fmap[F]（colimit_inj HL n）]。

此文件记录了标准包装推论：在一个*完备余范畴*中，余极限 [Colimit (Chain F)] 可以免费获得——它是完备余范畴为 ω 形图 [Chain F] 提供的余极限——因此只需提供 [AdamekData] 的分支一致性即可获得初始 [F] 代数。一个关于自函子侧的实例记录为 [NatF]，即 COQ 上的选项自函子。

账本 17 / 未完成：此处也未载入 [PreservesColimit -> AdamekData]。如 Theory/Adamek.v 的标题所解释，抽象的 [PreservesColimit] 见证者仅记录 [F A] 承载 [F ◯ Chain F] 的某个余极限；在共享顶点 [F A] 处的两个余极限余锥通过一个自由顶点自同构而不同，因此它不会暴露初始性论证所使用的腿部一致性 [colimit_inj (F-image colimit) n ≈ fmap[F]（colimit_inj HL n）。因此，该腿部一致性桥仍然是一个快速跟随；[AdamekData] 接口在此期间是承重契约，并且在下面的余完备推论中保持不变。
*)

(*
[Cocomplete C] (Structure/Complete.v) is [∀ D (G : D ⟶ C), Colimit G].
   Applying it to the ω-shape [Omega] and the diagram [Chain F] yields the
   colimit [Colimit (Chain F)] that [adamek] requires, with no further
   hypotheses.  We then feed that colimit together with the supplied
   [AdamekData] to [adamek].  The [Colimit] argument is threaded explicitly and
   identically into both the type of [D] and the body, so the [AdamekData]'s
   ambient colimit [L] and the one consumed by [adamek] are the very same
   term.

--------
[Cocomplete C] (Structure/Complete.v) 是 [∀ D (G : D ⟶ C), Colimit G]。
将其应用到 ω 形 [Omega] 和图 [Chain F] 会产生 [Colimit (Chain F)] 的余极限，这是 [adamek] 所需要的，无需其他假设。然后，我们将该余极限与提供的 [AdamekData] 一起输入到 [adamek]。[Colimit] 参数被显式地且相同地穿入 [D] 的类型和主体，因此 [AdamekData] 的环境余极限 [L] 与 [adamek] 消耗的余极限是完全相同的项。
*)
Corollary adamek_cocomplete
  {C : Category} `{@Initial C} (F : C ⟶ C)
  (CC : @Cocomplete C)
  (D : AdamekData F (CC _ (Chain F))) :
  @Initial (FAlg F).
Proof.
  exact (adamek F (CC _ (Chain F)) D).
Qed.

(*
The option endofunctor [NatF X := option X = 1 + X] on COQ (Instance/Coq.v).
   It is the polynomial endofunctor whose initial algebra is the type [nat]:
   the structure map [1 + nat ~> nat] is [O]/[S] ([None ↦ O], [Some k ↦ S k]),
   and initiality is exactly primitive recursion on [nat].

   [NatF] is the [A := unit] specialisation of the list endofunctor
   [ListF A X := option (A × X)] (Instance/Coq/Lists.v) up to the isomorphism
   [unit × X ≅ X]; that file carries the fully worked initial-algebra proof for
   [ListF A] (with [list A] the carrier), so the analogous [nat] initiality for
   [NatF] is exactly the [A := unit] reading of it.  Only the functor [NatF]
   itself is formalized below; the initiality is proven in Instance/Coq/Nat.v,
   where [nat_initial : @Initial (FAlg NatF)] exhibits [nat] with [O]/[S] as
   the initial [NatF]-algebra — existence of the mediator by primitive
   recursion, uniqueness by induction — and [nat_lambek] reads off the Lambek
   isomorphism [1 + nat ≅ nat].  As with [list A], that proof is direct and
   does not route through [adamek]: no [AdamekData] witness is constructed
   anywhere in the tree, so the ω-colimit route stays conditional and the
   concrete initial algebras are established by hand.

--------
COQ 上的选项自函子 [NatF X := option X = 1 + X]（实例/Coq.v）。
它是其初始代数为类型 [nat] 的多项式自函子：
结构映射 [1 + nat ~> nat] 是 [O]/[S] ([None ↦ O], [Some k ↦ S k])，
初始性恰好是 [nat] 上的原始递归。

[NatF] 是列表终结函子 [ListF A X := option (A × X)]（Instance/Coq/Lists.v）的 [A := unit] 专门化，直到同构 [unit × X ≅ X]；该文件包含对 [ListF A]（其载体为 [list A]）的完整初代代数证明，因此对 [NatF] 的类似 [nat] 初性正是其 [A := unit] 解读。下面仅形式化了函子 [NatF] 本身；初性在 Instance/Coq/Nat.v 中证明，其中 [nat_initial : @Initial (FAlg NatF)] 展示了 [nat]，将 [O]/[S] 作为初始 [NatF]-代数 —— 通过原始递归证明中介的存在，通过归纳证明唯一性 —— 并且 [nat_lambek] 读出 Lambek 同构 [1 + nat ≅ nat]。如同 [list A]，该证明是直接的，并未通过 [adamek]：在树中的任何位置都没有构造 [AdamekData] 见证，因此 ω-余极限方法保持条件性，而具体的初始代数是手工建立的。
*)

(*
Keep obligation handling explicit and predictable (as in Instance/Coq/Lists.v):
   surface each functor law as its own obligation rather than letting the ambient
   [cat_simpl] discharge or reshape them.

--------
保持义务处理的明确性和可预测性（如在 Instance/Coq/Lists.v 中）：将每个函子定律作为其自身的义务来呈现，而不是让环境 [cat_simpl] 去解除或重塑它们。
*)
#[local] Obligation Tactic := idtac.

Program Definition NatF : Coq ⟶ Coq := {|
  fobj := fun X => option X;
  fmap := fun X Y (f : X -> Y) o =>
            match o with
            | None   => None
            | Some x => Some (f x)
            end
|}.
Next Obligation.
  (* fmap respects pointwise equality of functions / fmap 尊重函数的逐点相等性 *)
  intros X Y f g Hfg o.
  destruct o as [x|].
  - simpl; rewrite (Hfg x); reflexivity.
  - reflexivity.
Qed.
Next Obligation.
  (* fmap preserves identities / fmap 保持恒等式 *)
  intros X o.
  destruct o as [x|]; reflexivity.
Qed.
Next Obligation.
  (* fmap preserves composition / fmap 保持组合性 *)
  intros X Y Z f g o.
  destruct o as [x|]; reflexivity.
Qed.
