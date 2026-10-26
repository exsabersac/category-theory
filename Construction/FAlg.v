Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

(** * The category of F-algebras / * F-代数的类别 *)

(*
 nLab:      https://ncatlab.org/nlab/show/algebra+over+an+endofunctor
 Wikipedia: https://en.wikipedia.org/wiki/F-algebra

 For an endofunctor [F : C ⟶ C], an F-algebra is an object [a] with a
 structure map [α : F a ~> a] (this is [FAlgebra F a] of Theory/Functor.v).
 A morphism of F-algebras [(a, α) ~> (b, β)] is a carrier map [h : a ~> b]
 commuting with the structure maps: [h ∘ α ≈ β ∘ fmap[F] h].  These form the
 category [FAlg F]; its initial object (when it exists) is the least fixed
 point of [F], and Lambek's lemma shows the initial structure map is an
 isomorphism [F μF ≅ μF] (Theory/Lambek.v).

 The construction mirrors [Monad/Eilenberg/Moore.v]: a bundled hom class
 [FAlgHom] carrying the commuting square, a dependent-pair object carrier,
 and a hom-setoid comparing the underlying carrier maps. 

 --------
 nLab：       https://ncatlab.org/nlab/show/algebra+over+an+endofunctor 
 维基百科：  https://en.wikipedia.org/wiki/F-algebra 

 对于一个端函子  [F : C ⟶ C] ，F-代数是一个对象  [a]  以及一个结构映射  [α : F a ~> a]  （这是  [FAlgebra F a]  在 Theory/Functor.v 中）。F-代数的态射  [(a, α) ~> (b, β)]  是一个载体映射  [h : a ~> b] ，它与结构映射交换：  [h ∘ α ≈ β ∘ fmap[F]  h]。它们形成了类别  [FAlg F] ；其初始对象（当存在时）是  [F] 的最小不动点，Lambek 引理表明初始结构映射是一个同构  [F μF ≅ μF]  （Theory/Lambek.v）。

 该构造类似于  [Monad/Eilenberg/Moore.v] ：一个捆绑的同态类  [FAlgHom] ，携带交换方格、依赖对对象载体，以及比较底层载体映射的同态集。
*)

(*
 Where the construction comes from, and what recursion becomes

 nLab:      https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor
 Wikipedia: https://en.wikipedia.org/wiki/Catamorphism
 Paper: Lambek, “A Fixpoint Theorem for Complete Categories”,
 Mathematische Zeitschrift 103, 1968
 Paper: Adámek, “Free algebras and automata realizations in the
 language of categories”, Comment. Math. Univ. Carolinae 15(4),
 1974
 Paper: Meijer, Fokkinga, Paterson, “Functional Programming with
 Bananas, Lenses, Envelopes and Barbed Wire”, FPCA 1991, LNCS 523
 Paper: Rutten, “Universal coalgebra: a theory of systems”,
 Theoretical Computer Science 249(1), 2000

 The least-fixed-point reading the header records has a precise origin.
 Lambek (1968) sought fixed points of an endofunctor by locating an
 INITIAL algebra rather than by iterating the functor; the invertibility
 lemma the header names is the observation that underwrites the method.
 The modern literature reads that lemma as a categorification of the
 Knaster–Tarski lattice fixed-point theorem, and Lambek returned to the
 theme over cartesian closed bases in “Least Fixpoints of Endofunctors
 of Cartesian Closed Categories” (Math. Structures in Comp. Sci. 3,
 1993).

 Naming [FAlg F] a category, and not μF a fixed point alone, is what
 turns recursion into a universal property.  For any target algebra
 (a, β) there is exactly one algebra map out of the initial object, and
 its carrier is the CATAMORPHISM, the categorical fold.  Existence of
 that map is what permits a definition by structural recursion, and
 uniqueness is the induction and fusion principle used to reason about
 it.  Theory/Recursion.v makes this literal: [cata β] is
 [falg_hom[ @zero (FAlg F) I (a ; β) ]], the carrier of the initial
 mediator, and [cata_commutes] is its recursion equation.

 The programming lineage runs through this fold.  Bird and Meertens
 built a calculus of programs in the 1980s in which folds are the
 central operator, and Malcolm (1990) gave the categorical definition of
 a catamorphism as the unique homomorphism out of an initial algebra.
 Meijer, Fokkinga and Paterson (1991) introduced the banana-bracket
 notation for it, cast explicit recursion as the functional-programming
 counterpart of the arbitrary goto that structured programming had
 abandoned, and recovered the structured schemes — cata, ana, hylo —
 from which the later Haskell idiom descends; Wadler (“Recursive Types
 for Free!”, 1990) ties inductive types to initial F-algebras in the
 same spirit.

 The header assumes an initial object “when it exists”; Adámek (1974)
 supplies it, building μF as the colimit of the ω-chain
 0 → F0 → F²0 → … whenever F preserves that colimit.  Theory/Adamek.v
 carries this as [adamek], proven from the leg-agreement hypothesis
 [AdamekData], over the diagram [Chain] (Construction/Chain.v) indexed by
 the ordinal ω (Instance/Omega.v).  The option endofunctor [NatF] in
 Theory/Adamek/Corollaries.v records the endofunctor side, and its [nat]
 initiality is proven in Instance/Coq/Nat.v -- [nat_initial] exhibits
 (nat, O/S) as the initial [NatF]-algebra, with [nat_lambek] the Lambek
 isomorphism read off it.  The
 book-length account is Adámek and Trnková, Automata and Algebras in
 Categories (1990).

 Dually, [FCoalg] (Construction/FCoalg.v) is the category of coalgebras,
 whose TERMINAL object is the greatest fixed point νF — codata in place
 of data.  Rutten (2000) organizes this side into a theory of systems:
 finite data are initial algebras, whereas streams, automata and
 transition systems are final coalgebras, and the algebra / homomorphism
 / congruence trinity dualizes to coalgebra / homomorphism /
 bisimulation, with coinduction the proof principle, resting on the
 bisimulation of Milner (1980) and Park (1981) and the non-wellfounded
 sets of Aczel (1988).  In-tree, [lambek_final] and [ana] mirror
 [lambek] and [cata], and Instance/Sets/Streams.v realizes streams as
 the final [StreamF]-coalgebra with equality taken as bisimilarity.

 Read computationally, an object (a, β : F a ~> a) is a one-layer
 evaluator: given a top constructor layer whose children have already
 been reduced to results — an element of F a — it returns a result of
 type a.  For the list signature [ListF A] (Instance/Coq/Lists.v),
 sending X to 1 + A × X, the structure map is a pair: a nil case and a
 cons step, precisely the two arguments of foldr.  It follows that the
 initial algebra is the type of finite F-shaped values with its
 constructor bundle for a structure map, and [cata β] is the recursive
 fold threading β through the whole shape — realized axiom-free with
 [list A] as μ (ListF A). 

 --------
 构造的来源，以及递归的发展

 nLab:       https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor 
 维基百科:  https://en.wikipedia.org/wiki/Catamorphism 
 论文: Lambek，《完备范畴的一个不动点定理》，
 数学杂志 103, 1968
 论文: Adámek，《范畴语言中的自由代数与自动机实现》，
 卡罗莱纳大学数学评论 15(4), 1974
 论文: Meijer, Fokkinga, Paterson，《使用香蕉、透镜、信封和带刺铁丝的函数式编程》，
 FPCA 1991, LNCS 523
 论文: Rutten，《通用余代数：系统理论》，
 理论计算机科学 249(1), 2000以最小不动点读取头记录有一个精确的起源。Lambek (1968) 通过找到一个初始代数而不是迭代函子来寻找一个自函子的不动点；头记录所命名的可逆性引理是支撑该方法的观察。现代文献将该引理解读为 Knaster–Tarski 格不动点定理的范畴化，而 Lambek 在《笛卡尔封闭范畴的自函子最小不动点》(数学结构在计算机科学 3, 1993) 中在笛卡尔封闭基上回到这个主题。将 [FAlg F] 命名为一个范畴，而不是仅仅将 μF 视为一个固定点，正是将递归转化为泛性质的原因。对于任何目标代数 (a, β)，从初始对象到它的代数映射恰好有一个，其承载体就是 CATAMORPHISM，即范畴折叠。该映射的存在允许通过结构递归进行定义，而唯一性则是用来推理的归纳和融合原则。Theory/Recursion.v 将这一点具体化：[cata β] 是 [falg_hom[ @zero (FAlg F) I (a ; β) ]，即初始中介的承载体，而 [cata_commutes] 则是它的递归方程。编程的传承贯穿于这个折叠中。Bird 和 Meertens 在 1980 年代建立了一个程序演算，其中折叠是核心操作符，而 Malcolm (1990) 给出了 catamorphism 的范畴定义，即初始代数中唯一的同态映射。Meijer、Fokkinga 和 Paterson (1991) 为它引入了香蕉括号符号，将显式递归视为结构化编程弃用的任意 goto 的函数式编程对应，并恢复了后来的 Haskell 习惯所衍生的结构方案——cata、ana、hylo；Wadler（“Recursive Types for Free!”, 1990）以同样的精神将归纳类型与初始 F-代数联系起来。该头假设存在一个初始对象“当它存在时”；Adámek (1974) 提供了它，将 μF 构建为 ω 链 0 → F0 → F²0 → … 的余极限，只要 F 保持该余极限。Theory/Adamek.v 中记录了这一点，记作 [adamek]，并从腿一致性假设 [AdamekData] 在图 [Chain] （Construction/Chain.v）上证明，该图由序数 ω (Instance/Omega.v) 索引。选项自函子 [NatF] 在 Theory/Adamek/Corollaries.v 中记录自函子的一侧，其 [nat] 的初始性在 Instance/Coq/Nat.v 中得到证明 —— [nat_initial] 展示了 (nat, O/S) 作为初始 [NatF]-代数，并从中读取 [nat_lambek] 为 Lambek 同构。书籍长度的描述见 Adámek 和 Trnková，《Categories 中的自动机与代数》 (1990)。对偶地，[FCoalg]（构造/FCoalg.v）是余代数的范畴，
 其终结对象是最大不动点νF——余数据已定
 数据的。Rutten（2000）将这一方面组织为系统理论：
 有限数据是初始代数，而流、自动机和
 转移系统是终余代数，代数/同态
 / 全余三位一体对偶化为余代数 / 同态 /
 双模拟，结合共归纳的证明原理，基于
 Milner（1980）和Park（1981）的双模拟以及非良基
 Aczel（1988）的集合。树内、[lambek_final]与[ana]镜像
 [lambek] 和 [cata] ，实例/集合/流.v 将流实现为
 最后一个[StreamF] -coalgebra，等式视为双相似性。从计算的角度来看，一个对象 (a, β : F a ~> a) 是一个单层求值器：给定一个顶层构造器层，其子元素已被简化为结果 —— F a 的元素 —— 它返回类型为 a 的结果。对于列表签名 [ListF A]（Instance/Coq/Lists.v），将 X 映射到 1 + A × X，结构映射是一个对：一个 nil 情况和一个 cons 步骤，正好是 foldr 的两个参数。因此，初始代数是有限 F 形值类型及其作为结构映射的构造器捆绑，而 [cata β] 是将 β 贯穿整个形状的递归 fold —— 在没有公理的情况下由 [list A] 实现为 μ (ListF A)。
*)

Class FAlgHom `(F : C ⟶ C) (a b : C)
      (α : FAlgebra F a) (β : FAlgebra F b) := {
  falg_hom : a ~> b;
  falg_commutes : falg_hom ∘ α ≈ β ∘ fmap[F] falg_hom
}.

Notation "falg_hom[ H ]" := (@falg_hom _ _ _ _ _ _ H)
  (at level 9, format "falg_hom[ H ]") : morphism_scope.

Program Definition FAlg `(F : C ⟶ C) : Category := {|
  obj     := ∃ a : C, FAlgebra F a;
  hom     := fun x y => FAlgHom F ``x ``y (`2 x) (`2 y);
  homset  := fun _ _ => {| equiv := fun f g => falg_hom[f] ≈ falg_hom[g] |};
  id      := fun _ => {| falg_hom := id |};
  compose := fun _ _ _ f g => {| falg_hom := falg_hom[f] ∘ falg_hom[g] |}
|}.
Next Obligation.
  (*
 the composite carrier map is an algebra map, pasting the two squares
 (the id-map and the setoid/category-law obligations are discharged by the
 ambient obligation tactic, as in Monad/Eilenberg/Moore.v). 

 --------
 复合承载映射是一个代数映射，将两个方块粘合起来（恒等映射和集合同构/范畴律的义务由环境义务策略解除，如在 Monad/Eilenberg/Moore.v 中）。
*)
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- falg_commutes.
  rewrite <- !comp_assoc.
  rewrite <- falg_commutes.
  reflexivity.
Qed.

(*
 The forgetful functor to the underlying category, dropping the structure. 

 --------
 到基础范畴的遗忘函子，丢弃结构。
*)
Program Definition FAlg_Forget `(F : C ⟶ C) : FAlg F ⟶ C := {|
  fobj := fun x => ``x;
  fmap := fun x y f => falg_hom[f]
|}.
