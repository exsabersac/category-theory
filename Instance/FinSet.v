Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(* * * FinSet, the skeletal category of finite sets / * * FinSet，有限集合的骨架范畴 *)

(*
 nLab:      https://ncatlab.org/nlab/show/FinSet
 Wikipedia: https://en.wikipedia.org/wiki/FinSet

 The skeleton of the category of finite sets: the objects are the natural
 numbers, with [n] standing for the canonical n-element set [Fin.t n], and
 the morphisms [m ~> n] are all functions [Fin.t m → Fin.t n].  Hom-setoids
 are pointwise Leibniz equality (via [fun_setoid] over the discrete
 [Fin_Setoid]), so this is an ordinary — non-quotient — category presented
 in the library's setoid discipline.  That FinSet is skeletal — that
 isomorphic objects are equal — is proved in Instance/FinSet/Skeleton.v
 ([FinSet_Skeletal]).

 FinSet is the PROP for commutative monoids: its coproduct-induced monoidal
 structure (tensor on objects is [plus]) makes every object a commutative
 monoid via the codiagonal [id ▽ id] and the empty map.  That monoidal
 assembly, and the [PROP] instance riding on it, need the coherence
 machinery and are not yet built; this file delivers their intended
 inputs:

 - the category itself, with Initial (0), Terminal (1) and COMPUTING
 coproducts: [fin_split] is a structural fixpoint dispatching through
 [Fin.caseS'], so copairings evaluate on closed inputs by [eq_refl]
 (see [fin_split_computes] and [merge_computes] below);
 - the [HomEqProp] and [ObjDecEq] side conditions from
 [Construction/Quotient.v], which universal-property proofs against
 FinSet-like targets require ([Prop]-reflected hom equivalence, and
 axiom-free UIP on objects via [Nat.eq_dec]).

 NOTE on names: [Structure/Cocartesian.v] defines [inl], [inr], [left]
 and [right] for the coproduct calculus, shadowing the sum-type
 constructors, which are therefore qualified [Datatypes.inl] and
 [Datatypes.inr] throughout this file. 

 --------
 nLab：https://ncatlab.org/nlab/show/FinSet
 维基百科：https://en.wikipedia.org/wiki/FinSet

 有限集范畴的骨架：对象是自然数，其中 [n] 代表规范的 n 元集合 [Fin.t n]，态射 [m ~> n] 是所有函数 [Fin.t m → Fin.t n]。Hom-集体是逐点莱布尼茨相等（通过 [fun_setoid] 在离散 [Fin_Setoid] 上），因此这是图书馆的集合范畴范式中呈现的普通——非商——范畴。证明 FinSet 是骨架的——也就是说同构对象相等——在 Instance/FinSet/Skeleton.v（[FinSet_Skeletal]）中进行。FinSet 是交换幺半群的 PROP：其余积诱导的单oidal结构（对象上的张量是 [plus]）通过余对角 [id ▽ id] 和空映射使每个对象成为交换幺半群。该单oidal组合，以及依附于它的 [PROP] 实例，需要一致性机制，目前尚未构建；此文件提供了它们预期的输入：- 类本身，包括初态 (0)、终态 (1) 和计算余积: [fin_split] 是一个结构性不动点，通过 [Fin.caseS'] 进行分发，因此对封闭输入的余配对通过 [eq_refl] 进行求值（参见下文的 [fin_split_computes] 和 [merge_computes]）；
 - 来自 [Construction/Quotient.v] 的 [HomEqProp] 和 [ObjDecEq] 边条件，对于类似 FinSet 的目标进行的泛性质证明是必要的（ZW20WZZ-反射同态等价，以及通过 [Nat.eq_dec] 对对象进行无公理 UIP）。

 名称说明: [Structure/Cocartesian.v] 定义了 [inl]、ZW24WZZ、ZW25WZZ 和 [right] 用于余积演算，覆盖了和求和类型构造函数相对应的名称，因此在本文件中统一被限定为 [Datatypes.inl] 和 [Datatypes.inr]。
*)

(*
 Why the skeleton, and where it leads

 nLab: https://ncatlab.org/nlab/show/FinSet
 nLab: https://ncatlab.org/nlab/show/Lawvere+theory

 The skeletal category of finite sets is the founding object of
 categorical universal algebra.  Lawvere's doctoral dissertation
 (F. W. Lawvere, "Functorial Semantics of Algebraic Theories", 1963)
 built algebraic theories on exactly this category: in the modern
 formulation recorded by nLab, a Lawvere theory is a category equipped
 with an identity-on-objects, strictly power-preserving functor out of
 the opposite of the category of natural numbers and functions between
 them — the opposite of the category defined here — and Lawvere
 theories so presented correspond to finitary monads on Set.  It
 follows that [FinSet]^op is the initial Lawvere theory, the theory of
 no operations that every other theory extends; Instance/FinSet/Lawvere.v
 realizes it in-tree as [FinSetOp_Lawvere], with the base reachability
 hypothesis discharged by [eq_refl] in Theory/Lawvere/Sets.v
 ([FinSetOp_reach]).

 The universal properties run in parallel.  Per nLab, FinSet is the free
 category with finite coproducts on a single object, and dually
 FinSet^op is the free category with finite products on one; the
 commutative-monoid PROP statement of the header traces to Lafont
 (Y. Lafont, "Towards an algebraic theory of Boolean circuits", Journal
 of Pure and Applied Algebra 184, 2003).  By generators and relations,
 FinSet is presented by one multiplication 2 → 1 and one unit 0 → 1
 under the commutative-monoid equations, and it anchors the
 network-theory chain in which cospans of finite sets form the prop for
 special commutative Frobenius monoids and spans the prop for
 bicommutative bimonoids (results of Lack and of Rosebrugh, Sabadini
 and Walters, assembled in Baez, Coya, Rebro, "Props in Network
 Theory", Theory and Applications of Categories 33, 2018) — the
 interconnection algebra discussed in Theory/Algebra/Frobenius.v.

 The footprint extends well beyond algebra.  FinSet is an elementary
 topos whose inclusion into Set is a logical morphism, and the functor
 category from FinSet to Set is the classifying topos for the theory of
 objects (nLab).  Presheaves on FinSet are the augmented symmetric
 simplicial sets of Grandis ("Finite sets and symmetric simplicial
 sets", Theory and Applications of Categories 8, 2001), with the
 simplex category Δ embedding into FinSet.  Covariant presheaves over
 this skeleton are likewise the mathematical universe of abstract
 syntax with variable binding (Fiore, Plotkin, Turi, "Abstract Syntax
 and Variable Binding", LICS 1999): an object n is a context of n free
 variables, morphisms are renamings, and binding signatures acquire
 initial-algebra semantics with a provably correct substitution
 structure — the underpinning of well-scoped De Bruijn
 representations.

 Within this library the skeleton earns its keep for a further,
 concrete reason: it computes.  Objects are literal natural numbers, so
 object equality is decidable — the content of [FinSet_ObjDecEq] —
 and UIP on objects then holds axiom-free by Hedberg's argument, while
 morphisms are honest Coq functions on the standard library's [Fin.t],
 the canonical n-element type of the dependent-types tradition.
 Categorical structure can therefore be made to evaluate, and the
 closed-computation discipline established here by [fin_split] and
 [fin_join] propagates through every satellite: positional product
 codecs [fin_pair] and [fin_unpair] in Instance/FinSet/Product.v,
 enumeration exponential codecs [fin_tabulate] and [fin_apply] in
 Instance/FinSet/Closed.v, counted pullbacks ([FinSet_Pullbacks]) and
 the decidable subobject classifier Ω := 2 in
 Instance/FinSet/Classifier.v, culminating in [FinSet_Topos] of
 Instance/FinSet/Topos.v, whose sanity Examples — [FinSet_Pow_two]
 computing the power object of 2 to be 4 among them — hold by
 [eq_refl]. 

 --------
 为什么是骷髅，以及它通向何方

 nLab:  https://ncatlab.org/nlab/show/FinSet 
 nLab:  https://ncatlab.org/nlab/show/Lawvere+theory有限集的骨架范畴是范畴通用代数的基础对象。Lawvere 的博士论文（F. W. Lawvere, "代数理论的函子语义"，1963）正是在这个范畴上构建了代数理论：在 nLab 所记录的现代表述中，Lawvere 理论是一个范畴，配备有从自然数及其间函数组成的范畴的对偶出发的对对象恒等、严格保持幂的函子——即本文定义的范畴的对偶——并且以这种方式呈现的 Lawvere 理论对应于 Set 上的有限元单子。由此可得 [FinSet] ^op 是初始的劳韦尔理论，即没有运算的理论，每个其他理论都扩展自它；Instance/FinSet/Lawvere.v 在树中将其具体化为 [FinSetOp_Lawvere]，并且基础可达性假设由 Theory/Lawvere/Sets.v 中的 [eq_refl] （[FinSetOp_reach]）解除。通用性质是并行运行的。根据 nLab，FinSet 是在单个对象上具有有限余积的自由范畴，而对偶地，FinSet^op 是在单个对象上具有有限积的自由范畴；标题中的交换单子 PROP 陈述可追溯到 Lafont（Y. Lafont，《Towards an algebraic theory of Boolean circuits》，《纯与应用代数杂志》184, 2003）。通过生成元和关系，
 FinSet 由一个乘法 2 → 1 和一个单位 0 → 1 在交换单元方程下表示，并且它锚定了网络理论链，其中有限集合的余跨度构成特殊交换 Frobenius 单元的道具，并跨越双交换双单元的道具（Lack 以及 Rosebrugh、Sabadini 和 Walters 的结果，汇编在 Baez、Coya、Rebro 的《网络理论中的道具》，类别理论与应用 33, 2018）——在 Theory/Algebra/Frobenius.v 中讨论的互连代数。这一影响远远超出了代数。FinSet 是一个初等拓扑，其包含到 Set 中是一个逻辑态射，而从 FinSet 到 Set 的函子范畴是对象理论的分类拓扑（nLab）。FinSet 上的预层是 Grandis 的增强对称单纯集合（“有限集合与对称单纯集合”，《范畴理论的理论与应用》8, 2001），单纯形范畴 Δ 嵌入到 FinSet 中。该骨架上的协变预层同样是带变量绑定的抽象语法的数学宇宙（Fiore, Plotkin, Turi，《抽象语法与变量绑定》，LICS 1999）：一个对象 n 是 n 个自由变量的上下文，态射是重命名，绑定签名通过带有可证明正确的替换结构获得初代数语义——这是作用良好范围的 De Bruijn 表示的基础。在这个库中，骨架还有另一个具体的理由来证明其存在价值：它会进行计算。对象是字面上的自然数，因此对象的相等性是可判定的——[FinSet_ObjDecEq] 的内容——并且根据 Hedberg 的论证，对对象的 UIP（唯一身份证明）则无需公理即可成立，而态射是标准库 [Fin.t] 上的诚实 Coq 函数，这个类型是依赖类型传统中规范的 n 元类型。因此，可以使范畴结构进行评估，并且由 [fin_split] 和 [fin_join] 在此建立的闭合计算规范会传播到每个卫星：Instance/FinSet/Product.v 中的位置乘积编解码器 [fin_pair] 和 [fin_unpair]，Instance/FinSet/Closed.v 中的枚举指数编解码器 [fin_tabulate] 和 [fin_apply]，计数拉回（[FinSet_Pullbacks]）以及 Instance/FinSet/Classifier.v 中可判定的子对象分类器 Ω := 2，最终在 Instance/FinSet/Topos.v 中形成 [FinSet_Topos]，其合理性示例 — 其中 [FinSet_Pow_two] 计算 2 的幂对象为 4 — 通过 [eq_refl] 得到验证。
*)

Program Definition FinSet : Category := {|
  obj := nat;
  hom := fun m n => Fin.t m → Fin.t n;
  homset := fun m n => fun_setoid (Fin.t m) (Fin.t n);
  id := fun _ i => i;
  compose := fun _ _ _ f g i => f (g i)
|}.
Next Obligation.
  (* compose respects pointwise equality in both arguments. / compose 在两个参数中都遵循逐点相等性。 *)
  intros f f' Hf g g' Hg i.
  rewrite (Hg i); apply Hf.
Qed.

(*
   * ** Side conditions for universal properties

   The hom equivalence of [FinSet] is already a [Prop]-valued pointwise
   equality, so the [Prop] reflection required by soundness inductions is
   the identity in both directions; and objects are natural numbers, whose
   equality is decidable, giving axiom-free UIP on objects. 

   --------
   * ** 泛性质的附加条件

   [FinSet] 的同构等价已经是一个 [Prop] 值的逐点相等，因此可靠性归纳所需的 [Prop] 反射在两个方向上都是恒等；并且对象是自然数，其相等性是可判定的，从而在对象上给出了无公理的 UIP。
*)

#[export] Instance FinSet_HomEqProp : HomEqProp FinSet :=
  Build_HomEqProp FinSet
    (fun m n (f g : Fin.t m → Fin.t n) => ∀ i, f i = g i)
    (fun _ _ _ _ H => H)
    (fun _ _ _ _ H => H).

#[export] Instance FinSet_ObjDecEq : ObjDecEq FinSet := Nat.eq_dec.

(*
   * ** The computing split/join toolkit on [Fin.t (m + n)]

   [fin_split] analyses an element of the canonical (m + n)-element set as
   either an element of the first m or of the last n; [fin_join] is its
   two-sided inverse, built from the standard library's injections [Fin.L]
   and [Fin.R].  [fin_split] is a structural fixpoint on [m] whose
   successor case dispatches through [Fin.caseS'], re-tagging the
   recursive result along [Fin.FS] — deliberately built from primitives
   common to every supported version, avoiding the split/join recursors
   that only the Rocq 9.x standard library provides, so the file also
   compiles on Coq 8.19/8.20.  Both directions REDUCE on closed input —
   the coproduct structure below computes by [eq_refl]. 

   --------
   * ** [Fin.t (m + n)] 上的计算拆分/合并工具包  

   [fin_split] 将一个规范的 (m + n) 元集合的元素分析为  
   要么是前 m 个元素中的一个，要么是后 n 个元素中的一个；[fin_join] 是它的双向逆，由标准库中的注入 [Fin.L] 和 [Fin.R] 构建。[fin_split] 是 [m] 上的一个结构性不动点，其后继情况通过 [Fin.caseS'] 分派——沿 [Fin.FS] 重新标记递归结果——有意用每个受支持版本通用的原语构建，避免使用仅 Rocq 9.x 标准库提供的拆分/合并递归器，因此该文件也能在 Coq 8.19/8.20 上编译。两种方向在封闭输入上都可以 REDUCE ——下面的余积结构通过 [eq_refl] 进行计算。
*)

Fixpoint fin_split {m n : nat} {struct m} :
  Fin.t (m + n) -> (Fin.t m + Fin.t n)%type :=
  match m return Fin.t (m + n) -> (Fin.t m + Fin.t n)%type with
  | O => fun p => Datatypes.inr p
  | S m' => fun p =>
      Fin.caseS' p (fun _ => (Fin.t (S m') + Fin.t n)%type)
        (Datatypes.inl Fin.F1)
        (fun q =>
           match @fin_split m' n q with
           | Datatypes.inl a => Datatypes.inl (Fin.FS a)
           | Datatypes.inr b => Datatypes.inr b
           end)
  end.

Definition fin_join {m n : nat} (s : (Fin.t m + Fin.t n)%type) :
  Fin.t (m + n) :=
  match s with
  | Datatypes.inl a => Fin.L n a
  | Datatypes.inr b => Fin.R m b
  end.

Lemma fin_split_L {m n : nat} (a : Fin.t m) :
  fin_split (Fin.L n a) = Datatypes.inl a.
Proof.
  induction a as [m | m a IH]; simpl.
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma fin_split_R {m n : nat} (b : Fin.t n) :
  fin_split (Fin.R m b) = Datatypes.inr b.
Proof.
  (* Induction on the amount [m] prepended: [Fin.R 0 b] is definitionally [b], and the successor case re-tags along [Fin.FS]. / 关于数额 [m] 的归纳预置：[Fin.R 0 b] 从定义上是 [b]，继承情况则附加 [Fin.FS]。 *)
  induction m as [| m IH]; simpl.
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma fin_join_split {m n : nat} (p : Fin.t (m + n)) :
  fin_join (fin_split p) = p.
Proof.
  revert p; induction m as [| m IH]; intro p.
  - reflexivity.
  - apply (Fin.caseS' p
             (fun p : Fin.t (S m + n) =>
                fin_join (@fin_split (S m) n p) = p)).
    + reflexivity.
    + intro q; specialize (IH q); simpl; revert IH.
      destruct (fin_split q) as [a|b]; simpl; intro IH;
        rewrite IH; reflexivity.
Qed.

Lemma fin_split_join {m n : nat} (s : (Fin.t m + Fin.t n)%type) :
  fin_split (fin_join s) = s.
Proof. destruct s; [apply fin_split_L | apply fin_split_R]. Qed.

(* The computability acceptance test: the analysis reduces by [eq_refl]. / 可计算性接受测试：分析通过 [eq_refl] 进行简化。 *)
Example fin_split_computes :
  @fin_split 2 2 (Fin.FS (Fin.FS Fin.F1)) = Datatypes.inr Fin.F1 := eq_refl.

(** ** Initial and terminal objects / ** 初始对象和终端对象 *)

(* Initiality is terminality in [FinSet^op], so the fields carry the [Terminal] names: [one {x}] here lands in [Fin.t 0 → Fin.t x], the unique (empty) map out of the empty set. / 在 [FinSet^op] 中，初始性就是终端性，因此这些域带有 [Terminal] 名称：[one {x}] 在这里落入 [Fin.t 0 → Fin.t x]，这是从空集出的唯一（空）映射。 *)
#[export] Instance FinSet_Initial : Initial FinSet :=
  @Build_Terminal (FinSet^op) 0%nat
    (fun x (v : Fin.t 0) => Fin.case0 (fun _ => Fin.t x) v)
    (fun x f g i => Fin.case0 (fun j => f j = g j) i).

(* The one-element set is a singleton: every inhabitant is [Fin.F1]. / 单元素集合是单例：每个成员都是 [Fin.F1]。 *)
Lemma fin1_unique (j : Fin.t 1) : j = Fin.F1.
Proof.
  apply (Fin.caseS' j (fun j => j = Fin.F1)).
  - reflexivity.
  - intro j'; exact (Fin.case0 (fun j' => Fin.FS j' = Fin.F1) j').
Qed.

#[export] Instance FinSet_Terminal : @Terminal FinSet :=
  @Build_Terminal FinSet 1%nat
    (fun x (_ : Fin.t x) => Fin.F1)
    (fun x f g i =>
       eq_trans (fin1_unique (f i)) (eq_sym (fin1_unique (g i)))).

(*
   * ** Computable coproducts

   Being cocartesian is being cartesian in [FinSet^op], so the fields reuse
   the [Cartesian] names: [product_obj] is the coproduct object [m + n],
   [fork] is the copairing by case analysis through [fin_split], and
   [exl]/[exr] are the injections [Fin.L]/[Fin.R] (the projections read in
   the opposite category). 

   --------
   * ** 可计算的余积

   在 [FinSet^op] 中，共笛卡尔就是笛卡尔，因此这些字段重用 [Cartesian] 的名称：[product_obj] 是余积对象 [m + n]，[fork] 是通过 [fin_split] 的情况分析进行的共配对，而 [exl] / [exr] 是注入 [Fin.L] / [Fin.R]（在对偶范畴中读取的投影）。
*)

#[export] Program Instance FinSet_Cocartesian : @Cocartesian FinSet := {|
  product_obj := fun m n => (m + n)%nat;
  fork := fun x y z (f : Fin.t y → Fin.t x) (g : Fin.t z → Fin.t x) p =>
    match fin_split p with
    | Datatypes.inl a => f a
    | Datatypes.inr b => g b
    end;
  exl := fun x y => Fin.L y;
  exr := fun x y => Fin.R x
|}.
Next Obligation.
  (* The copairing respects pointwise equality in both arguments. / 共配对在两个参数中都尊重逐点相等。 *)
  intros f f' Hf g g' Hg p.
  destruct (fin_split p); [apply Hf | apply Hg].
Qed.
Next Obligation.
  (*
 The universal property: h ≈ f ▽ g exactly when h recovers f along
 Fin.L and g along Fin.R. 

 --------
 泛性质：当且仅当 h 沿 Fin.L 恢复 f 且沿 Fin.R 恢复 g 时，h ≈ f ▽ g。
*)
  split.
  - intros Hh; split; intro q; simpl.
    + rewrite (Hh (Fin.L _ q)), fin_split_L; reflexivity.
    + rewrite (Hh (Fin.R _ q)), fin_split_R; reflexivity.
  - intros [Hl Hr] p.
    destruct (fin_split p) as [a|b] eqn:Hs.
    + assert (Hp : p = Fin.L z a)
        by (rewrite <- (fin_join_split p), Hs; reflexivity).
      rewrite Hp; apply Hl.
    + assert (Hp : p = Fin.R y b)
        by (rewrite <- (fin_join_split p), Hs; reflexivity).
      rewrite Hp; apply Hr.
Qed.

(*
 Closed copairings evaluated at concrete elements of Fin.t 3, by
 [eq_refl]: the derived merge (▽) of Structure/Cocartesian.v computes over
 this instance.  The two components are chosen to DISAGREE at the routed
 values, so each Example certifies its routing and not merely reduction:
 [Fin.FS Fin.F1] lies in the [Fin.R]-image, and only routing to the
 second component (the identity) returns [Fin.F1] — the first component
 would return [Fin.FS Fin.F1]; dually, [Fin.F1] lies in the
 [Fin.L]-image and must reach the first component to return
 [Fin.FS Fin.F1]. 

 --------
 在 Fin.t 3 的具体元素上评估的封闭共配对，由 [eq_refl]：Structure/Cocartesian.v 的导出合并（▽）在此实例上计算。两个分量被选择为在路由值上产生不一致，因此每个示例验证其路由，而不仅仅是约简：[Fin.FS Fin.F1] 位于 [Fin.R] 的象中，并且只有路由到第二个分量（恒等）才会返回 [Fin.F1] ——第一个分量会返回 [Fin.FS Fin.F1]；相反，[Fin.F1] 位于 [Fin.L] 的象中，必须到达第一个分量才能返回 [Fin.FS Fin.F1]。
*)
Example merge_computes :
  @merge FinSet FinSet_Cocartesian 2%nat 1%nat 2%nat
    (fun _ : Fin.t 1 => Fin.FS Fin.F1) (fun i : Fin.t 2 => i)
    (Fin.FS Fin.F1) = Fin.F1 := eq_refl.

Example merge_computes_inl :
  @merge FinSet FinSet_Cocartesian 2%nat 1%nat 2%nat
    (fun _ : Fin.t 1 => Fin.FS Fin.F1) (fun i : Fin.t 2 => i)
    Fin.F1 = Fin.FS Fin.F1 := eq_refl.
