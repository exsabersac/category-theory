Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Comonad.Core.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The store (costate) comonad / * 存储（余状态）余单子 *)

(*
 nLab:      https://ncatlab.org/nlab/show/store+comonad
 Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

 The store comonad — also called the costate comonad — over a fixed object
 s of “positions” sends x to (s ⇒ x) × s: a store is an observation
 function h from positions to values together with a currently focused
 position s0, with

 extract   (h, s0) = h s0                 (observe at the current focus)
 duplicate (h, s0) = ((λ σ, (h, σ)), s0)  (a store of stores: at every
 position σ, the same
 observation refocused at σ)

 Abstractly it is the comonad F ◯ U of the currying adjunction
 (− × s) ⊣ (s ⇒ −) on a cartesian closed category, dually to the state
 monad U ◯ F = s ⇒ (− × s).  Its coalgebras are the “very well-behaved
 lenses” of functional programming.

 Following Theory/Monad.v's [Comonad := @Monad (C^op) (W^op)], the witness
 [Store_Comonad] below is literally a [Monad] on the opposite category; the
 covariant accessors of Comonad/Core.v then read [extract], [duplicate] and
 [extend] off it definitionally (the *_spec lemmas at the end hold by
 [reflexivity]). 

 --------
 nLab：https://ncatlab.org/nlab/show/store+comonad
 Wikipedia：https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

 存储余范畴——也称为余状态余范畴——在固定对象 s “位置”上，将 x 映射为 (s ⇒ x) × s：一个存储是从位置到值的观测函数 h，加上当前聚焦的位置 s0，满足

 extract   (h, s0) = h s0                 （在当前焦点处观察）
 duplicate (h, s0) = ((λ σ, (h, σ)), s0)  （存储的存储：在每个位置 σ，重新聚焦于 σ 的相同观测）

 抽象地，它是笛卡尔闭范畴上柯里化伴随 (− × s) ⊣ (s ⇒ −) 的余范畴 F ◯ U，与状态单子 U ◯ F = s ⇒ (− × s) 对偶。它的余代数是函数式编程中的“非常良好行为的透镜”。根据 Theory/Monad.v 的 [Comonad := @Monad (C^op) (W^op)]，下面的见证 [Store_Comonad] 实际上是在对偶范畴上的 [Monad]；Comonad/Core.v 的共变访问器随后按定义读取 [extract]、[duplicate] 和 [extend]（最后的 *_spec 引理通过 [reflexivity] 成立）。
*)

(*
 Lenses, grids, and the practical API

 nLab:  https://ncatlab.org/nlab/show/store+comonad
 Paper: O'Connor, “Functor is to Lens as Applicative is to Biplate:
 Introducing Multiplate”, arXiv:1103.2841, 2011

 The one-line remark above about lenses has a precise statement.  A
 coalgebra of this comonad on a carrier a — a costructure map
 a ~> (s ⇒ a) × s satisfying the counit and coaction laws of
 Comonad/Coalgebra.v — amounts to a pair of maps get : a → s and
 put : s × a → a, and the two coalgebra laws are together equivalent
 to the three lens laws: put (get a, a) = a; get (put (σ, a)) = σ;
 and put (τ, put (σ, a)) = put (τ, a).  Coalgebras of the store
 comonad are therefore exactly the lawful (“very well-behaved”)
 lenses of functional programming, a correspondence due to O'Connor
 (November 2010; arXiv:1103.2841, 2011).

 The spatial intuition is a grid of observations with a cursor, and
 it is what makes this comonad the natural home of cellular
 computation.  Conway's Game of Life serves as the guiding example in
 Milewski's exposition (2017).  Piponi's treatment of cellular
 automata works the same idea over a bi-infinite zipper comonad, one
 step of the automaton applying the local rule at every refocusing at
 once — which is [extend] of the rule (2006).  Foner's comonadic
 fixed point evaluates multi-dimensional spreadsheet-like recurrences
 in which every cell observes its own context within the whole
 (Haskell Symposium 2015).

 Kmett's ComonadStore class names the practical vocabulary, and each
 of its names lands on an artifact of this file.  pos reads the
 focused position: here [snd], and [extend] preserves it
 ([Store_extend_pos_spec]).  peek observes at a given position:
 applying [fst], so that [extract] is peek at pos
 ([Store_extract_spec]).  seek repositions the store absolutely: the
 library's [store_seek], whose family over all positions is the
 observation component of [duplicate] ([Store_seek_spec]).
 experiment observes many neighbouring positions at once. 

 --------
 透镜、网格和实用 API

 nLab: https://ncatlab.org/nlab/show/store+comonad 
 论文: O'Connor, “Functor 类似于透镜，Applicative 类似于双板：引入 Multiplate”，arXiv:1103.2841, 2011

 上面关于透镜的一行评论有一个精确的表述。在承载类型 a 上的这个余单子 (comonad) 的一个上代数(coalgebra)——一个代映射 a ~> (s ⇒ a) × s，满足余单子/上代数的 counit 和 coaction 定律——相当于一对映射 get : a → s 和 put : s × a → a，并且两个上代数定律合起来等价于三个透镜定律：put(get a, a) = a；get(put(σ, a)) = σ；以及 put(τ, put(σ, a)) = put(τ, a)。因此，存储余单子的上代数正好是函数式编程中符合法则（“非常良好行为”）的透镜，这一对应关系归功于 O'Connor（2010 年 11 月；arXiv:1103.2841, 2011）。空间直觉是一个带有光标的观察网格，它使这个余单子成为细胞计算的自然归宿。康威的《生命游戏》在Milewski的讲解（2017年）中作为指导示例。Piponi 对细胞自动机的处理在双无限拉链余单子上应用了相同的思路，自动机的每一步在每次重新聚焦时一次性应用局部规则——这就是规则的 [extend]（2006年）。Foner 的余单子固定点评估多维类电子表格的递推，其中每个单元格都观察自己在整体中的上下文（Haskell 研讨会 2015年）。Kmett 的 ComonadStore 类命名了实用的词汇表，它的每一个名称都对应本文件的一个工件。pos 读取焦点位置：这里是 [snd]，而 [extend] 保留它（[Store_extend_pos_spec]）。peek 在给定位置观察：应用 [fst]，使得 [extract] 是在 pos 的 peek（[Store_extract_spec]）。seek 绝对重新定位存储：库中的 [store_seek]，其在所有位置上的族是 [duplicate] 的观察组件（[Store_seek_spec]）。experiment 同时观察许多相邻的位置。
*)

(*
   * ** The store data over raw types, and why the witness is hosted on Sets

   Instance/Coq/Comonad/Env.v hosts the environment comonad on COQ, whose
   morphism equivalence is pointwise Leibniz equality.  For the store
   functor every comonad *equation* of the corresponding raw data likewise
   holds pointwise and definitionally: the [coq_store_*] lemmas below check
   all of them by destructuring alone, with no axiom involved.

   What resists is not any equation but the *setoid respectfulness* of the
   functor action, the [fmap_respects] field a [Functor] on COQ must carry.
   Because a store places the observation function h : s → x inside the
   object, respectfulness at pointwise-= homs asks for Leibniz equality of
   function components given only pointwise-equal inputs, and
   [coq_store_map_proper_entails_funext] shows that the very first instance
   of that obligation already implies functional extensionality for
   functions out of an inhabited s.  The obligation is therefore not merely
   inconvenient: it is out of reach for axiom-free Coq.

   This is precisely the corner named by the plan's Phase 6 risk note
   (doc/classical-completion-plan.md), together with the sanctioned move:
   “if a corner genuinely resists, move that single instance to Sets
   (setoid homs make the law proper-trivial) and record the move in the
   phase PR — the deliverable is the comonad witness, not its host
   category.”  The bundled witness
   [Store_Comonad] accordingly lives on [Sets], where the store object
   carries a componentwise setoid and respectfulness is a one-line
   pointwise argument.  The file keeps its planned location. 

   --------
   * ** 存储数据与原始类型，以及为什么见证在集合上托管

   Instance/Coq/Comonad/Env.v 在 COQ 上托管环境 comonad，其
   态射等价是逐点的 Leibniz 相等。对于存储函子，相应原始数据的每个 comonad *方程* 同样在逐点和定义上成立：下面的 [coq_store_*] 引理仅通过析构就检查了所有这些方程，不涉及任何公理。抵抗的不是任何方程，而是函子作用必须具有的*集合等价尊重性*，COQ 上的 [fmap_respects] 场必须携带 [Functor]。因为存储将观察函数 h : s → x 放置在对象内部，所以逐点等同性的同态上的尊重性要求函数组件在仅给出逐点相等输入的情况下具有 Leibniz 等式，而 [coq_store_map_proper_entails_funext] 显示该义务的第一个实例已经意味着对来自非空 s 的函数的函数外延性。因此，该义务不仅仅是不便：对于无公理的 Coq 而言，它是无法实现的。这正是计划第6阶段风险说明（doc/classical-completion-plan.md）中指出的角落，同时附带批准的操作：
   “如果一个角落确实有抵抗，将该单例移动到集合（setoid homs 使该律成为适当-平凡），并在阶段 PR 中记录该操作——交付成果是 comonad 的见证，而不是其宿主类别。” 因此，绑定的见证 [Store_Comonad] 位于 [Sets] 上，其中存储对象包含逐组件的集合，并且尊重性是单行逐点论证。该文件保持其计划位置。
*)

(*
   * The plan-prescribed action on raw types: apply f to every observation,
   keep the focus. 

   --------
   * 针对原始类型的计划规定动作：对每个观察应用 f，保持焦点。
*)
Definition coq_store_map {s x y : Type} (f : x → y) (p : (s → x) * s) :
  (s → y) * s :=
  match p with (h, s0) => ((λ σ, f (h σ)), s0) end.

(** The counit on raw types: observe at the current focus. / 原始类型的余单位：观察当前焦点。 *)
Definition coq_store_extract {s x : Type} (p : (s → x) * s) : x :=
  match p with (h, s0) => h s0 end.

(** The comultiplication on raw types: refocus at every position. / 原始类型上的余乘法：在每个位置重新聚焦。 *)
Definition coq_store_duplicate {s x : Type} (p : (s → x) * s) :
  (s → (s → x) * s) * s :=
  match p with (h, s0) => ((λ σ, (h, σ)), s0) end.

(*
   * Both functor equations hold pointwise; eta for functions is part of
   Coq's definitional equality, so destructuring the pair suffices. 

   --------
   * 两个函子方程在每一点上都成立；函数的 eta 是 Coq 定义等式的一部分，因此析构该对就足够了。
*)

Lemma coq_store_map_id {s x : Type} (p : (s → x) * s) :
  coq_store_map (λ v : x, v) p = p.
Proof. now destruct p. Qed.

Lemma coq_store_map_comp {s x y z : Type} (f : y → z) (g : x → y)
  (p : (s → x) * s) :
  coq_store_map (λ v, f (g v)) p = coq_store_map f (coq_store_map g p).
Proof. now destruct p. Qed.

(*
   * So do all five comonad equations, stated in the op-read orientation of
   Theory/Monad.v's monad laws (cf. Instance/Coq/Comonad/Env.v). 

   --------
   * 所有五个余单子方程也都成立，它们是以 Theory/Monad.v 的单子律的正向阅读方式陈述的（参见 Instance/Coq/Comonad/Env.v）。
*)

Lemma coq_store_extract_natural {s x y : Type} (f : x → y)
  (p : (s → x) * s) :
  f (coq_store_extract p) = coq_store_extract (coq_store_map f p).
Proof. now destruct p. Qed.

Lemma coq_store_duplicate_coassoc {s x : Type} (p : (s → x) * s) :
  coq_store_map coq_store_duplicate (coq_store_duplicate p)
    = coq_store_duplicate (coq_store_duplicate p).
Proof. now destruct p. Qed.

Lemma coq_store_fmap_extract_duplicate {s x : Type} (p : (s → x) * s) :
  coq_store_map coq_store_extract (coq_store_duplicate p) = p.
Proof. now destruct p. Qed.

Lemma coq_store_extract_duplicate {s x : Type} (p : (s → x) * s) :
  coq_store_extract (coq_store_duplicate p) = p.
Proof. now destruct p. Qed.

Lemma coq_store_duplicate_natural {s x y : Type} (f : x → y)
  (p : (s → x) * s) :
  coq_store_map (coq_store_map f) (coq_store_duplicate p)
    = coq_store_duplicate (coq_store_map f p).
Proof. now destruct p. Qed.

(*
   * The obstruction, machine-checked: the respectfulness a COQ-hosted store
   functor would owe — at the single instance x := s, with the identity
   observation as the store — is already the statement of functional
   extensionality for functions out of s, whenever s is inhabited (the
   final conversion step is definitional eta).  Restricted functional
   extensionality is independent of Coq's type theory, so no axiom-free
   [Functor] on COQ can carry this action, and the bundled witness below
   is hosted on [Sets] instead. 

   --------
   * 阻塞，机器检查：一个在 COQ 托管的存储函子所应具有的尊重性 — 在单个实例 x := s 下，并以身份观测作为存储 — 已经是从 s 出发的函数的函数外延性的陈述，前提是 s 非空（最终转换步骤是定义性的 eta）。有限制的函数外延性独立于 Coq 的类型理论，因此在 COQ 上没有无公理的 [Functor] 可以执行此操作，下方捆绑的证人则托管在 [Sets] 上。
*)

Lemma coq_store_map_proper_entails_funext {s y : Type} (s0 : s)
  (respects : ∀ f g : s → y,
      (∀ v, f v = g v) →
      ∀ p : (s → s) * s, coq_store_map f p = coq_store_map g p) :
  ∀ f g : s → y, (∀ v, f v = g v) → f = g.
Proof.
  intros f g Hfg.
  exact (f_equal fst (respects f g Hfg ((λ σ, σ), s0))).
Qed.

(** ** The store setoid on [Sets] / ** 该商店设于 [Sets] *)

(*
 A store over the setoid s is an ≈-respecting observation map paired with
 a position; two stores are equivalent when the observations agree
 pointwise (up to the codomain's ≈) and the positions agree (up to s's ≈).
 This componentwise relation is exactly what makes every obligation below
 pointwise, in contrast to the Leibniz pairing over raw types above. 

 --------
 集合 s 上的存储是一个≈-保持的观察映射与一个位置的配对；当观察在每一点上都一致（到余域的≈为止）且位置一致（到 s 的≈为止）时，两个存储是等价的。这种按组件的关系正是使得下面的每个义务都是按点的，相对于上面原始类型上的莱布尼茨配对而言。
*)

Definition store_equiv {s x : SetoidObject} :
  crelation (SetoidMorphism s x * carrier s) :=
  λ p q, ((∀ σ : carrier s, fst p σ ≈ fst q σ) * (snd p ≈ snd q))%type.

Arguments store_equiv {s x} _ _ /.

#[local] Obligation Tactic := idtac.

Program Definition store_obj (s x : SetoidObject) : SetoidObject := {|
  carrier := SetoidMorphism s x * carrier s;
  is_setoid := {| equiv := store_equiv; setoid_equiv := _ |}
|}.
Next Obligation.
  intros s x; constructor.
  - intros p; split.
    + intros σ; reflexivity.
    + reflexivity.
  - intros p q [Hh Hs]; split.
    + intros σ; symmetry; apply Hh.
    + now symmetry.
  - intros p q r [Hh Hs] [Hg Ht]; split.
    + intros σ; etransitivity.
      * apply Hh.
      * apply Hg.
    + etransitivity.
      * exact Hs.
      * exact Ht.
Qed.

(** ** The functorial action / ** 函子作用 *)

(*
 Post-composition under the observation map: f is applied to every
 observation, the focus is kept. 

 --------
 在观测图下的后组合：f 应用于每个观测，焦点保持不变。
*)
Program Definition store_map {s x y : SetoidObject} (f : SetoidMorphism x y) :
  SetoidMorphism (store_obj s x) (store_obj s y) := {|
  morphism := λ p, (setoid_morphism_compose f (fst p), snd p)
|}.
Next Obligation.
  intros s x y f p q [Hh Hs]; split.
  - intros σ; simpl.
    apply proper_morphism, Hh.
  - exact Hs.
Qed.

(*
   * [store_map] respects ≈ pointwise — the field whose COQ counterpart is
   the funext-entailing obligation above; here it is immediate. 

   --------
   *  [store_map]  尊重 ≈ 点态 —— 其 COQ 对应物是上面强制要求 funext 的字段；在这里它是直接的。
*)
Lemma store_map_respects {s x y : SetoidObject} (f g : SetoidMorphism x y) :
  (∀ v : carrier x, f v ≈ g v) →
  ∀ p : SetoidMorphism s x * carrier s,
    store_equiv (store_map f p) (store_map g p).
Proof.
  intros Hfg p; split.
  - intros σ; simpl.
    apply Hfg.
  - reflexivity.
Qed.

Lemma store_map_id {s x : SetoidObject}
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_map setoid_morphism_id p) p.
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

Lemma store_map_comp {s x y z : SetoidObject}
  (f : SetoidMorphism y z) (g : SetoidMorphism x y)
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_map (setoid_morphism_compose f g) p)
              (store_map f (store_map g p)).
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

(** The store endofunctor (s ⇒ −) × s on [Sets]. / 在 [Sets] 上的存储 endofunctor (s ⇒ −) × s 。 *)
Definition StoreF (s : SetoidObject) : Sets ⟶ Sets := @Build_Functor Sets Sets
  (λ x : SetoidObject, store_obj s x)
  (λ (x y : SetoidObject) (f : SetoidMorphism x y), @store_map s x y f)
  (λ x y : SetoidObject, @store_map_respects s x y)
  (λ x : SetoidObject, @store_map_id s x)
  (λ (x y z : SetoidObject) (f : SetoidMorphism y z) (g : SetoidMorphism x y),
     @store_map_comp s x y z f g).

(** ** The comonad structure / ** 共单子结构 *)

(** The counit ε: observe at the current focus. / 协同单位 ε：观察当前焦点。 *)
Program Definition store_extract {s x : SetoidObject} :
  SetoidMorphism (store_obj s x) x := {|
  morphism := λ p, fst p (snd p)
|}.
Next Obligation.
  intros s x p q [Hh Hs]; simpl.
  etransitivity.
  - apply Hh.
  - now apply proper_morphism.
Qed.

(* Refocusing: pair the observation map with every position — the observation component of [duplicate]. / 重新聚焦：将观察图与每个位置配对——[duplicate] 的观察组件。 *)
Program Definition store_seek {s x : SetoidObject} (h : SetoidMorphism s x) :
  SetoidMorphism s (store_obj s x) := {|
  morphism := λ σ, (h, σ)
|}.
Next Obligation.
  intros s x h σ τ Hστ; split.
  - intros ρ; reflexivity.
  - exact Hστ.
Qed.

(** The comultiplication δ: a store of stores, refocused at every position. / 余乘 δ：一个存储的存储，在每个位置都重新聚焦。 *)
Program Definition store_duplicate {s x : SetoidObject} :
  SetoidMorphism (store_obj s x) (store_obj s (store_obj s x)) := {|
  morphism := λ p, (store_seek (fst p), snd p)
|}.
Next Obligation.
  intros s x p q [Hh Hs]; split.
  - intros σ; split.
    + intros τ; apply Hh.
    + reflexivity.
  - exact Hs.
Qed.

(** Naturality of the counit — the op-read of [fmap_ret]. / 余单位的自然性——[fmap_ret] 的对操作读取。 *)
Lemma store_extract_natural {s x y : SetoidObject} (f : SetoidMorphism x y)
  (p : SetoidMorphism s x * carrier s) :
  f (store_extract p) ≈ store_extract (store_map f p).
Proof. reflexivity. Qed.

(** Coassociativity W δ ∘ δ ≈ δ ∘ δ — the op-read of [join_fmap_join]. / 共结合性 W δ ∘ δ ≈ δ ∘ δ — [join_fmap_join] 的操作读取。 *)
Lemma store_duplicate_coassoc {s x : SetoidObject}
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_map store_duplicate (store_duplicate p))
              (store_duplicate (store_duplicate p)).
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

(** Counit law W ε ∘ δ ≈ id — the op-read of [join_fmap_ret]. / 协 counit 定律 W ε ∘ δ ≈ id — [join_fmap_ret] 的对读。 *)
Lemma store_fmap_extract_duplicate {s x : SetoidObject}
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_map store_extract (store_duplicate p)) p.
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

(** Counit law ε ∘ δ ≈ id — the op-read of [join_ret]. / 凑单位律 ε ∘ δ ≈ id — [join_ret] 的对读。 *)
Lemma store_extract_duplicate {s x : SetoidObject}
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_extract (store_duplicate p)) p.
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

(** Naturality of the comultiplication — the op-read of [join_fmap_fmap]. / 余乘法的自然性 — [join_fmap_fmap] 的 op-读取。 *)
Lemma store_duplicate_natural {s x y : SetoidObject} (f : SetoidMorphism x y)
  (p : SetoidMorphism s x * carrier s) :
  store_equiv (store_map (store_map f) (store_duplicate p))
              (store_duplicate (store_map f p)).
Proof.
  split.
  - intros σ; reflexivity.
  - reflexivity.
Qed.

(*
   * The comonad witness: per Theory/Monad.v, a comonad on [Sets] IS a monad
   on [Sets^op], so the record is assembled with [Build_Monad] at (Sets^op,
   (StoreF s)^op) — [ret] is the counit and [join] the comultiplication,
   and each monad law is the corresponding lemma above, read through the
   opposite category's reversed composition. 

   --------
   * comonad 见证：根据 Theory/Monad.v，[Sets] 上的 comonad 是 [Sets^op] 上的 monad，因此该记录使用 [Build_Monad] 在 (Sets^op, (StoreF s)^op) 处组装——[ret] 是余单位，[join] 是共乘法，并且每条 monad 定律都是上面的对应引理，通过对立范畴的逆向组合来阅读。
*)
#[export] Instance Store_Comonad (s : SetoidObject) :
  @Comonad Sets (StoreF s) :=
  @Build_Monad (Sets^op) ((StoreF s)^op)
    (λ x : SetoidObject, @store_extract s x)          (* ret  = ε *)
    (λ x : SetoidObject, @store_duplicate s x)        (* join = δ *)
    (λ (x y : SetoidObject) (f : SetoidMorphism y x),
       @store_extract_natural s y x f)
    (λ x : SetoidObject, @store_duplicate_coassoc s x)
    (λ x : SetoidObject, @store_fmap_extract_duplicate s x)
    (λ x : SetoidObject, @store_extract_duplicate s x)
    (λ (x y : SetoidObject) (f : SetoidMorphism y x),
       @store_duplicate_natural s y x f).

(*
   * The covariant accessors of Comonad/Core.v compute on this witness
   exactly as the plan's skeleton promises: [extract] observes at the
   focus, [duplicate] refocuses at every position, and [extend f] runs the
   co-Kleisli arrow f on every refocused store while keeping the focus. 

   --------
   * Comonad/Core.v 的协变访问器在这个证据上正如计划的骨架所承诺的那样进行计算：[extract] 在焦点处进行观察，[duplicate] 在每个位置重新聚焦，[extend f] 在保持焦点的同时对每个重新聚焦的存储运行 co-Kleisli 箭头 f。
*)

Lemma Store_extract_spec {s x : SetoidObject}
  (h : SetoidMorphism s x) (s0 : carrier s) :
  extract[StoreF s] (h, s0) = h s0.
Proof. reflexivity. Qed.

Lemma Store_duplicate_spec {s x : SetoidObject}
  (h : SetoidMorphism s x) (s0 : carrier s) :
  duplicate[StoreF s] (h, s0) = (store_seek h, s0).
Proof. reflexivity. Qed.

Lemma Store_seek_spec {s x : SetoidObject}
  (h : SetoidMorphism s x) (s0 σ : carrier s) :
  fst (duplicate[StoreF s] (h, s0)) σ = (h, σ).
Proof. reflexivity. Qed.

Lemma Store_extend_spec {s x y : SetoidObject}
  (f : SetoidMorphism (store_obj s x) y) (h : SetoidMorphism s x)
  (s0 σ : carrier s) :
  fst (extend[StoreF s] f (h, s0)) σ = f (h, σ).
Proof. reflexivity. Qed.

Lemma Store_extend_pos_spec {s x y : SetoidObject}
  (f : SetoidMorphism (store_obj s x) y) (h : SetoidMorphism s x)
  (s0 : carrier s) :
  snd (extend[StoreF s] f (h, s0)) = s0.
Proof. reflexivity. Qed.
