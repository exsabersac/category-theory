Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Comonad.Core.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(* * * The traced (cowriter, exponent) comonad / * * 被追踪的（共同作者，指数）余单子 *)

(*
 Haskell:   Control.Comonad.Traced (the comonad package)
 Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

 The traced comonad over a monoid (m, mempty, mappend) — Haskell's Traced,
 also called the cowriter or exponent comonad — is the endofunctor m ⇒ −,
 sending x to the functions m → x, with

 extract   h = h mempty                  (evaluate at the neutral trace)
 duplicate h = λ w w', h (mappend w w')  (evaluate under every further
 translation of the context)

 It is dual to the writer monad m × −: the same monoid structure that lets
 a writer computation merge the output it emits lets a traced computation
 split the context it consumes.  Both arise by pushing the monoid m through
 a monoidal functor into the endofunctor category: m × − covariantly
 (giving a monad), m ⇒ − contravariantly (giving a comonad, since
 (m ⇒ −) ○ (m ⇒ −) ≅ (m × m) ⇒ − lets mappend and mempty land as the
 comultiplication δ and the counit ε).  Co-Kleisli arrows (m → x) → y
 consume a value together with all of its monoid translates — the comonad
 of cellular automata (m a grid of offsets) and of monoid-weighted contexts
 generally, with co-Kleisli composition accumulating the offsets.

 Following Theory/Monad.v's [Comonad := @Monad (C^op) (W^op)], the witness
 [Traced_Comonad] below is literally a [Monad] on the opposite category;
 the covariant accessors of Comonad/Core.v then read [extract], [duplicate]
 and [extend] off it definitionally (the *_spec lemmas at the end hold by
 [reflexivity]). 

 --------
 Haskell: Control.Comonad.Traced（comonad 包）
 Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

 单子 (m, mempty, mappend) 上的追踪 comonad——Haskell 的 Traced，也称为 cowriter 或指数 comonad——是函子 m ⇒ −，将 x 发送到函数 m → x，具有

 extract   h = h mempty                  （在中性追踪处求值）
 duplicate h = λ w w', h (mappend w w')  （在上下文的每个进一步变换下求值）它是作家单子 m × − 的对偶：允许作家计算合并它发出的输出的同一个幺半群结构，也让被追踪的计算可以拆分它消耗的上下文。两者都是通过将幺半群 m 推入函子范畴的自函子中产生的：m × − 是协变的（得到一个单子），m ⇒ − 是逆变的（得到一个余单子，因为 (m ⇒ −) ○ (m ⇒ −) ≅ (m × m) ⇒ − 允许 mappend 和 mempty 作为余乘 δ 和余单位 ε）。Co-Kleisli 箭头 (m → x) → y 会连同其所有幺半群变换一起消耗一个值——余单子在元胞自动机中（m 作为偏移网格）以及在一般的幺半群加权上下文中表现出来，其中 co-Kleisli 组合累积偏移量。根据 Theory/Monad.v 中的 [Comonad := @Monad (C^op) (W^op)]，下面的见证 [Traced_Comonad] 实际上是在对偶范畴上的 [Monad]；然后 Comonad/Core.v 的协变访问器按定义读取 [extract]、[duplicate] 和 [extend] （最后的 *_spec 引理通过 [reflexivity] 成立）。
*)

(*
 How much monoid the comonad costs

 Haskell: Control.Comonad.Traced (Kmett's comonad package)
 Paper:   Eilenberg, Moore, "Adjoint functors and triples", Illinois
 Journal of Mathematics 9(3), 1965 (the adjoint monad theorem)

 The exponent functor m ⇒ − is made a comonad by exactly the monoid
 structure on m, and the file keeps the accounting visible: ε
 consumes the unit, δ consumes the multiplication, and each of the
 three comonad laws consumes precisely one monoid law.
 [traced_extract_duplicate] uses only [mempty_left];
 [traced_fmap_extract_duplicate] uses only [mempty_right]; and
 [traced_duplicate_coassoc] uses only [mappend_assoc].  The
 [Proof using] annotations record these dependencies, so the
 correspondence is checked rather than asserted.  Haskell mirrors the
 requirement: the Comonad instance for Traced m exists exactly under
 a Monoid m constraint, and the ComonadTraced class provides
 trace :: m -> w a -> a — run the observation at a chosen
 displacement of the context — as the practical vocabulary.

 The comonad also has an adjoint provenance.  Besides the
 contravariant monoidal push described above, the writer monad m × −
 is left adjoint to m ⇒ −, and whenever a monad has a right adjoint,
 that right adjoint canonically carries a comonad structure whose
 counit and comultiplication are the mates of the monad's unit and
 multiplication, with the Eilenberg–Moore category of the monad
 equivalent to the coalgebras of the comonad compatibly with the
 forgetful functors.  This is the adjoint monad theorem, implicit in
 Eilenberg–Moore (1965) and explicit in Mac Lane and Moerdijk,
 "Sheaves in Geometry and Logic", Thm. 2, p. 249.  Writer and Traced
 are thus paired twice over: dual through the monoid, and adjoint
 through the exponential. 

 --------
 范畴对偶单子的代价有多大

 Haskell：Control.Comonad.Traced（Kmett 的 comonad 包）
 论文：Eilenberg, Moore，《伴随函子与三元组》，伊利诺伊数学杂志 9(3), 1965（伴随单子定理）指数函子 m ⇒ − 正是通过 m 上的幺半群结构成为一个余单子，并且文件保持了会计的可见性：ε 消耗单位元，δ 消耗乘法运算，每一个余单子定律正好消耗一个幺半群定律。[traced_extract_duplicate] 只使用 [mempty_left]；[traced_fmap_extract_duplicate] 只使用 [mempty_right]；而 [traced_duplicate_coassoc] 只使用 [mappend_assoc]。[Proof using] 注释记录了这些依赖关系，因此对应关系是被检查的，而不是被断言的。Haskell 反映了这个要求：Traced m 的 Comonad 实例恰好在 Monoid m 约束下存在，而 ComonadTraced 类提供 trace :: m -> w a -> a——在上下文的选定位移运行观察——作为实际的词汇。余单子也有一个伴随源。除了上面描述的逆变幺半群推动之外，写作单子 m × − 是 m ⇒ − 的左伴随，并且每当单子有右伴随时，该右伴随自然地携带一个余单子结构，其余单位和余乘法是单子的单位和乘法的对应物，单子的 Eilenberg–Moore 范畴与余单子的余代数等价，并且与遗忘函子相容。这就是伴随单子定理，在 Eilenberg–Moore（1965）中隐含，在 Mac Lane 和 Moerdijk 的《几何与逻辑中的层》（Sheaves in Geometry and Logic）中明确提出，第 2 定理，第 249 页。因此，Writer 和 Traced 是双重配对的：通过幺半群是对偶的，通过指数是伴随的。
*)

Section Traced.

(*
   * The section-context monoid: ordinary Coq data — a bare type together
   with a unit, a multiplication, and the three monoid equations as Leibniz
   laws. 

   --------
   * 片段-上下文单元：普通的 Coq 数据 — 一个裸类型，连同一个单位、一个乘法，以及三个作为莱布尼茨定律的单元方程。
*)

Context (m : Type).
Context (mempty : m).
Context (mappend : m → m → m).

Hypothesis mempty_left  : ∀ w : m, mappend mempty w = w.
Hypothesis mempty_right : ∀ w : m, mappend w mempty = w.
Hypothesis mappend_assoc :
  ∀ u v w : m, mappend u (mappend v w) = mappend (mappend u v) w.

(*
   * ** The traced data over raw types, and why the witness is hosted on Sets

   Instance/Coq/Comonad/Env.v hosts the environment comonad on COQ, whose
   morphism equivalence is pointwise Leibniz equality.  For the traced
   functor, four of the seven functor/comonad equations of the corresponding
   raw data below are closed by Coq's definitional beta and eta alone, at
   the full function level (the Leibniz-valued lemmas below, all by
   [reflexivity]).  The remaining three equations are exactly the ones that
   consult the monoid laws, and their Leibniz forms compare functions that
   differ beneath a binder — (λ w', h (mappend mempty w')) against h, and so
   on.  Each of these holds pointwise, which is the restatement the plan
   prescribes for this file (doc/classical-completion-plan.md, Phase 6), and
   is proved below by rewriting the monoid law at the sampled point; the
   Leibniz form itself is out of reach for axiom-free Coq.  So, moreover, is
   the [fmap_respects] field a [Functor] on COQ must carry:
   [coq_traced_map_proper_entails_funext] shows that the very first instance
   of that obligation already implies functional extensionality for
   functions out of m — no inhabitation hypothesis needed, the identity
   trace exhibits it.

   This is precisely the corner named by the plan's Phase 6 risk note,
   together with the sanctioned move, already exercised by the store comonad
   in Instance/Coq/Comonad/Store.v: "if a corner genuinely resists, move
   that single instance to Sets (setoid homs make the law proper-trivial) —
   the deliverable is the comonad witness, not its host category."  The
   bundled witness [Traced_Comonad] accordingly lives on [Sets], where the
   traced object m → x is compared pointwise up to the codomain's ≈ and
   every equation above literally becomes its pointwise restatement.  The
   monoid itself remains the ordinary Coq data of this section, and the
   file keeps its planned location. 

   --------
   * ** 关于原始类型的跟踪数据，以及为什么见证者托管在集合上Instance/Coq/Comonad/Env.v 在 COQ 上承载环境 comonad，其态射等价为逐点 Leibniz 相等。对于 traced 函子，下列对应原始数据中的七个函子/ comonad 方程中的四个，仅靠 Coq 的定义性 beta 和 eta 就在完整函数层级上封闭（下面的 Leibniz 值引理，均由 [reflexivity] 提供）。剩下的三个方程正是那些需要查阅幺半群律的方程，它们的 Leibniz 形式比较的是在绑定器下不同的函数——(λ w', h (mappend mempty w')) 与 h，等等。这些每一个都是逐点成立的，这也是该计划（doc/classical-completion-plan.md，第6阶段）为此文件规定的重述，并且在下文通过在抽样点重写幺半群律进行了证明；勒布尼茨形式对于无公理的 Coq 是无法实现的。同样，COQ 上的 [fmap_respects] 域是一个 [Functor]，必须包含：[coq_traced_map_proper_entails_funext] 显示了该义务的第一个实例已经暗示了从 m 出来的函数的函数外延性——不需要存在性假设，身份迹就展示了它。这正是计划第6阶段风险注释中提到的角落，连同批准的操作，已经由商店余单子在 Instance/Coq/Comonad/Store.v 中执行：“如果某个角落确实抵抗，将该单一实例移到 Sets（等同范畴的 Hom 使其法律本质上平凡）——可交付物是余单子证据，而不是其宿主范畴。” 因此，捆绑的证据 [Traced_Comonad] 存在于 [Sets] 上，其中追踪的对象 m → x 在点对点地与陪域的 ≈ 比较，每个上述方程字面上都变为其点对点表述。该幺半群本身仍然是本节中的普通 Coq 数据，且文件保持其计划的位置。
*)

(** The plan-prescribed action on raw types: post-compose the observation. / 对原始类型的计划规定操作：后组合观察。 *)
Definition coq_traced_map {x y : Type} (f : x → y) (h : m → x) : m → y :=
  λ w, f (h w).

(** The counit on raw types: evaluate at the neutral trace. / 原始类型的余单位：在中性迹上评估。 *)
Definition coq_traced_extract {x : Type} (h : m → x) : x := h mempty.

(** The comultiplication on raw types: evaluate under every translation. / 原始类型上的余乘法：在每个翻译下进行评估。 *)
Definition coq_traced_duplicate {x : Type} (h : m → x) : m → m → x :=
  λ w w', h (mappend w w').

(*
   * Four of the equations are definitional at the function level: beta and
   eta for functions are part of Coq's conversion. 

   --------
   * 四个方程是在函数层面的定义：函数的 beta 和 eta 是 Coq 转换的一部分。
*)

Lemma coq_traced_map_id {x : Type} (h : m → x) :
  coq_traced_map (λ v : x, v) h = h.
Proof. reflexivity. Qed.

Lemma coq_traced_map_comp {x y z : Type} (f : y → z) (g : x → y)
  (h : m → x) :
  coq_traced_map (λ v, f (g v)) h = coq_traced_map f (coq_traced_map g h).
Proof. reflexivity. Qed.

(** Naturality of the counit — the op-read of [fmap_ret]. / 余单位的自然性——[fmap_ret] 的对操作读取。 *)
Lemma coq_traced_extract_natural {x y : Type} (f : x → y) (h : m → x) :
  f (coq_traced_extract h) = coq_traced_extract (coq_traced_map f h).
Proof. reflexivity. Qed.

(** Naturality of the comultiplication — the op-read of [join_fmap_fmap]. / 余乘法的自然性 — [join_fmap_fmap] 的 op-读取。 *)
Lemma coq_traced_duplicate_natural {x y : Type} (f : x → y) (h : m → x) :
  coq_traced_map (coq_traced_map f) (coq_traced_duplicate h)
    = coq_traced_duplicate (coq_traced_map f h).
Proof. reflexivity. Qed.

(*
   * The remaining three equations consult the monoid laws and hold pointwise
   — each is the plan's restatement of the corresponding law at a sampled
   trace. 

   --------
   * 剩下的三个方程参考了幺半群定律，并且在每一点上都成立——每个方程都是该计划在采样轨迹上对应定律的重新表述。
*)

(** Counit law ε ∘ δ ≈ id, pointwise — the op-read of [join_ret]. / 余单位律 ε ∘ δ ≈ id, 点对点 —— [join_ret] 的对偶读法。 *)
Lemma coq_traced_extract_duplicate {x : Type} (h : m → x) (w : m) :
  coq_traced_extract (coq_traced_duplicate h) w = h w.
Proof using mempty_left.
  unfold coq_traced_extract, coq_traced_duplicate.
  now rewrite mempty_left.
Qed.

(** Counit law W ε ∘ δ ≈ id, pointwise — the op-read of [join_fmap_ret]. / 柯单位律 W ε ∘ δ ≈ id，在点上 — [join_fmap_ret] 的对读。 *)
Lemma coq_traced_fmap_extract_duplicate {x : Type} (h : m → x) (w : m) :
  coq_traced_map coq_traced_extract (coq_traced_duplicate h) w = h w.
Proof using mempty_right.
  unfold coq_traced_map, coq_traced_extract, coq_traced_duplicate.
  now rewrite mempty_right.
Qed.

(*
   * Coassociativity W δ ∘ δ ≈ δ ∘ δ, pointwise — the op-read of
   [join_fmap_join]. 

   --------
   * 余结合性 W δ ∘ δ ≈ δ ∘ δ，逐点 — [join_fmap_join] 的操作读取。
*)
Lemma coq_traced_duplicate_coassoc {x : Type} (h : m → x) (a b c : m) :
  coq_traced_map coq_traced_duplicate (coq_traced_duplicate h) a b c
    = coq_traced_duplicate (coq_traced_duplicate h) a b c.
Proof using mappend_assoc.
  unfold coq_traced_map, coq_traced_duplicate.
  now rewrite mappend_assoc.
Qed.

(*
   * The obstruction, machine-checked: the respectfulness a COQ-hosted traced
   functor would owe — at the single instance x := m, with the identity
   trace as the argument — is already the statement of functional
   extensionality for functions out of the monoid (the final conversion
   step is definitional eta).  Restricted functional extensionality is
   independent of Coq's type theory, so no axiom-free [Functor] on COQ can
   carry this action, and the bundled witness below is hosted on [Sets]
   instead. 

   --------
   * 阻碍，机器检查：一个在 COQ 上托管的追踪函子所应有的尊重性 — 在单一实例 x := m 下，取恒等追踪作为参数 — 已经是关于从幺半群出发的函数的函数外延性声明（最终转换步骤是定义上的 eta）。受限的函数外延性独立于 Coq 的类型理论，因此在 COQ 上没有无公理的 [Functor] 能执行此操作，下方的捆绑定的见证则托管在 [Sets] 上。
*)

Lemma coq_traced_map_proper_entails_funext {y : Type}
  (respects : ∀ f g : m → y,
      (∀ v, f v = g v) →
      ∀ h : m → m, coq_traced_map f h = coq_traced_map g h) :
  ∀ f g : m → y, (∀ v, f v = g v) → f = g.
Proof.
  intros f g Hfg.
  exact (respects f g Hfg (λ w, w)).
Qed.

(** ** The traced setoid on [Sets] / ** 在 [Sets] 上的追踪等价类 *)

(*
 A traced value over the raw monoid m is a bare function m → x into the
 setoid x; two of them are equivalent when they agree at every trace, up to
 the codomain's ≈.  This componentwise relation is exactly what makes every
 obligation below pointwise, in contrast to the Leibniz function
 equalities demanded over raw types above.  The monoid needs no setoid of
 its own: it enters only through the (Leibniz) rewriting of its laws at
 sampled points. 

 --------
 一个在原始幺半群 m 上跟踪的值是一个裸函数 m → x 映射到集合等价 x；当两个值在每一个跟踪上都一致（以值域的 ≈ 为准）时，它们是等价的。这种按分量的关系正是使下面的每个义务都是按点的，而不同于上面在原始类型上要求的 Leibniz 函数等式。幺半群自身不需要集合等价：它仅通过在抽样点对其律的（Leibniz）重写进入。
*)

Definition traced_equiv {x : SetoidObject} : crelation (m → carrier x) :=
  λ h k, ∀ w : m, h w ≈ k w.

Arguments traced_equiv {x} _ _ /.

#[local] Obligation Tactic := idtac.

Program Definition traced_obj (x : SetoidObject) : SetoidObject := {|
  carrier := m → carrier x;
  is_setoid := {| equiv := traced_equiv; setoid_equiv := _ |}
|}.
Next Obligation.
  intros x; constructor.
  - intros h w.
    reflexivity.
  - intros h k Hhk w.
    symmetry; apply Hhk.
  - intros h k l Hhk Hkl w.
    etransitivity.
    + apply Hhk.
    + apply Hkl.
Qed.

(** ** The functorial action / ** 函子作用 *)

(*
 Post-composition under the trace: f is applied to the value observed at
 every trace. 

 --------
 迹下的后组合：f 被应用于观察到的每个迹上的值。
*)
Program Definition traced_map {x y : SetoidObject} (f : SetoidMorphism x y) :
  SetoidMorphism (traced_obj x) (traced_obj y) := {|
  morphism := λ h w, f (h w)
|}.
Next Obligation.
  intros x y f h k Hhk w; simpl.
  apply proper_morphism, Hhk.
Qed.

(*
   * [traced_map] respects ≈ pointwise — the field whose COQ counterpart is
   the funext-entailing obligation above; here it is immediate. 

   --------
   *  [traced_map]  尊重 ≈ 点对点 — 其 COQ 对应物是上述包含 funext 的义务；在这里它是直接的。
*)
Lemma traced_map_respects {x y : SetoidObject} (f g : SetoidMorphism x y) :
  (∀ v : carrier x, f v ≈ g v) →
  ∀ h : m → carrier x, traced_equiv (traced_map f h) (traced_map g h).
Proof.
  intros Hfg h w; simpl.
  apply Hfg.
Qed.

Lemma traced_map_id {x : SetoidObject} (h : m → carrier x) :
  traced_equiv (traced_map setoid_morphism_id h) h.
Proof.
  intros w; simpl.
  reflexivity.
Qed.

Lemma traced_map_comp {x y z : SetoidObject}
  (f : SetoidMorphism y z) (g : SetoidMorphism x y) (h : m → carrier x) :
  traced_equiv (traced_map (setoid_morphism_compose f g) h)
               (traced_map f (traced_map g h)).
Proof.
  intros w; simpl.
  reflexivity.
Qed.

(** The traced endofunctor m ⇒ − on [Sets]. / 在 [Sets] 上被追踪的端函子 m ⇒ − 。 *)
Definition TracedF : Sets ⟶ Sets := @Build_Functor Sets Sets
  (λ x : SetoidObject, traced_obj x)
  (λ (x y : SetoidObject) (f : SetoidMorphism x y), @traced_map x y f)
  (λ x y : SetoidObject, @traced_map_respects x y)
  (λ x : SetoidObject, @traced_map_id x)
  (λ (x y z : SetoidObject) (f : SetoidMorphism y z) (g : SetoidMorphism x y),
     @traced_map_comp x y z f g).

(** ** The comonad structure / ** 共单子结构 *)

(** The counit ε: evaluate at the neutral trace. / 余单位 ε：在单位迹上求值。 *)
Program Definition traced_extract {x : SetoidObject} :
  SetoidMorphism (traced_obj x) x := {|
  morphism := λ h, h mempty
|}.
Next Obligation.
  intros x h k Hhk; simpl.
  apply Hhk.
Qed.

(** The comultiplication δ: evaluate under every further translation. / 余乘 δ：在每个进一步的翻译下评估。 *)
Program Definition traced_duplicate {x : SetoidObject} :
  SetoidMorphism (traced_obj x) (traced_obj (traced_obj x)) := {|
  morphism := λ h w w', h (mappend w w')
|}.
Next Obligation.
  intros x h k Hhk w w'; simpl.
  apply Hhk.
Qed.

(** Naturality of the counit — the op-read of [fmap_ret]. / 余单位的自然性——[fmap_ret] 的对操作读取。 *)
Lemma traced_extract_natural {x y : SetoidObject} (f : SetoidMorphism x y)
  (h : m → carrier x) :
  f (traced_extract h) ≈ traced_extract (traced_map f h).
Proof. reflexivity. Qed.

(** Coassociativity W δ ∘ δ ≈ δ ∘ δ — the op-read of [join_fmap_join]. / 共结合性 W δ ∘ δ ≈ δ ∘ δ — [join_fmap_join] 的操作读取。 *)
Lemma traced_duplicate_coassoc {x : SetoidObject} (h : m → carrier x) :
  traced_equiv (traced_map traced_duplicate (traced_duplicate h))
               (traced_duplicate (traced_duplicate h)).
Proof using mappend_assoc.
  intros a b c; simpl.
  now rewrite mappend_assoc.
Qed.

(** Counit law W ε ∘ δ ≈ id — the op-read of [join_fmap_ret]. / 协 counit 定律 W ε ∘ δ ≈ id — [join_fmap_ret] 的对读。 *)
Lemma traced_fmap_extract_duplicate {x : SetoidObject} (h : m → carrier x) :
  traced_equiv (traced_map traced_extract (traced_duplicate h)) h.
Proof using mempty_right.
  intros w; simpl.
  now rewrite mempty_right.
Qed.

(** Counit law ε ∘ δ ≈ id — the op-read of [join_ret]. / 凑单位律 ε ∘ δ ≈ id — [join_ret] 的对读。 *)
Lemma traced_extract_duplicate {x : SetoidObject} (h : m → carrier x) :
  traced_equiv (traced_extract (traced_duplicate h)) h.
Proof using mempty_left.
  intros w; simpl.
  now rewrite mempty_left.
Qed.

(** Naturality of the comultiplication — the op-read of [join_fmap_fmap]. / 余乘法的自然性 — [join_fmap_fmap] 的 op-读取。 *)
Lemma traced_duplicate_natural {x y : SetoidObject} (f : SetoidMorphism x y)
  (h : m → carrier x) :
  traced_equiv (traced_map (traced_map f) (traced_duplicate h))
               (traced_duplicate (traced_map f h)).
Proof.
  intros w w'; simpl.
  reflexivity.
Qed.

(*
   * The comonad witness: per Theory/Monad.v, a comonad on [Sets] IS a monad
   on [Sets^op], so the record is assembled with [Build_Monad] at (Sets^op,
   TracedF^op) — [ret] is the counit and [join] the comultiplication, and
   each monad law is the corresponding lemma above, read through the
   opposite category's reversed composition. 

   --------
   * comonad 见证：根据 Theory/Monad.v，[Sets] 上的 comonad 是 [Sets^op] 上的 monad，因此该记录使用 [Build_Monad] 在 (Sets^op, TracedF^op) 组装 — [ret] 是 counit，[join] 是 comultiplication，每条 monad 定律都是上面的对应引理，通过对偶范畴的反向组合来理解。
*)
Definition Traced_Comonad : @Comonad Sets TracedF :=
  @Build_Monad (Sets^op) (TracedF^op)
    (λ x : SetoidObject, @traced_extract x)           (* ret  = ε *)
    (λ x : SetoidObject, @traced_duplicate x)         (* join = δ *)
    (λ (x y : SetoidObject) (f : SetoidMorphism y x),
       @traced_extract_natural y x f)
    (λ x : SetoidObject, @traced_duplicate_coassoc x)
    (λ x : SetoidObject, @traced_fmap_extract_duplicate x)
    (λ x : SetoidObject, @traced_extract_duplicate x)
    (λ (x y : SetoidObject) (f : SetoidMorphism y x),
       @traced_duplicate_natural y x f).

#[local] Existing Instance Traced_Comonad.

(*
   * The covariant accessors of Comonad/Core.v compute on this witness
   exactly as the plan's skeleton promises: [extract] evaluates at the
   neutral trace, [duplicate] evaluates under every further translation,
   and [extend f] runs the co-Kleisli arrow f on every translate of its
   argument. 

   --------
   * Comonad/Core.v 的协变访问器在这个证明对象上计算，正如计划的框架所承诺的那样：[extract] 在中性迹上求值，[duplicate] 在每一个进一步的翻译下求值，而 [extend f] 在其参数的每一个翻译上运行 co-Kleisli 箭头 f。
*)

Lemma Traced_extract_spec {x : SetoidObject} (h : m → carrier x) :
  extract[TracedF] h = h mempty.
Proof. reflexivity. Qed.

Lemma Traced_duplicate_spec {x : SetoidObject} (h : m → carrier x)
  (w w' : m) :
  duplicate[TracedF] h w w' = h (mappend w w').
Proof. reflexivity. Qed.

Lemma Traced_extend_spec {x y : SetoidObject}
  (f : SetoidMorphism (traced_obj x) y) (h : m → carrier x) (w : m) :
  extend[TracedF] f h w = f (λ w' : m, h (mappend w w')).
Proof. reflexivity. Qed.

End Traced.

(*
 No [#[export] Existing Instance] here: the monoid supply (mempty, mappend,
 and the three laws) is a section premise not determined by the instance
 head [@Comonad Sets (TracedF m)], so a global registration would force
 typeclass resolution to backtrack through undischargeable subgoals.
 Callers apply [Traced_Comonad] with explicit monoid arguments; the
 [#[local] Existing Instance] above already serves the in-section spec
 lemmas. 

 --------
 这里没有 [#[export] 现有实例：单子供应（mempty、mappend，以及三个定律）是一个章节前提，并不是由实例头 [@Comonad Sets (TracedF m)] 决定的，因此全局注册会迫使类型类解析回溯无法解除的子目标。调用者使用显式的单子参数调用 [Traced_Comonad]；上面的 [#[local] 现有实例] 已经作为章节内规范引理使用。
*)
