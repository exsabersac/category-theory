Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Hypergraph.Spider.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Instance.Ab.Monoidal.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Generalizable All Variables.

(* * * ⨁ₙ A^{⊗n}: words modulo multilinearity, and the direct sum of the tensor powers / * * ⨁ₙ A^{⊗n}: 单词模多线性，以及张量幂的直和 *)

(*
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, §VI.4, Exercise 4(a), printed p. 146 (PDF
 p. 155) — maclane:VI.4:ex4
 Book: Riehl, “Category Theory in Context”, Example 5.5.7(ii), printed
 p. 205 (PDF p. 225) — riehl:5.5:example7
 nLab: https://ncatlab.org/nlab/show/tensor+algebra
 nLab: https://ncatlab.org/nlab/show/direct+sum
 Wikipedia: https://en.wikipedia.org/wiki/Tensor_algebra

 WHAT THE BOOKS SAY, read from the page image and the PDF.  Mac Lane,
 Exercise 4: “The adjunction ⟨F, G, φ⟩ : Ab ⇀ Rng with G the functor
 ”forget the multiplication in a ring“ defines a monad T in Ab.  (a)
 Give a direct description of this monad, like that in the text for W,
 with Xⁿ replaced by the n-fold tensor power and coproduct ∐ by the
 (infinite) direct sum of abelian groups.”  Riehl, Example 5.5.7(ii):
 “The induced monad on Ab is the free monoid monad TA := ⨁_{n≥0}
 A^{⊗n}”.  This file is the abelian-group half of (a), with nothing of
 rings in it: the group ⨁ₙ A^{⊗n} in two readings, and the theorem
 that they are one.  Instance/Rng/FreeMonad/Words.v proves T A
 isomorphic to it and reads η, μ and T f through the isomorphism.

 WORDS MODULO MULTILINEARITY.  [TWAb A] is the formal sums [TWTerm A]
 of words over A (lists of elements) modulo [tw_eq]: the abelian-group
 laws, congruence for + and −, and, in each letter of a word,
 saturation under A's own ≈ ([twe_letter]) and additivity
 ([twe_lin]).  Reflexivity is derived ([tw_refl]), as in
 Instance/Rng/Free.v and Instance/Ab/Tensor.v, so every induction on
 [tw_eq] has ten cases.  [tw_eq] is a [Prop], so the [PropEquiv] field
 an abelian group carries since PR #1320 is the relation's own mirror.
 A function on words that respects each letter and is additive in each
 extends to a homomorphism out of [TWAb A] ([tw_ext], which computes on
 words, [tw_ext_word]): the universal property of the presentation.
 Juxtaposition on the left by a word, [tw_lmul], is here with its laws
 because the injections below are built from it; the ring is Words.v's.
 Its additivity on the right is Instance/CMon/Biproduct.v's middle-four
 interchange [cmon_plus_interchange] at [TWAb], not a local copy.

 THE LITERAL DIRECT SUM.  The n-fold tensor powers are not a new
 construction: they are Structure/Monoidal/Hypergraph/Spider.v's
 [tpower] at Instance/Ab/Monoidal.v's [Ab_Monoidal], written A ^⨂ n,
 with A^{⊗0} the unit [ZAb] (ℤ) and A^{⊗(n+1)} = A ⊗ A^{⊗n},
 Instance/Ab/Tensor.v's [AbTensor], both at [eq_refl]
 ([tpower_ab_zero], [tpower_ab_succ]).  The shared route costs eight
 modules: the imports of this file load 64 [Category] modules with
 Spider.v and 56 without it (Print Libraries, compared by script); a
 local fixpoint would be the same family by [eq_refl] and was not
 written.  [tw_pure w] is a word as the pure tensor a₁ ⊗ (… ⊗ (aₙ ⊗ 1))
 of its length; the injections [tw_iota n : A^{⊗n} → TWAb A] come from
 the tensor's universal property ([tensor_ump]), degree 0 by the
 integer multiples of the empty word ([tw_iota0], through
 Instance/Ab/Monoidal.v's [zsmul]), with ι_{n+1}(a ⊗ x) = ⟨a⟩ · ιₙ x at
 [eq_refl] ([tw_iota_gen]) and every word the image of its pure tensor
 at ≈ ([tw_word_iota]).  The copairing [tw_desc] of a family ιₙ :
 A^{⊗n} → c computes on words ([tw_desc_word]); with [tw_desc_iota]
 (the copairing composed with ιₙ is the n-th map, at ≈) and
 [tw_desc_unique] it gives [TW_is_tensor_coproduct : IsIndexedCoproduct
 (fun n => A ^⨂ n) (TWAb A) tw_iota], Structure/Limit/Coproduct.v's
 class in Ab: Mac Lane's “(infinite) direct sum of the n-fold tensor
 powers”, literally.  The copairing respects a letter and is additive
 in it by an induction on the prefix of the word generalized over the
 whole family ([tw_shift], [tw_desc_letter], [tw_desc_lin]), so no
 transport along the length of a word is ever needed.  Read at c := A,
 those two lemmas also say that a family of homomorphisms
 νₙ : A^{⊗n} → A is a function on words respecting each letter and
 additive in each, the form in which Instance/Rng/FreeMonad/System.v
 states Mac Lane's systems.

 STRENGTHS.  Every [Example] holds at [eq_refl], and
 Test/ProbeFreeRing474.v restates each one (C55 to C59).  Stated at ≈:
 [tw_word_iota] and [tw_desc_iota], refused at [eq_refl] at a variable
 (R21, R20) and false at Leibniz = at an explicit instance (C103, C104),
 and the uniqueness [tw_desc_unique], whose hypothesis is at ≈.  Three
 lemmas are Leibniz equalities, stronger than ≈: [tw_lmul_app],
 [tw_lmul_nil] and [tw_desc_lmul] (juxtaposition by one letter shifts
 the family).  Six proofs end [Defined] and eighteen [Qed] (counted by
 token).  Five [Defined]s are load-bearing, measured by closing each
 alone [Qed] in a renamed copy of #474's five files and the probe and
 naming the first command that then stops: [tw_ext] ([tw_ext_word]),
 [tw_iota0] ([tw_word_iota]), [tw_lmul1_bilin] ([tw_iota_gen]),
 [ts_gen_hom] ([tw_desc_letter]) and [tw_desc] ([tw_desc_iota]);
 [TW_is_tensor_coproduct] is [Defined] by the data convention only
 (closed [Qed], nothing stops).

 UNIVERSES, read off [About] (every name, by script).  Every name is
 universe polymorphic, with no [Set] but strict lower bounds and with
 caps of the standard library's global levels only.  Thirty-nine names
 bind three levels (the inductives [TWTerm] and [tw_eq] with their
 constructors bind A's three), six bind four ([tw_Setoid],
 [tw_eq_Equivalence], the eliminators [TWTerm_rect] and [TWTerm_rec],
 [tw_ext_fun] and [tw_ext_respects]), fourteen bind five ([TWAb],
 [tw_lmul1_bilin], [ts_gen_hom], the copairing's nine and the extension's
 two) and [TW_is_tensor_coproduct] six.  Nothing in this file is
 annotated, as in Instance/Ab/Tensor.v: the levels are inferred, and on
 Coq 8.19.2 and 8.20.1 every name binds the same levels as on Rocq 9.1.1
 (FreeMonad.v's header).  One equation, [u0 = u2], in eleven names: the
 nine copairing names of the section [Desc] ([tw_shift] to
 [tw_desc_unique]) and [tw_ext] with [tw_ext_word].  Its cause is
 inherent: those maps run from A's words into c in ONE [Ab], whose
 objects [AbObject@{p p p}] share their carrier level, so A's carrier
 level and c's are identified, while the two object levels stay free.
 [TW_is_tensor_coproduct] itself carries no equation.

 NOT DELIVERED.  A general [HasIndexedCoproducts Ab]: this is the
 coproduct of one family, the tensor powers of one A (the same
 construction over tagged elements would give the general one; not
 attempted).  A normal form for [tw_eq], hence no decision procedure
 and no basis. 

 --------
 书籍：Mac Lane，《为工作数学家准备的范畴论》，第2版，Springer GTM 5, 1998, 第VI.4节，练习4(a)，印刷版第146页（PDF第155页） — maclane:VI.4:ex4
 书籍：Riehl，《上下文中的范畴论》，例5.5.7(ii)，印刷版第205页（PDF第225页） — riehl:5.5:example7
 nLab: https://ncatlab.org/nlab/show/tensor+algebra
 nLab: https://ncatlab.org/nlab/show/direct+sum
 维基百科: https://en.wikipedia.org/wiki/Tensor_algebra书中所说的内容，从页面图片和 PDF 中阅读。Mac Lane，练习 4：“伴随 ⟨F, G, φ⟩ : Ab ⇀ Rng，其中 G 是将环中的乘法‘遗忘’的函子，在 Ab 中定义了一个单子 T。 (a) 给出这个单子的直接描述，就像文本中对 W 的描述一样，用 Xⁿ 替换 n 次张量幂，用直和 ∐ 替换阿贝尔群的（无限）直和。” Riehl，例 5.5.7(ii)：“在 Ab 上诱导的单子是自由幺半群单子 TA := ⨁_{n≥0} A^{⊗n}。” 这个文件是 (a) 的阿贝尔群部分，里面没有环的内容：群 ⨁ₙ A^{⊗n} 的两种读法，以及它们相同的定理。Instance/Rng/FreeMonad/Words.v 证明了 T A 同构于它，并通过同构来读取 η、μ 和 T f。单词模多重线性。[TWAb A] 是形式和 [TWTerm A] 的单词（元素列表）模 [tw_eq]：阿贝尔群定律，对于 + 和 − 的合同，以及在单词的每个字母中，在 A 自身的 ≈（[twe_letter]）下的饱和性和加法性（[twe_lin]）。反身性是导出的（[tw_refl]），如在 Instance/Rng/Free.v 和 Instance/Ab/Tensor.v 中，所以对 [tw_eq] 的每个归纳有十种情况。[tw_eq] 是一个 [Prop]，因此 [PropEquiv] 的字段由于 PR #1320 是关系自身的镜像而承载阿贝尔群。在单词上尊重每个字母并在每个字母上可加的函数，可扩展为 [TWAb A] 的同态（[tw_ext]，在单词上进行计算，[tw_ext_word]）：表示的普遍性质。左侧由一个单词 [tw_lmul] 进行并列，原因在于下方的注入是由它构建的；该环是 Words.v 的。右侧的加法性是 Instance/CMon/Biproduct.v 的 middle-four 交换 [cmon_plus_interchange] 于 [TWAb]，而非本地副本。字面直接和。n 次张量幂不是一个新的构造：它们是 Structure/Monoidal/Hypergraph/Spider.v 的 [tpower]，在 Instance/Ab/Monoidal.v 的 [Ab_Monoidal] 中写作 A ^⨂ n，其中 A^{⊗0} 是单位 [ZAb]（ℤ），A^{⊗(n+1)} = A ⊗ A^{⊗n}，Instance/Ab/Tensor.v 的 [AbTensor]，两者都在 [eq_refl]（[tpower_ab_zero]，[tpower_ab_succ]）。共享路径成本为八个模块：此文件的导入加载了 64 个 [Category] 模块带 Spider.v，56 个不带（通过脚本比较 Print Libraries）；局部不动点将是 [eq_refl] 的相同系列，但未被编写。[tw_pure w] 是一个词，表示其长度的纯张量 a₁ ⊗ (… ⊗ (aₙ ⊗ 1))；注入映射 [tw_iota n : A^{⊗n} → TWAb A] 来源于张量的普遍性质 ([tensor_ump])，在整数倍空词 ([tw_iota0]，通过 Instance/Ab/Monoidal.v 的 [zsmul]) 下为 0 次，且有 ι_{n+1}(a ⊗ x) = ⟨a⟩ · ιₙ x 在 [eq_refl] ([tw_iota_gen])，每个词都是其纯张量在 ≈ ([tw_word_iota]) 的像。族 ιₙ: A^{⊗n} → c 的共配对 [tw_desc] 在词上的计算为 ([tw_desc_word])；与 [tw_desc_iota] （共配对与 ιₙ 组合是第 n 个映射，在 ≈）和 [tw_desc_unique]，给出了 [TW_is_tensor_coproduct : IsIndexedCoproduct (fun n => A ^⨂ n) (TWAb A) tw_iota]，Structure/Limit/Coproduct.v 中 Ab 类：Mac Lane 的“n 重张量幂的（无限）直和”，字面意思。共配对尊重字母，并且通过对单词前缀的归纳在其上是可加的，该归纳推广到整个族（[tw_shift]、[tw_desc_letter]、[tw_desc_lin]），因此从不需要沿单词长度进行传输。在 c := A 处读取时，这两个引理还表明，一个同态族 νₙ : A^{⊗n} → A 是一个对单词的函数，尊重每个字母并在每个字母上是可加的，这正是 Instance/Rng/FreeMonad/System.v 中陈述 Mac Lane 系统的形式。优势。每个 [Example] 在 [eq_refl] 上成立，并且 Test/ProbeFreeRing474.v 重述了每一个（C55 到 C59）。在大约处表述为：[tw_word_iota] 和 [tw_desc_iota]，在 [eq_refl] 处被拒绝于一个变量（R21, R20），并且在 Leibniz = 上在一个明确实例（C103, C104）处为假，以及唯一性 [tw_desc_unique]，其假设大约在。三个引理是 Leibniz 等式，比大约更强：[tw_lmul_app]、[tw_lmul_nil] 和 [tw_desc_lmul]（通过一个字母的并列移动家族）。六个证明以 [Defined] 结束，十八个以 [Qed] 结束（按记号计数）。五个 [Defined] 是承重的，通过在 #474 的五个文件的重命名副本中单独关闭每个 [Qed] 并探查，然后命名第一个停止的命令来测量：[tw_ext] ([tw_ext_word])、[tw_iota0] ([tw_word_iota])、[tw_lmul1_bilin] ([tw_iota_gen])、[ts_gen_hom] ([tw_desc_letter]) 和 [tw_desc] ([tw_desc_iota])；[TW_is_tensor_coproduct] 仅通过数据约定被认为是 [Defined]（关闭 [Qed]，没有任何停止）。UNIVERSES，按 [About] 列出（每个名称按脚本）。每个名称都是多态宇宙，没有 [Set]，但有严格的下界，并且仅限于标准库的全局级别上限。三十九个名称绑定三个级别（归纳类型 [TWTerm] 和 [tw_eq] 及其构造函数绑定 A 的三个级别），六个绑定四个级别（[tw_Setoid]、[tw_eq_Equivalence]、消解器 [TWTerm_rect] 和 [TWTerm_rec]、[tw_ext_fun] 和 [tw_ext_respects]），十四个绑定五个级别（[TWAb]、[tw_lmul1_bilin]、[ts_gen_hom]、协对的九个和扩展的两个）和 [TW_is_tensor_coproduct] 六个。在此文件中没有任何注释，就像在 Instance/Ab/Tensor.v 中一样：级别是推断出来的，并且在 Coq 8.19.2 和 8.20.1 上，每个名称绑定的级别与 Rocq 9.1.1（FreeMonad.v 的头部）上相同。一个方程，[u0 = u2]，在十一种名称中：本节[Desc]的九个配对名称（[tw_shift]至[tw_desc_unique]）以及[tw_ext]与[tw_ext_word]。其原因是固有的：这些映射从A的话语映射到单个[Ab]中的c，其对象[AbObject@{p p p}]共享它们的承载层，因此A的承载层和c的承载层被识别，而两个对象层保持自由。[TW_is_tensor_coproduct]本身不承载方程。

 未交付。一般的[HasIndexedCoproducts Ab]：这是一个族的余积，一个A的张量幂（在带标签的元素上进行相同构造将给出一般情况；未尝试）。[tw_eq]的规范形式，因此没有判定过程，也没有基。
*)

(* ------------------------------------------------------------------------ *)
(* * ** Formal sums of words, modulo multilinearity in each letter / * ** 词的形式和，对每个字母的多重线性取模 *)

Section Words.

Context (A : AbObject).

Local Notation L := (carrier (cmon_setoid A)).

Inductive TWTerm : Type :=
  | tw_word : list L → TWTerm
  | tw_zero : TWTerm
  | tw_plus : TWTerm → TWTerm → TWTerm
  | tw_neg  : TWTerm → TWTerm.

(* The congruence: the abelian-group laws, congruence for the two formers, and in each letter of a word saturation under A's own `≈` and additivity. Reflexivity is derived ([tw_refl]). / 同余：阿贝尔群定律，对于前两个的同余，以及在一个词的每个字母中在 A 自己的 `≈` 下的饱和性和可加性。自反性是推导出来的（[tw_refl]）。 *)
Inductive tw_eq : TWTerm → TWTerm → Prop :=
  | twe_letter (u v : list L) {a b : L} :
      a ≈ b → tw_eq (tw_word (u ++ a :: v)) (tw_word (u ++ b :: v))
  | twe_lin (u v : list L) (a b : L) :
      tw_eq (tw_word (u ++ cmon_plus A a b :: v))
            (tw_plus (tw_word (u ++ a :: v)) (tw_word (u ++ b :: v)))
  | twe_plus {s s' t t'} :
      tw_eq s s' → tw_eq t t' → tw_eq (tw_plus s t) (tw_plus s' t')
  | twe_neg {s s'} : tw_eq s s' → tw_eq (tw_neg s) (tw_neg s')
  | twe_assoc (s t u : TWTerm) :
      tw_eq (tw_plus (tw_plus s t) u) (tw_plus s (tw_plus t u))
  | twe_comm (s t : TWTerm) : tw_eq (tw_plus s t) (tw_plus t s)
  | twe_zero_l (s : TWTerm) : tw_eq (tw_plus tw_zero s) s
  | twe_neg_l (s : TWTerm) : tw_eq (tw_plus (tw_neg s) s) tw_zero
  | twe_sym {s t} : tw_eq s t → tw_eq t s
  | twe_trans {s t u} : tw_eq s t → tw_eq t u → tw_eq s u.

Lemma tw_refl (s : TWTerm) : tw_eq s s.
Proof.
  induction s as [ w | | s IHs t IHt | s IHs ].
  - exact (twe_trans (twe_sym (twe_zero_l (tw_word w)))
                     (twe_zero_l (tw_word w))).
  - exact (twe_trans (twe_sym (twe_zero_l tw_zero)) (twe_zero_l tw_zero)).
  - exact (twe_plus IHs IHt).
  - exact (twe_neg IHs).
Qed.

Lemma tw_eq_Equivalence : Equivalence tw_eq.
Proof.
  constructor.
  - exact tw_refl.
  - exact (fun s t => twe_sym).
  - exact (fun s t u => twe_trans).
Qed.

Definition tw_Setoid : Setoid TWTerm := {|
  equiv := tw_eq;
  setoid_equiv := tw_eq_Equivalence
|}.

Definition TWAb : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := TWTerm; is_setoid := tw_Setoid |};
    cmon_zero := tw_zero;
    cmon_plus := tw_plus;
    cmon_plus_respects := fun _ _ Hs _ _ Ht => twe_plus Hs Ht;
    cmon_plus_assoc := twe_assoc;
    cmon_plus_comm := twe_comm;
    cmon_plus_zero_l := twe_zero_l;
    (*
 [tw_eq] IS a [Prop]-valued relation, so it is its own [Prop]
 mirror and both implications are the identity. 

 --------
 [tw_eq] 是一个 [Prop] 值的关系，所以它是其自身的 [Prop] 镜像，并且两个蕴含都是恒等式。
*)
    cmon_prop := @PropEquiv_of_relation _ tw_Setoid tw_eq
                   (fun _ _ h => h) (fun _ _ h => h)
  |};
  ab_neg := tw_neg;
  ab_neg_respects := fun _ _ Hs => twe_neg Hs;
  ab_neg_left := twe_neg_l
|}.

Definition tw_eq_of_eq {s t : TWTerm} (e : s = t) : tw_eq s t :=
  match e with eq_refl => tw_refl s end.

(* Juxtaposition on the left by a word, extended additively. / 左侧的并列，通过词语进行，附加扩展。 *)
Fixpoint tw_lmul (w : list L) (t : TWTerm) : TWTerm :=
  match t with
  | tw_word v => tw_word (w ++ v)
  | tw_zero => tw_zero
  | tw_plus s t => tw_plus (tw_lmul w s) (tw_lmul w t)
  | tw_neg s => tw_neg (tw_lmul w s)
  end.

Lemma tw_lmul_app (w v : list L) (t : TWTerm) :
  tw_lmul (w ++ v) t = tw_lmul w (tw_lmul v t).
Proof.
  induction t as [ x | | s IHs t IHt | s IHs ]; simpl.
  - rewrite app_assoc. reflexivity.
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

Lemma tw_lmul_nil (t : TWTerm) : tw_lmul nil t = t.
Proof.
  induction t as [ x | | s IHs t IHt | s IHs ]; simpl;
    [ reflexivity | reflexivity | rewrite IHs, IHt | rewrite IHs ];
    reflexivity.
Qed.

Lemma tw_lmul_respects_r (w : list L) (t t' : TWTerm) :
  tw_eq t t' → tw_eq (tw_lmul w t) (tw_lmul w t').
Proof.
  intro H.
  induction H as [ u v a b Hab | u v a b | s s' t t' _ IH1 _ IH2 | s s' _ IH
                 | s t u | s t | s | s | s t _ IH | s t u _ IH1 _ IH2 ];
    simpl.
  - rewrite !app_assoc. exact (twe_letter (w ++ u) v Hab).
  - rewrite !app_assoc. exact (twe_lin (w ++ u) v a b).
  - exact (twe_plus IH1 IH2).
  - exact (twe_neg IH).
  - apply twe_assoc.
  - apply twe_comm.
  - apply twe_zero_l.
  - apply twe_neg_l.
  - exact (twe_sym IH).
  - exact (twe_trans IH1 IH2).
Qed.

(*
 Group-level helpers, read off [TWAb]; the middle-four interchange is
 Instance/CMon/Biproduct.v's [cmon_plus_interchange] at [TWAb]. 

 --------
 组级辅助，读出 [TWAb]；中间四个交换是 Instance/CMon/Biproduct.v 的 [cmon_plus_interchange] 在 [TWAb]。
*)
Lemma tw_neg_plus (a b : TWTerm) :
  tw_eq (tw_neg (tw_plus a b)) (tw_plus (tw_neg a) (tw_neg b)).
Proof. exact (ab_neg_plus TWAb a b). Qed.

Lemma tw_neg_zero : tw_eq (tw_neg tw_zero) tw_zero.
Proof. exact (ab_neg_zero TWAb). Qed.

Lemma tw_zero_zero : tw_eq tw_zero (tw_plus tw_zero tw_zero).
Proof. exact (twe_sym (twe_zero_l tw_zero)). Qed.

(* Juxtaposition on the left respects the letters on the right... / 左边的并置尊重右边的字母... *)
Lemma tw_lmul_letter (u v : list L) (a b : L) (H : a ≈ b) (t : TWTerm) :
  tw_eq (tw_lmul (u ++ a :: v) t) (tw_lmul (u ++ b :: v) t).
Proof.
  induction t as [ x | | s IHs t IHt | s IHs ]; simpl.
  - rewrite <- !app_assoc. simpl. exact (twe_letter u (v ++ x) H).
  - apply tw_refl.
  - exact (twe_plus IHs IHt).
  - exact (twe_neg IHs).
Qed.

(* ...and is additive in each of its letters. / ...并且在其每个字母中都是可加的。 *)
Lemma tw_lmul_lin (u v : list L) (a b : L) (t : TWTerm) :
  tw_eq (tw_lmul (u ++ cmon_plus A a b :: v) t)
        (tw_plus (tw_lmul (u ++ a :: v) t) (tw_lmul (u ++ b :: v) t)).
Proof.
  induction t as [ x | | s IHs t IHt | s IHs ]; simpl.
  - rewrite <- !app_assoc. simpl. exact (twe_lin u (v ++ x) a b).
  - exact tw_zero_zero.
  - refine (twe_trans (twe_plus IHs IHt) _).
    exact (cmon_plus_interchange TWAb _ _ _ _).
  - refine (twe_trans (twe_neg IHs) _). apply tw_neg_plus.
Qed.

End Words.

Arguments tw_word {A} _.
Arguments tw_zero {A}.
Arguments tw_plus {A} _ _.
Arguments tw_neg {A} _.
Arguments tw_lmul {A} _ _.
Arguments tw_refl {A} _.
Arguments twe_sym {A s t} _.
Arguments twe_trans {A s t u} _ _.
Arguments twe_letter {A} u v {a b} _.
Arguments twe_lin {A} u v a b.
Arguments twe_plus {A s s' t t'} _ _.
Arguments twe_neg {A s s'} _.
Arguments twe_assoc {A} s t u.
Arguments twe_comm {A} s t.
Arguments twe_zero_l {A} s.
Arguments twe_neg_l {A} s.
Arguments tw_eq_of_eq {A s t} _.

(* A function on words that respects each letter and is additive in each letter extends to a homomorphism out of [TWAb]: the universal property of the presentation. / 一个在单词上作用、尊重每个字母并在每个字母上可加的函数可以扩展为从 [TWAb] 出发的同态：这是该表示的泛性质。 *)
Section Extension.

Context (A c : Ab).

Local Notation L := (carrier (cmon_setoid A)).

Context (ν : list L → carrier (cmon_setoid c)).
Context (Hletter : ∀ (u v : list L) (a b : L),
                     a ≈ b → ν (u ++ a :: v) ≈ ν (u ++ b :: v)).
Context (Hlin : ∀ (u v : list L) (a b : L),
                  ν (u ++ cmon_plus A a b :: v)
                    ≈ cmon_plus c (ν (u ++ a :: v)) (ν (u ++ b :: v))).

Fixpoint tw_ext_fun (t : TWTerm A) : carrier (cmon_setoid c) :=
  match t with
  | tw_word w => ν w
  | tw_zero => cmon_zero c
  | tw_plus s t => cmon_plus c (tw_ext_fun s) (tw_ext_fun t)
  | tw_neg s => ab_neg c (tw_ext_fun s)
  end.

Lemma tw_ext_respects (s t : TWTerm A) :
  tw_eq A s t → tw_ext_fun s ≈ tw_ext_fun t.
Proof using Hletter Hlin.
  intro He.
  apply pequiv_to.
  induction He as [ u v a b Hab | u v a b | s s' t t' _ IH1 _ IH2 | s s' _ IH
                  | s t u | s t | s | s | s t _ IH | s t u _ IH1 _ IH2 ];
    simpl.
  - apply pequiv_from. exact (Hletter u v a b Hab).
  - apply pequiv_from. exact (Hlin u v a b).
  - apply pequiv_from.
    exact (cmon_plus_respects c _ _ (pequiv_to _ _ IH1)
                                _ _ (pequiv_to _ _ IH2)).
  - apply pequiv_from. exact (ab_neg_respects c _ _ (pequiv_to _ _ IH)).
  - apply pequiv_from. apply cmon_plus_assoc.
  - apply pequiv_from. apply cmon_plus_comm.
  - apply pequiv_from. apply cmon_plus_zero_l.
  - apply pequiv_from. apply ab_neg_left.
  - exact (symmetry IH).
  - exact (transitivity IH1 IH2).
Qed.

Definition tw_ext : TWAb A ~{Ab}~> c.
Proof using Hletter Hlin.
  unshelve refine (@Build_CMonHom (TWAb A) c
    (@Build_SetoidMorphism (TWTerm A) (tw_Setoid A)
       (carrier (cmon_setoid c)) (is_setoid (cmon_setoid c)) tw_ext_fun _)
    _ _).
  - intros s t H. exact (tw_ext_respects s t H).
  - reflexivity.
  - intros s t. reflexivity.
Defined.

Example tw_ext_word (w : list L) : cmon_map tw_ext (tw_word w) = ν w
  := eq_refl.

End Extension.

Arguments tw_ext {A} c ν Hletter Hlin.

(* ------------------------------------------------------------------------ *)
(* * ** The n-fold tensor powers, and the words as their direct sum / * ** n 重张量幂，以及作为其直和的词 *)

(*
 The tensor powers are Structure/Monoidal/Hypergraph/Spider.v's
 [tpower] at Instance/Ab/Monoidal.v's [Ab_Monoidal]: A^{⊗0} is the unit
 ℤ and A^{⊗(n+1)} is A ⊗ A^{⊗n}, Instance/Ab/Tensor.v's [AbTensor]. 

 --------
 张量幂是 Structure/Monoidal/Hypergraph/Spider.v 的 [tpower]，在 Instance/Ab/Monoidal.v 的 [Ab_Monoidal] 中：A^{⊗0} 是单位 ℤ，A^{⊗(n+1)} 是 A ⊗ A^{⊗n}，Instance/Ab/Tensor.v 的 [AbTensor]。
*)
Example tpower_ab_zero (A : Ab) : A ^⨂ 0 = ZAb := eq_refl.

Example tpower_ab_succ (A : Ab) (n : nat) :
  A ^⨂ (S n) = AbTensor A (A ^⨂ n) := eq_refl.

Section Coproduct.

Context (A : Ab).

Local Notation L := (carrier (cmon_setoid A)).

(* A word as a pure tensor of its length: ⟨a₁ … aₙ⟩ ↦ a₁ ⊗ (… ⊗ (aₙ ⊗ 1)). / 一个单词作为其长度的纯张量：⟨a₁ … aₙ⟩ ↦ a₁ ⊗ (… ⊗ (aₙ ⊗ 1))。 *)
Fixpoint tw_pure (w : list L) : carrier (A ^⨂ (length w)) :=
  match w with
  | nil => ZAb_one
  | a :: w' => @ts_gen A (A ^⨂ (length w')) a (tw_pure w')
  end.

(* The injection of degree 0: k ↦ k·⟨⟩. / 零度注入：k ↦ k·⟨⟩。 *)
Definition tw_iota0 : ZAb ~{Ab}~> TWAb A.
Proof.
  unshelve refine (@Build_CMonHom ZAb (TWAb A)
    (@Build_SetoidMorphism (carrier ZAb) (is_setoid (cmon_setoid ZAb))
       (TWTerm A) (tw_Setoid A) (fun k => zsmul (TWAb A) k (tw_word nil)) _)
    _ _).
  - intros k k' H. apply ZAb_eq in H. subst. apply tw_refl.
  - exact (zsmul_Z0 (TWAb A) _).
  - intros k k'. exact (zsmul_add (TWAb A) k k' _).
Defined.

(* The bilinear map a, x ↦ ⟨a⟩ · ι x out of A × A^{⊗n}. / 双线性映射 a, x ↦ ⟨a⟩ · ι x 从 A × A^{⊗n}。 *)
Definition tw_lmul1_bilin (n : nat) (ι : A ^⨂ n ~{Ab}~> TWAb A) :
  Bilinear A (A ^⨂ n) (TWAb A).
Proof.
  unshelve refine (@Build_Bilinear A (A ^⨂ n) (TWAb A)
                     (fun a x => tw_lmul (a :: nil) (cmon_map ι x)) _ _ _).
  - intros a a' Ha x x' Hx.
    refine (twe_trans (tw_lmul_letter A nil nil a a' Ha _) _).
    exact (tw_lmul_respects_r A _ _ _ (proper_morphism (cmon_map ι) _ _ Hx)).
  - intros a a' x. exact (tw_lmul_lin A nil nil a a' _).
  - intros a x x'.
    exact (tw_lmul_respects_r A _ _ _ (cmon_map_plus ι x x')).
Defined.

(* The injections ιₙ : A^{⊗n} → ⨁, by the tensor's universal property. / 通过张量的普遍性质，注入 ιₙ : A^{⊗n} → ⨁。 *)
Fixpoint tw_iota (n : nat) : A ^⨂ n ~{Ab}~> TWAb A :=
  match n with
  | O => tw_iota0
  | S n => tensor_ump (tw_lmul1_bilin n (tw_iota n))
  end.

Example tw_iota_gen (n : nat) (a : L) (x : carrier (A ^⨂ n)) :
  cmon_map (tw_iota (S n)) (ts_gen a x)
    = tw_lmul (a :: nil) (cmon_map (tw_iota n) x) := eq_refl.

(* Every word is the image of its pure tensor. / 每一个词都是其纯张量的映像。 *)
Lemma tw_word_iota (w : list L) :
  tw_eq A (tw_word w) (cmon_map (tw_iota (length w)) (tw_pure w)).
Proof.
  induction w as [ | a w IH ]; simpl.
  - exact (twe_sym (zsmul_one (TWAb A) (tw_word nil))).
  - exact (tw_lmul_respects_r A (a :: nil) _ _ IH).
Qed.

End Coproduct.

Arguments tw_pure {A} w.
Arguments tw_iota {A} n.

(* The copairing of a family ιₙ : A^{⊗n} → c. / 一个族 ιₙ : A^{⊗n} → c 的共配对。 *)
Section Desc.

Context (A : Ab) (c : Ab).

Local Notation L := (carrier (cmon_setoid A)).

Definition ts_gen_hom (n : nat) (a : L) :
  A ^⨂ n ~{Ab}~> AbTensor A (A ^⨂ n).
Proof.
  unshelve refine (@Build_CMonHom (A ^⨂ n) (AbTensor A (A ^⨂ n))
    (@Build_SetoidMorphism (carrier (A ^⨂ n))
       (is_setoid (cmon_setoid (A ^⨂ n)))
       (tsum A (A ^⨂ n)) (ts_Setoid A (A ^⨂ n)) (@ts_gen A (A ^⨂ n) a) _)
    _ _).
  - intros x y H. exact (te_gen (reflexivity a) H).
  - exact (ts_gen_zero_r a).
  - intros x y. exact (te_bilin_r a x y).
Defined.

(* The family shifted by one letter a: x ↦ ι_{n+1}(a ⊗ x). / 这个族通过一个字母 a 移位：x ↦ ι_{n+1}(a ⊗ x)。 *)
Definition tw_shift (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c) (a : L) :
  ∀ n : nat, A ^⨂ n ~{Ab}~> c :=
  fun n => iota (S n) ∘[Ab] ts_gen_hom n a.

Fixpoint tw_desc_fun (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c) (t : TWTerm A) :
  carrier c :=
  match t with
  | tw_word w => cmon_map (iota (length w)) (tw_pure w)
  | tw_zero => cmon_zero c
  | tw_plus s t => cmon_plus c (tw_desc_fun iota s) (tw_desc_fun iota t)
  | tw_neg s => ab_neg c (tw_desc_fun iota s)
  end.

(* The copairing respects a letter and is additive in it. The induction is on the prefix, generalized over the whole family, so no transport along the length of a word is needed. / 共对配对遵循字母并且在字母上是可加的。归纳是在前缀上进行的，并对整个族做了推广，因此不需要沿单词长度进行传递。 *)
Lemma tw_desc_letter (u : list L) : ∀ (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c)
  (v : list L) (a b : L), a ≈ b →
  cmon_map (iota (length (u ++ a :: v))) (tw_pure (u ++ a :: v))
    ≈ cmon_map (iota (length (u ++ b :: v))) (tw_pure (u ++ b :: v)).
Proof.
  induction u as [ | d u IH ]; intros iota v a b H; simpl.
  - apply (proper_morphism (cmon_map (iota (S (length v))))).
    exact (te_gen H (reflexivity _)).
  - exact (IH (tw_shift iota d) v a b H).
Qed.

Lemma tw_desc_lin (u : list L) : ∀ (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c)
  (v : list L) (a b : L),
  cmon_map (iota (length (u ++ cmon_plus A a b :: v)))
           (tw_pure (u ++ cmon_plus A a b :: v))
    ≈ cmon_plus c
        (cmon_map (iota (length (u ++ a :: v))) (tw_pure (u ++ a :: v)))
        (cmon_map (iota (length (u ++ b :: v))) (tw_pure (u ++ b :: v))).
Proof.
  induction u as [ | d u IH ]; intros iota v a b; simpl.
  - refine (transitivity (proper_morphism (cmon_map (iota (S (length v))))
                            _ _ (te_bilin_l a b (tw_pure v))) _).
    exact (cmon_map_plus (iota (S (length v))) _ _).
  - exact (IH (tw_shift iota d) v a b).
Qed.

Lemma tw_desc_respects (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c)
  (s t : TWTerm A) :
  tw_eq A s t → tw_desc_fun iota s ≈ tw_desc_fun iota t.
Proof.
  intro He.
  apply pequiv_to.
  induction He as [ u v a b Hab | u v a b | s s' t t' _ IH1 _ IH2 | s s' _ IH
                  | s t u | s t | s | s | s t _ IH | s t u _ IH1 _ IH2 ];
    simpl.
  - apply pequiv_from. exact (tw_desc_letter u iota v a b Hab).
  - apply pequiv_from. exact (tw_desc_lin u iota v a b).
  - apply pequiv_from.
    exact (cmon_plus_respects c _ _ (pequiv_to _ _ IH1)
                                _ _ (pequiv_to _ _ IH2)).
  - apply pequiv_from. exact (ab_neg_respects c _ _ (pequiv_to _ _ IH)).
  - apply pequiv_from. apply cmon_plus_assoc.
  - apply pequiv_from. apply cmon_plus_comm.
  - apply pequiv_from. apply cmon_plus_zero_l.
  - apply pequiv_from. apply ab_neg_left.
  - exact (symmetry IH).
  - exact (transitivity IH1 IH2).
Qed.

Definition tw_desc (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c) :
  TWAb A ~{Ab}~> c.
Proof.
  unshelve refine (@Build_CMonHom (TWAb A) c
    (@Build_SetoidMorphism (TWTerm A) (tw_Setoid A) (carrier c)
       (is_setoid (cmon_setoid c)) (tw_desc_fun iota) _) _ _).
  - intros s t H. exact (tw_desc_respects iota s t H).
  - reflexivity.
  - intros s t. reflexivity.
Defined.

(* Juxtaposition on the left by one letter shifts the family, LEIBNIZ. / 左边相邻一个字母就会改变这个家族，莱布尼茨。 *)
Lemma tw_desc_lmul (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c) (a : L)
  (t : TWTerm A) :
  tw_desc_fun iota (tw_lmul (a :: nil) t) = tw_desc_fun (tw_shift iota a) t.
Proof.
  induction t as [ w | | s IHs t IHt | s IHs ]; simpl.
  - reflexivity.
  - reflexivity.
  - rewrite IHs, IHt. reflexivity.
  - rewrite IHs. reflexivity.
Qed.

(* The copairing composed with ιₙ is the n-th map of the family. / 与 ιₙ 组合的共配对是该族的第 n 个映射。 *)
Lemma tw_desc_iota (n : nat) : ∀ (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c)
  (x : carrier (A ^⨂ n)),
  cmon_map (tw_desc iota) (cmon_map (tw_iota n) x) ≈ cmon_map (iota n) x.
Proof.
  induction n as [ | n IH ]; intros iota x.
  - simpl.
    refine (transitivity (zsmul_hom (tw_desc iota) x (tw_word nil)) _).
    simpl.
    refine (transitivity (symmetry (zsmul_hom (iota O) x ZAb_one)) _).
    apply (proper_morphism (cmon_map (iota O))).
    exact (zsmul_int_one x).
  - refine (tensor_hom_ext (tw_desc iota ∘[Ab] tw_iota (S n)) (iota (S n))
              _ x).
    intros a y. simpl.
    rewrite tw_desc_lmul.
    exact (IH (tw_shift iota a) y).
Qed.

(* ...and it is the only such homomorphism. / ...并且它是唯一的此类同态映射。 *)
Lemma tw_desc_unique (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c)
  (g : TWAb A ~{Ab}~> c)
  (H : ∀ n : nat, g ∘[Ab] tw_iota n ≈ iota n) (t : TWTerm A) :
  cmon_map g t ≈ tw_desc_fun iota t.
Proof.
  induction t as [ w | | s IHs t IHt | s IHs ]; simpl.
  - refine (transitivity (proper_morphism (cmon_map g) _ _
                            (tw_word_iota A w)) _).
    exact (H (length w) (tw_pure w)).
  - exact (cmon_map_zero g).
  - refine (transitivity (cmon_map_plus g s t) _).
    exact (cmon_plus_respects c _ _ IHs _ _ IHt).
  - refine (transitivity (ab_map_neg g s) _).
    exact (ab_neg_respects c _ _ IHs).
Qed.

End Desc.

(* Mac Lane's “(infinite) direct sum of the n-fold tensor powers”: the words are the coproduct in Ab of the A^{⊗n}, with the injections ιₙ. / Mac Lane的“(无限) n次张量幂的直和”：这些词是在Ab中的A^{⊗n}的余积，并带有注入映射 ιₙ。 *)
Definition TW_is_tensor_coproduct (A : Ab) :
  @IsIndexedCoproduct Ab nat (fun n => A ^⨂ n) (TWAb A) (@tw_iota A).
Proof.
  apply Build_IsIndexedCoproduct.
  intros c iota.
  unshelve eexists.
  - exact (tw_desc A c iota).
  - intros n x. exact (tw_desc_iota A c n iota x).
  - intros g Hg t. symmetry. exact (tw_desc_unique A c iota g Hg t).
Defined.

(* The copairing computes on words. / 该共配在词上进行计算。 *)
Example tw_desc_word (A c : Ab) (iota : ∀ n : nat, A ^⨂ n ~{Ab}~> c)
  (w : list (carrier (cmon_setoid A))) :
  cmon_map (tw_desc A c iota) (tw_word w)
    = cmon_map (iota (length w)) (tw_pure w) := eq_refl.
