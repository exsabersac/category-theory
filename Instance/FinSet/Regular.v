Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.FinSet.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(* * * Regular arrows in FinSet, by finite search / * * 在 FinSet 中的常规箭头，通过有限搜索 *)

(*
 nLab:      https://ncatlab.org/nlab/show/split+epimorphism
 Wikipedia: https://en.wikipedia.org/wiki/Regular_semigroup
 Wikipedia: https://en.wikipedia.org/wiki/Axiom_of_choice

 Mac Lane, CWM 2nd ed., §I.5 Exercise 7, printed p. 21.  CITED BY LOCATION;
 the printed text was not consulted and no sentence of it is reproduced.
 The in-tree catalog (doc/plan/books/maclane/inventory/I.json, id
 maclane:I.5:ex7) summarizes the exercise as: "Call an arrow f : a -> b in
 a category C regular when there exists g : b -> a with f g f = f.  Show f
 is regular whenever it has either a left or a right inverse, and prove
 that in Set every arrow f : a -> b with a nonempty is regular."

 The first half is category theory and lives in Theory/Morphisms.v
 ([regular_of_section], [regular_of_retraction]).  This file is the second
 half, and the second half is where a choice principle would ordinarily be
 spent.  It is spent here on FINITENESS instead. 

 --------
 nLab:       https://ncatlab.org/nlab/show/split+epimorphism 
 维基百科:  https://en.wikipedia.org/wiki/Regular_semigroup 
 维基百科:  https://en.wikipedia.org/wiki/Axiom_of_choice 

 Mac Lane, CWM 第二版, §I.5 练习 7, 印刷页 21. 引用位置;
 未查阅印刷文本，也未复现其中的任何句子。
 树内目录 (doc/plan/books/maclane/inventory/I.json, id
 maclane:I.5:ex7) 将该练习总结为："在一个范畴 C 中，若存在 g : b -> a 且 f g f = f，则称箭头 f : a -> b 为正规。证明当 f 拥有左逆或右逆时，f 都是正规的，并证明在 Set 中每个箭头 f : a -> b（当 a 非空）都是正规的。"

 前半部分属于范畴论，存放于 Theory/Morphisms.v
 ( [regular_of_section] ,  [regular_of_retraction] )。该文件是后半部分，通常选择原则会用于后半部分。这里它被用于 FINITENESS（有限性）。
*)

(* ------------------------------------------------------------------------ *)
(* * ** What the classical statement costs, and what is proved instead / * ** 经典陈述的代价，以及相应证明的内容 *)

(*
 WHAT THE CLASSICAL ARGUMENT SPENDS.

 Fix f : A → B in Set with A inhabited by a₀.  A pseudoinverse must send
 each b ∈ B to SOME element of the fibre f⁻¹(b) when that fibre is
 nonempty, and anywhere at all (say a₀) when it is empty.  Nothing in the
 data of f selects a fibre element: the classical construction picks one
 simultaneously for every b in the image, which is an instance of the axiom
 of choice over the family of fibres.  Reading a regularity witness back
 off is choice-free, and is [regular_epic_retraction] /
 [regular_monic_section] in Theory/Morphisms.v.

 HOW MUCH THE BLANKET PRINCIPLE COSTS HERE.  Choice is what that argument
 spends under an ambient excluded middle.  It is not what the blanket
 principle costs in this library's ambient logic, where the principle is
 strictly STRONGER than any choice axiom: it decides every proposition.
 Instance/Sets/Regular.v proves that, axiom-free.
 [blanket_regularity_entails_LEM] there derives ∀ P : Prop, P + (P → False)
 from "every arrow of [Sets] with inhabited domain is regular", and
 [blanket_splitting_entails_LEM] derives the same conclusion from the
 weaker internal choice principle "every epimorphism with inhabited domain
 splits" -- the phrasing the nLab page on split epimorphisms records for
 the axiom of choice internal to a category, noting that "In Set this is
 equivalent to the usual axiom of choice" (retrieved 2026-08).  The
 implication BETWEEN those two quantified principles is
 [blanket_regularity_entails_splitting], itself a statement of Coq rather
 than a remark about the pointwise [regular_epic_retraction] it is one line
 from.  The countermodel driving all three is a two-element setoid
 coarsened by a proposition, in the shape of Diaconescu's argument; the
 header of that file carries the citations, and the reason a SETOID library
 pays this price where the standard library's intensional choice axioms do
 not.  No [Axiom] is declared in this file or in that one, and [Print
 Assumptions] on every constant of either reports "Closed under the global
 context".

 WHAT IS PROVED INSTEAD.  Over FinSet the fibre selection needs no choice
 at all, because a fibre of a map Fin.t m → Fin.t n can be SEARCHED: the
 domain is a finite type, so a scan over it terminates, and equality in the
 codomain is decidable, so each candidate can be tested ([Fin.eq_dec] of the
 standard library, which is transparent and reduces on closed terms).
 [fin_preimage] performs that search by structural recursion on m and
 [finset_regular] assembles the pseudoinverse from it, so the witness is a
 program rather than an appeal.  Because the library's `∃` is Type-valued
 (`sigT`, Lib/Foundation.v) the witness survives as data, and the
 [Example]s at the end of this file evaluate it by [eq_refl].  The
 inhabited-domain hypothesis is then disposed of in the only case it
 excludes: an epimorphism out of the empty object forces an empty codomain
 ([finset_epi_from_empty_absurd]), so [finset_every_epi_splits] holds for
 EVERY arrow of FinSet, with no restriction on the domain and no choice
 principle in sight.  The hypothesis is nevertheless SHARP for regularity
 itself -- [finset_empty_to_one_not_regular] refutes it for the unique
 arrow 0 → 1 -- so FinSet supplies its own witness that regularity is a
 real condition, and this file no longer has to reach to Instance/Two.v
 for one.

 The exchange is a genuine restriction and not a re-description: FinSet is
 the SKELETON of finite sets, so "every arrow with inhabited domain is
 regular" is proved here only for finite sets, and nothing below says
 anything about an arrow of [Sets] with an infinite domain.  What
 Instance/Sets/Regular.v adds about [Sets] is a bound in the other
 direction: the blanket statement is not available there, so the exercise's
 second half stops at the finite case for a reason, and not for want of an
 argument.  Instance/Sets.v is short of the ingredients in any case: its
 [surjectivity_is_epic] is abandoned in the epi → surjective direction for
 an unrelated size reason documented at Instance/Sets.v, so the
 tree has no route from [Epic] to a fibre witness in [Sets] to begin
 with. 

 --------
 经典论证消耗的内容。

 固定 f : A → B 在集合论中，且 A 中有元素 a₀。一个伪逆必须将每个 b ∈ B 发送到 f⁻¹(b) 的某个元素，当该纤维非空时；而当纤维为空时，则发送到任意元素（例如 a₀）。f 的数据中没有选择纤维元素的机制：经典构造为像中的每个 b 同时选择一个元素，这是纤维族上的选择公理的一个实例。从规则性证明中回读是无需选择的，并且在 Theory/Morphisms.v 中表示为 [regular_epic_retraction] / [regular_monic_section]。这里的总原则成本是多少。选择是在一个环境排中律下该论证所花费的。它不是在这个库的环境逻辑中总原则的成本，在这里该原则严格强于任何选择公理：它决定了每一个命题。Instance/Sets/Regular.v 在无公理的情况下证明了这一点。[blanket_regularity_entails_LEM] 从“每一个具有非空域的箭头都是正规箭头”推导出 ∀ P : Prop, P + (P → False)，而 [blanket_splitting_entails_LEM] 则从较弱的内部选择原则“每一个具有非空域的满射分裂”推导出相同的结论——这是 nLab 页面关于分裂满射对范畴内部选择公理的表述，并指出“在 Set 中，这等价于通常的选择公理”（2026-08 检索）。这两个量化原理之间的蕴含是 [blanket_regularity_entails_splitting]，它本身是 Coq 的一个陈述，而不是关于逐点 [regular_epic_retraction] 的一个注释，它来自的一行。驱动这三个的反模型是一个由命题粗化的二元集合体，其形式类似于 Diaconescu 的论证；该文件的标题带有引用，并解释了为什么在标准库的强度选择公理不产生代价的情况下，SETOID 库需要支付这一代价。在此文件或那个文件中都没有声明 [Axiom]，对任一常量执行 [Print Assumptions] 都报告“在全局上下文下封闭”。相反被证明的内容。在 FinSet 上，纤维选择根本不需要选择，因为可以搜索映射 Fin.t m → Fin.t n 的纤维：其定义域是有限类型，因此对其扫描是会终止的，并且值域的相等性是可判定的，因此可以测试每个候选项（标准库的 [Fin.eq_dec]，它是透明的并且在封闭项上会归约）。[fin_preimage] 通过对 m 的结构递归执行该搜索，而 [finset_regular] 则从中组装出伪逆，因此见证者是一个程序，而不是一种请求。因为库的 `∃` 是类型值（`sigT`, Lib/Foundation.v），见证者可以作为数据存在，并且本文件末尾的 [Example] 通过 [eq_refl] 对其求值。那么，已占领域假设仅在它排除的唯一情况下被驳回：从空对象出的满射迫使一个空余域（[finset_epi_from_empty_absurd]），因此[finset_every_epi_splits]对FinSet的每一个箭头都成立，对域没有任何限制，也不需要选择公理。然而，该假设对于正则性本身仍然是尖锐的——[finset_empty_to_one_not_regular]针对唯一的箭头 0 → 1 驳斥了它——因此FinSet提供了自身的证据表明正则性是一个真实的条件，而且该文件不再需要去引用Instance/Two.v来得到一个例子。该交换是一个真正的限制，而不是重新描述：FinSet 是有限集合的骨架，所以“具有非空定义域的每一个箭头都是正规”在此仅对有限集合进行了证明，下文并未涉及具有无限定义域的 [Sets] 的箭头。Instance/Sets/Regular.v 对 [Sets] 的补充是另一个方向的界限：那里没有通用声明，因此练习的第二部分在有限情况下结束是有原因的，而不是缺乏论证。无论如何，Instance/Sets.v 缺少必要的成分：它的 [surjectivity_is_epic] 在 epi → surjective 方向被放弃，原因是与大小无关，并在 Instance/Sets.v 中有说明，因此树从 [Epic] 到 [Sets] 中的纤维证据根本没有路径。
*)

(* ------------------------------------------------------------------------ *)
(** ** The finite search / ** 有限搜索 *)

(*
 [fin_preimage f b] scans the domain in index order and returns the first
 a with f a = b, or [None] if there is none.  The recursion is structural
 in m: at [S m'] it tests the head index [Fin.F1] and otherwise recurses on
 the tail map [fun q => f (Fin.FS q)], re-tagging the answer along
 [Fin.FS].  This mirrors the recursion pattern already used for [fin_split]
 in Instance/FinSet.v, and like it, reduces on closed input. 

 --------
 [fin_preimage f b] 按索引顺序扫描域，并返回第一个满足 f a = b 的 a，如果没有则返回 [None]。递归在 m 上是结构性的：在 [S m'] 处，它测试头索引 [Fin.F1]，否则递归处理尾映射 [fun q => f (Fin.FS q)]，并沿 [Fin.FS] 重新标记答案。这反映了在 Instance/FinSet.v 中 [fin_split] 已使用的递归模式，并且像它一样，在闭合输入上进行化简。
*)

Fixpoint fin_preimage (m n : nat) (f : Fin.t m → Fin.t n) (b : Fin.t n)
         {struct m} : option (Fin.t m) :=
  match m return (Fin.t m → Fin.t n) → option (Fin.t m) with
  | O    => fun _ => None
  | S m' => fun f =>
      match Fin.eq_dec (f Fin.F1) b with
      | left _  => Some Fin.F1
      | right _ =>
          match fin_preimage m' n (fun q => f (Fin.FS q)) b with
          | Some q => Some (Fin.FS q)
          | None   => None
          end
      end
  end f.

Arguments fin_preimage {m n} f b.

(*
 Correctness of the search, in the only form needed: at a value that IS
 attained the search succeeds, and what it returns is a genuine preimage.
 Both halves are packaged in one [match] so that a single induction on the
 witness a proves them together -- the [None] branch is the statement that
 the search cannot miss, and the [Some] branch that it cannot lie.

 Note the use of `=` rather than `≈` here and in [fin3_cases] below: these
 are equations between ELEMENTS of [Fin.t n], not between morphisms, so the
 library's `≈`-only rule for morphism equality does not apply (this is not
 the same-term exception documented at Functor/Bifunctor.v).  Every
 MORPHISM equation in this file -- [finset_split_pair], [finset_point_bang],
 [finset_collapse_not_id] and the [RegularMorphism] statements -- is stated
 with `≈`, which over FinSet unfolds to pointwise `=` on [Fin.t] via
 [Fin_Setoid] (Lib/Setoid.v) and [fun_setoid] (Lib/Datatypes.v). 

 --------
 搜索的正确性，仅在所需的唯一形式下：在一个被实现的值时，搜索成功，并且返回的是一个真正的原像。两部分都被打包在一个 [match] 中，以便对见证 a 的单一归纳同时证明它们——[None] 分支表示搜索不可能遗漏，[Some] 分支表示搜索不可能撒谎。注意这里以及下面的 [fin3_cases] 中使用的是 `=` 而不是 `≈`：这些是 [Fin.t n] 元素之间的方程，而不是态射之间的方程，所以库中的仅针对态射相等的 `≈` 规则不适用（这不是 Functor/Bifunctor.v 中记录的同项例外）。本文件中的每一个态射方程 —— [finset_split_pair]、[finset_point_bang]、[finset_collapse_not_id] 和 [RegularMorphism] 声明 —— 都是用 `≈` 表示的，在 FinSet 中展开时通过 [Fin_Setoid]（Lib/Setoid.v）和 [fun_setoid]（Lib/Datatypes.v）在 [Fin.t] 上逐点地变为 `=`。
*)

Lemma fin_preimage_correct {m n : nat} (f : Fin.t m → Fin.t n) (a : Fin.t m) :
  match fin_preimage f (f a) with
  | Some a' => f a' = f a
  | None    => False
  end.
Proof.
  revert f.
  induction a as [m | m a IH]; intros f; simpl.
  - (* head index: the test at [Fin.F1] succeeds outright / 头索引：在 [Fin.F1] 的测试直接成功 *)
    destruct (Fin.eq_dec (f Fin.F1) (f Fin.F1)) as [_ | ne].
    + reflexivity.
    + now contradiction ne.
  - (* tail index: either the head already hits the value, or recurse / 尾索引：要么头部已经命中该值，要么递归 *)
    destruct (Fin.eq_dec (f Fin.F1) (f (Fin.FS a))) as [e | _].
    + exact e.
    + specialize (IH (fun q => f (Fin.FS q))); simpl in IH.
      destruct (fin_preimage (fun q => f (Fin.FS q)) (f (Fin.FS a)));
        exact IH.
Qed.

(*
 The pseudoinverse of f relative to a chosen fallback point a0 of the
 domain: search the fibre, and land on a0 where the fibre is empty.  The
 fallback is the only use made of the inhabitation hypothesis. 

 --------
 相对于所选域的备用点 a0 的 f 的伪逆：搜索纤维，当纤维为空时落在 a0 上。备用点是对存在性假设的唯一使用。
*)

Definition finset_pseudoinverse {m n : nat} (a0 : Fin.t m)
           (f : Fin.t m → Fin.t n) : Fin.t n → Fin.t m :=
  fun b => match fin_preimage f b with
           | Some a => a
           | None   => a0
           end.

(* ------------------------------------------------------------------------ *)
(* * ** Mac Lane §I.5 Exercise 7, second half, over FinSet / * ** Mac Lane §I.5 练习 7，下半部分，关于 FinSet *)

(*
 Every arrow of FinSet whose domain is inhabited is regular.  Inhabitation
 is taken as DATA (an actual element a0), which is what "nonempty" means
 constructively and what the finite search needs; the special case of a
 successor domain, where [Fin.F1] serves, is [finset_regular_pos] below.

 This is [Definition] ... [Defined] rather than [Qed] so the pseudoinverse
 really can be projected out and run; the [Example]s below do exactly
 that. 

 --------
 每一个定义域不为空的 FinSet 箭头都是正则的。这里的不为空被视为 DATA（一个实际元素 a0），这就是构造中“非空”的含义，也是有限搜索所需要的；对于后继域的特殊情况，其中 [Fin.F1] 起作用，在下面由 [finset_regular_pos] 表示。

 这是 [Definition] ... [Defined] 而不是 [Qed]，因此伪逆确实可以被投影出来并运行；下面的 [Example] 正是这样做的。
*)

Definition finset_regular {m n : nat} (a0 : Fin.t m) (f : m ~{FinSet}~> n) :
  RegularMorphism f.
Proof.
  exists (finset_pseudoinverse a0 f).
  intro a; simpl; unfold finset_pseudoinverse.
  pose proof (fin_preimage_correct f a) as H.
  destruct (fin_preimage f (f a)) as [a' |].
  - exact H.
  - contradiction.
Defined.

(*
 The same statement with inhabitation read off the object: an arrow out of
 a successor object is regular, with [Fin.F1] as the fallback. 

 --------
 对对象读取居住的相同语句：来自继承对象的箭头是规则的，以 [Fin.F1] 作为后备。
*)
Definition finset_regular_pos {m n : nat} (f : S m ~{FinSet}~> n) :
  RegularMorphism f := finset_regular Fin.F1 f.

(* ------------------------------------------------------------------------ *)
(* * ** The hypothesis is sharp, and every epimorphism splits regardless / * ** 假设是明确的，并且每个满射都可以拆分，无论如何 *)

(*
 The inhabitation hypothesis of [finset_regular] is not an artefact of the
 search.  An arrow out of the empty object into a nonempty one has no
 pseudoinverse at all, since a pseudoinverse would be an arrow BACK, and
 there is no map into the empty set from a nonempty one. 

 --------
 [finset_regular] 的居住假设并不是搜索的产物。从空对象到非空对象的箭头根本没有伪逆，因为伪逆将是一个返回的箭头，而从非空集合到空集合没有映射。
*)

Lemma finset_empty_domain_not_regular {n : nat} (f : 0%nat ~{FinSet}~> S n) :
  RegularMorphism f → False.
Proof. intros [g _]; exact (Fin.case0 (fun _ => False) (g Fin.F1)). Qed.

(*
 The smallest instance is the unique arrow from the empty set to the
 singleton -- the [zero] of [FinSet_Initial] (Instance/FinSet.v),
 written out -- and it is FinSet's own non-regular arrow.  Regularity is
 therefore a real condition on an arrow of THIS category, without appeal to
 the interval category of Instance/Two.v. 

 --------
 最小的实例是从空集到单集的唯一箭头——在  [FinSet_Initial]  的  [zero]  中（Instance/FinSet.v），展开写出——它是 FinSet 自身的非正规箭头。因此，正规性确实是此范畴中箭头的一个真正条件，而无需诉诸于 Instance/Two.v 的区间范畴。
*)

Definition finset_empty_to_one : 0%nat ~{FinSet}~> 1%nat :=
  fun a => Fin.case0 (fun _ => Fin.t 1) a.

Definition finset_empty_to_one_not_regular :
  RegularMorphism finset_empty_to_one → False :=
  finset_empty_domain_not_regular finset_empty_to_one.

(*
 Splitting, unlike regularity, survives the empty domain: an epimorphism
 out of the empty object forces its codomain to be empty as well.  Probe it
 with the two constant maps into the two-element object, which agree after
 it vacuously -- there is nothing to evaluate them at -- hence agree
 outright, which they do not.  No choice principle and no case distinction
 on a proposition enters, only the emptiness of [Fin.t 0]. 

 --------
 分裂不同于正规性，它在空范畴中依然成立：从空对象出的满射也迫使其陪域为空。用两个映入双元素对象的恒等映射来探究它，它们在空映射之后勉强一致——因为没有可评价的对象——因此完全一致，而它们实际上并不一致。这里没有使用选择原理，也没有对命题进行情形区分，仅涉及 [Fin.t 0] 的空性。
*)

Lemma finset_epi_from_empty_absurd {n : nat} (f : 0%nat ~{FinSet}~> n) :
  Epic f → Fin.t n → False.
Proof.
  intros E b.
  destruct n as [| n'].
  - exact (Fin.case0 (fun _ => False) b).
  - pose proof (@epic _ _ _ f E 2%nat (fun _ => Fin.F1)
                  (fun _ => Fin.FS Fin.F1)
                  (fun a => Fin.case0 (fun _ => _) a)) as H.
    discriminate (H Fin.F1).
Qed.

(*
 So such an epimorphism splits vacuously: its codomain has no element to
 choose a preimage for. 

 --------
 因此这样的满同态自然而然地分裂：它的余域没有元素可以选择原像。
*)
Lemma finset_epi_from_empty_splits {n : nat} (f : 0%nat ~{FinSet}~> n) :
  Epic f → Retraction f.
Proof.
  intro E.
  exists (fun b => False_rect (Fin.t 0) (finset_epi_from_empty_absurd f E b)).
  intro b.
  exact (False_rect _ (finset_epi_from_empty_absurd f E b)).
Qed.

(*
 EVERY epimorphism of FinSet splits, with no hypothesis on the domain: the
 successor case is [finset_regular_pos] read back through
 [regular_epic_retraction], the zero case is the vacuous splitting above.
 Stated as a [match] on the domain so the retraction still reduces on
 closed input, as [finset_epi_split_computes] at the end of this file
 checks. 

 --------
 FinSet 的每一个满射都会分裂，不需要对定义域作任何假设：
 后继情况是通过 [regular_epic_retraction] 读取回 [finset_regular_pos]，实现分裂，零情况是上面提到的平凡分裂。
 在定义域上表述为 [match]，因此收缩仍然可以在封闭输入上简化，正如本文件末尾的 [finset_epi_split_computes] 所检查的那样。
*)
Definition finset_every_epi_splits {m n : nat} (f : m ~{FinSet}~> n) :
  Epic f → Retraction f :=
  match m return ∀ f : m ~{FinSet}~> n, Epic f → Retraction f with
  | O    => fun f E => finset_epi_from_empty_splits f E
  | S m' => fun f E => regular_epic_retraction f (finset_regular_pos f) E
  end f.

(* ------------------------------------------------------------------------ *)
(* * ** Non-vacuity I: regular, but neither a section nor a retraction / * ** 非空性 I：规则，但既不是截面也不是收回 *)

(*
 Every isomorphism is trivially regular, so an invertible witness would
 establish nothing.  [finset_shift3] is the self-map of a three-element set

 0 ↦ 2,  1 ↦ 2,  2 ↦ 0.

 It identifies 0 with 1 and it misses the value 1 entirely.  The first
 refutes any left inverse ([finset_shift3_not_section], by evaluating the
 left-inverse law at the two indices sharing an image) and the second any
 right inverse ([finset_shift3_not_retraction], by evaluating the
 right-inverse law at the missed value), so the arrow is neither a section
 nor a retraction, and a fortiori not an isomorphism
 ([finset_shift3_not_iso]).  Regularity nevertheless holds, by the finite
 search.

 Both refutations are DIRECT.  The tree does have the bridge that would let
 them go the long way round -- [finset_monic_iff_injective]
 (Instance/FinSet/Classifier.v) proves monic in FinSet is exactly
 injective, and [sections_are_monic] would finish the first half -- but
 taking it would place this file downstream of the subobject-classifier
 development for no gain, and there is no companion epi/surjective
 characterization for FinSet to run the second half through.

 The same two features are what put the search through its paces: the
 missed value forces the fallback, and the shared image forces a choice,
 resolved by taking the first index. 

 --------
 每个同构在形式上都是正则的，因此一个可逆证据什么也无法建立。[finset_shift3] 是一个三元素集合的自映射

 0 ↦ 2,  1 ↦ 2,  2 ↦ 0。

 它将 0 与 1 识别，并且完全没有取值 1。第一个反驳了任何左逆（通过在共享像的两个索引处评估左逆律，[finset_shift3_not_section]），第二个反驳了任何右逆（通过在被遗漏的值处评估右逆律，[finset_shift3_not_retraction]），所以该箭头既不是截面也不是收缩，从而也不是同构（[finset_shift3_not_iso]）。然而，通过有限搜索，正则性仍然成立。两个反驳都是直接的。树确实有桥可以让他们绕远路走——[finset_monic_iff_injective]（Instance/FinSet/Classifier.v）证明在 FinSet 中单射（monic）正好等于注射（injective），而 [sections_are_monic] 会完成前半部分——但采用它会使这个文件位于子对象分类器开发的下游而没有任何收益，而且 FinSet 没有伴随的满射（epi/surjective）特征来运行后半部分。

 同样的两个特征也是让搜索充分发挥作用的原因：缺失的值迫使采用回退（fallback），共享的映像迫使做出选择，这个选择通过取第一个索引来解决。
*)

Definition finset_shift3 : 3%nat ~{FinSet}~> 3%nat :=
  fun a =>
    Fin.caseS' a (fun _ => Fin.t 3)
      (Fin.FS (Fin.FS Fin.F1))
      (fun a1 =>
         Fin.caseS' a1 (fun _ => Fin.t 3)
           (Fin.FS (Fin.FS Fin.F1))
           (fun _ => Fin.F1)).

(*
 Exhaustive case analysis on a three-element index, needed to show that a
 value is missed by every argument. 

 --------
 对三元素索引进行详尽的情况分析，需要证明每个参数都会遗漏某个值。
*)
Lemma fin3_cases (a : Fin.t 3) :
  (a = Fin.F1) ∨ (a = Fin.FS Fin.F1) ∨ (a = Fin.FS (Fin.FS Fin.F1)).
Proof.
  apply (Fin.caseS' a
           (fun a => (a = Fin.F1) ∨ (a = Fin.FS Fin.F1)
                       ∨ (a = Fin.FS (Fin.FS Fin.F1)))).
  - now left.
  - intro b.
    apply (Fin.caseS' b
             (fun b => (Fin.FS b = Fin.F1) ∨ (Fin.FS b = Fin.FS Fin.F1)
                         ∨ (Fin.FS b = Fin.FS (Fin.FS Fin.F1)))).
    + right; now left.
    + (* the remaining index lives in [Fin.t 1], a singleton by [fin1_unique] (Instance/FinSet.v) / 剩余的索引存在于 [Fin.t 1] 中，由 [fin1_unique]（Instance/FinSet.v）单独表示 *)
      intro c.
      right; right.
      now rewrite (fin1_unique c).
Qed.

(* It is regular: the finite search supplies the pseudoinverse. / 它是正规的：有限的搜索提供了伪逆。 *)
Definition finset_shift3_regular : RegularMorphism finset_shift3 :=
  finset_regular_pos finset_shift3.

(*
 It is not injective -- indices 0 and 1 share an image -- so it has no left
 inverse. 

 --------
 它不是单射——索引 0 和 1 共享一个像——所以它没有左逆。
*)
Lemma finset_shift3_not_section : Section finset_shift3 → False.
Proof.
  intros [s Hs].
  (* s ∘ f ≈ id, evaluated at the two indices sharing an image / s ∘ f ≈ id，在两个共享像的索引处求值 *)
  pose proof (Hs Fin.F1) as H0.
  pose proof (Hs (Fin.FS Fin.F1)) as H1.
  simpl in H0, H1.
  (* both reduce to a statement about s applied to the SAME value / 都归结为关于 s 应用于相同值的陈述 *)
  rewrite H0 in H1.
  discriminate.
Qed.

(* It misses the value 1 entirely, so it has no right inverse. / 它完全缺少值1，因此它没有右逆。 *)
Lemma finset_shift3_not_retraction : Retraction finset_shift3 → False.
Proof.
  intros [r Hr].
  pose proof (Hr (Fin.FS Fin.F1)) as H.
  simpl in H.
  destruct (fin3_cases (r (Fin.FS Fin.F1))) as [E | [E | E]];
    rewrite E in H; discriminate.
Qed.

(*
 Hence not an isomorphism either: an inverse would in particular be a left
 inverse. 

 --------
 因此也不是同构：反函子特别来说会是一个左逆。
*)
Lemma finset_shift3_not_iso : IsIsomorphism finset_shift3 → False.
Proof.
  intros [g _ Hl].
  exact (finset_shift3_not_section (Build_Section _ _ finset_shift3 g Hl)).
Qed.

(* The exercise's point, packaged: regularity is strictly weaker than one-sided invertibility, and strictly weaker than invertibility. / 练习的要点，总结如下：规律性严格弱于单边可逆性，并且严格弱于可逆性。 *)
Definition finset_regular_not_split :
  RegularMorphism finset_shift3
  * (Section finset_shift3 → False)
  * (Retraction finset_shift3 → False)
  * (IsIsomorphism finset_shift3 → False) :=
  (finset_shift3_regular, finset_shift3_not_section,
   finset_shift3_not_retraction, finset_shift3_not_iso).

(* ------------------------------------------------------------------------ *)
(* * ** Non-vacuity II: a split pair whose idempotent is not the identity / * ** 非空性 II：一个其幂等元不是单位元的分裂对 *)

(*
 [split_pair_idempotent] (Theory/Morphisms.v) would say nothing if every
 available split pair made h ∘ g the identity.  A 1-element object beside a
 2-element one settles that: the point inclusion and the terminal map
 compose to the identity ONE WAY ONLY. 

 --------
 [split_pair_idempotent]（Theory/Morphisms.v）如果每一个可用的分裂对都使得 h ∘ g 成为恒等映射的话，就不会说任何东西。一个单元素对象与一个双元素对象并列解决了这个问题：点的包含映射和终端映射只以一种方式组成恒等映射。
*)

Definition finset_point : 1%nat ~{FinSet}~> 2%nat := fun _ => Fin.F1.
Definition finset_bang  : 2%nat ~{FinSet}~> 1%nat := fun _ => Fin.F1.
Definition finset_collapse : 2%nat ~{FinSet}~> 2%nat := fun _ => Fin.F1.

(* One composite is the identity of the 1-element object. / 一个复合是1元素对象的恒等式。 *)
Lemma finset_split_pair : finset_bang ∘ finset_point ≈ id.
Proof. intro i; exact (eq_sym (fin1_unique i)). Qed.

(* The other composite is [finset_collapse], on the nose. / 另一个复合物是 [finset_collapse]，正中目标。 *)
Lemma finset_point_bang : finset_point ∘ finset_bang ≈ finset_collapse.
Proof. intro i; reflexivity. Qed.

(* So the collapse is idempotent -- by the general lemma, not by hand. / 所以塌缩是幂等的——根据一般引理，而不是手动证明。 *)
Lemma finset_collapse_idempotent : Idempotent finset_collapse.
Proof.
  apply (idempotent_respects (finset_point ∘ finset_bang)).
  - exact finset_point_bang.
  - exact (split_pair_idempotent finset_bang finset_point finset_split_pair).
Qed.

(*
 And it is NOT the identity: it sends index 1 to index 0.  Without this the
 idempotence above would be witnessed by identities alone. 

 --------
 它不是恒等映射：它将索引 1 发送到索引 0。没有它，上述幂等性将仅由恒等映射来体现。
*)
Lemma finset_collapse_not_id : finset_collapse ≈ id → False.
Proof.
  intro H.
  pose proof (H (Fin.FS Fin.F1)) as H1.
  simpl in H1.
  discriminate.
Qed.

(*
 Mac Lane's [maclane:I.5:def5] over FinSet, packaged: a split pair, the
 identification of its OTHER composite with [finset_collapse], the
 idempotence of that composite, and the refutation that it is an identity.
 The second component is what ties the package to its own headline:
 [finset_collapse] is an independently defined constant, so without
 [finset_point_bang] the remaining three would say only that a split pair
 exists and that some non-identity idempotent exists, separately. 

 --------
 Mac Lane 的 [maclane:I.5:def5] 在 FinSet 上，打包：一个分裂对，它的另一个复合与 [finset_collapse] 的识别，该复合的幂等性，以及它不是恒等映射的反驳。第二个组成部分将该包与其自己的标题联系起来：[finset_collapse] 是一个独立定义的常量，因此如果没有 [finset_point_bang]，其余三个只能分别说明存在一个分裂对以及存在某个非恒等幂等元。
*)
Definition finset_split_pair_nontrivial :
  (finset_bang ∘ finset_point ≈ id)
  * (finset_point ∘ finset_bang ≈ finset_collapse)
  * Idempotent finset_collapse
  * (finset_collapse ≈ id → False) :=
  (finset_split_pair, finset_point_bang,
   finset_collapse_idempotent, finset_collapse_not_id).

(* ------------------------------------------------------------------------ *)
(** ** The search runs / ** 搜索正在运行 *)

(*
 The three behaviours of [fin_preimage] on [finset_shift3], each by
 [eq_refl], so the finite search is executable and not merely provable.  In
 order: a hit at a LATER index (the search scans past 0 and 1 before
 finding 2), a MISS (nothing maps to index 1, so the fallback in
 [finset_pseudoinverse] is what supplies the value), and a hit at index
 0 where two indices compete and the first wins. 

 --------
 [fin_preimage] 在 [finset_shift3] 上的三种行为，每种行为由 [eq_refl] 执行，因此有限搜索是可执行的，而不仅仅是可证明的。顺序如下：在较后的索引命中（搜索在找到 2 之前扫描 0 和 1），未命中（没有任何内容映射到索引 1，所以 [finset_pseudoinverse] 中的回退提供了值），以及在索引 0 的命中，两者索引竞争且第一个获胜。
*)

Example finset_preimage_late :
  fin_preimage finset_shift3 Fin.F1 = Some (Fin.FS (Fin.FS Fin.F1)) := eq_refl.

Example finset_preimage_miss :
  fin_preimage finset_shift3 (Fin.FS Fin.F1) = None := eq_refl.

Example finset_preimage_first :
  fin_preimage finset_shift3 (Fin.FS (Fin.FS Fin.F1)) = Some Fin.F1 := eq_refl.

(*
 The assembled pseudoinverse, evaluated at all three indices.  The middle
 value is the fallback -- [Fin.F1], the same one [finset_regular_pos]
 supplies -- because index 1 has an empty fibre. 

 --------
 组装的伪逆，在所有三个索引处进行评估。中间的值是备用值 -- [Fin.F1]，与 [finset_regular_pos] 提供的相同 -- 因为索引 1 的纤维为空。
*)
Example finset_pseudoinverse_computes :
  (finset_pseudoinverse Fin.F1 finset_shift3 Fin.F1,
   finset_pseudoinverse Fin.F1 finset_shift3 (Fin.FS Fin.F1),
   finset_pseudoinverse Fin.F1 finset_shift3 (Fin.FS (Fin.FS Fin.F1)))
  = (Fin.FS (Fin.FS Fin.F1), Fin.F1, Fin.F1) := eq_refl.

(*
 And the witness projected out of the regularity proof is that same
 program, at every index -- the [Defined] on [finset_regular] is what makes
 this hold by [eq_refl]. 

 --------
 而从规律性证明中投射出来的证据正是那个相同的程序，在每个索引——[Defined] 在 [finset_regular] 上正是通过 [eq_refl] 使得这一点成立的原因。
*)
Example finset_regular_witness_computes :
  (`1 finset_shift3_regular Fin.F1,
   `1 finset_shift3_regular (Fin.FS Fin.F1),
   `1 finset_shift3_regular (Fin.FS (Fin.FS Fin.F1)))
  = (Fin.FS (Fin.FS Fin.F1), Fin.F1, Fin.F1) := eq_refl.

(*
 [finset_every_epi_splits] computes too, so it is not vacuous on the side
 that matters.  [finset_bang] is epic -- everything out of the singleton is
 determined at [Fin.F1], which [finset_bang] hits -- and the retraction the
 theorem returns for it is the finite search's answer, by [eq_refl]. 

 --------
 [finset_every_epi_splits] 也进行计算，所以在重要的一方面它并非空洞。[finset_bang] 史诗般 —— 单例之外的一切都在 [Fin.F1] 被确定，而 [finset_bang] 命中它 —— 并且该定理为其返回的缩回是有限搜索的答案，由 [eq_refl] 得出。
*)

Lemma finset_bang_epic : Epic finset_bang.
Proof.
  constructor; intros z g1 g2 H i.
  rewrite (fin1_unique i).
  exact (H Fin.F1).
Qed.

Example finset_epi_split_computes :
  @retract _ _ _ _ (finset_every_epi_splits finset_bang finset_bang_epic) Fin.F1
  = Fin.F1 := eq_refl.
