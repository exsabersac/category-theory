Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Thin.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(*
   * * The free monoidal category on one generator

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §VII.2
   (book pp. 165-168): binary words [maclane:VII.2:def1], the category [W]
   [maclane:VII.2:construction1], and the freeness theorem
   [maclane:VII.2:thm1].
   nLab: https://ncatlab.org/nlab/show/coherence+theorem+for+monoidal+categories

   A monoidal category has a tensor that is associative and unital only UP TO
   coherent isomorphism, so an iterated tensor is not one object but a whole
   family of them, one per bracketing.  Mac Lane's device for studying that
   family is to make the bracketings themselves the objects of a category.  A
   BINARY WORD is a formal parenthesised product built from a single
   placeholder [(-)] and an empty slot [e0]; [W] has the binary words as
   objects and EXACTLY ONE arrow between any two words of the same length.

   That last clause is the whole point.  Because the hom is a proposition, any
   two parallel arrows of [W] are equal, so every diagram in [W] commutes for
   free — and a structure-preserving functor out of [W] must therefore send
   every diagram of bracket-shuffles to a commuting diagram downstream.  [W]
   is the walking (weak, non-symmetric) monoidal category on one object, and
   its universal property is a form of the coherence theorem.

   WHY THE HOM IS A LENGTH EQUATION.  We take [hom v w := wlen v = wlen w]
   and declare the hom-setoid equivalence to be the constantly-true relation,
   exactly as Instance/Proset.v does for a preorder.  Two consequences
   are load-bearing:

   - every law of a category, of a bifunctor, and of [Monoidal] — including
   the triangle and the pentagon — is an equation between PARALLEL arrows
   of [W], hence inhabited by [I] : True.  None of them costs a proof.
   This is [W_thin] below, and it is why this file contains no coherence
   argument at all: the coherence content of §VII.2 lives entirely in the
   FREENESS theorem, not in [W] itself.

   - [wlen] must be defined structurally with [+], not with an accumulator.
   Then [wlen (WT WE x)] is convertible with [wlen x] because [0 + n]
   reduces, so the left unitor of [W] is literally [eq_refl].  An
   accumulator-based length would break that conversion and force a cast
   into every unitor.

   SCOPE OF THIS FILE.  It supplies the reusable core: the word datatype, [W],
   and its monoidal structure.  Mac Lane's Theorem 1 — for a monoidal [B] and
   an object [b], a unique structure-preserving functor [W ⟶ B] sending the
   generator to [b] — is developed on top of this and is stated against STRICT
   monoidal functors, which is what Mac Lane's own statement means: his Moncat
   (§VII.1, [maclane:VII.1:construction2]) is “the category of all small
   monoidal categories with strict morphisms as arrows”, and his strict
   morphism ([maclane:VII.1:def3]) is required to carry alpha, lambda and rho
   to alpha', lambda' and rho' on the nose.  Uniqueness among merely STRONG
   monoidal functors is false, so the strict reading is not a weakening but
   the only one under which Theorem 1 can hold.

   The word datatype is exported as a standalone [Set] on purpose: §VII.2's
   coherence corollary and the §XI word-functor development both need to
   recurse over the same words. 

   --------
   * * 单生成自由幺半范畴

   Mac Lane，《为工作数学家准备的范畴论》，第二版，§VII.2（书页 165-168）：二进制字 [maclane:VII.2:def1]，范畴 [W] [maclane:VII.2:construction1]，以及自由性定理 [maclane:VII.2:thm1]。
   nLab: https://ncatlab.org/nlab/show/coherence+theorem+for+monoidal+categories

   一个幺半范畴具有一个张量积，该张量积仅在同构协调下是结合的并且有单位，因此迭代张量积不是一个对象，而是一整个对象族，每个括号形式对应一个对象。Mac Lane 用于研究该族的方法是将括号形式本身作为一个范畴的对象。
   二进制字是由单一占位符 [(-)] 和一个空槽 [e0] 构建的正式带括号的乘积；[W] 以这些二进制字作为对象，并且在同长度的任意两个字之间恰好有一条箭头。最后一句话就是关键。因为 hom 是一个命题，[W] 中的任意两条平行箭头都是相等的，因此 [W] 中的每个图表都是自动交换的——因此，从 [W] 出发的保持结构的函子必须将每一个括号乱排的图表发送为下游的交换图表。[W] 是在一个对象上的行走（弱的、非对称的）单类范畴，它的泛性质是一种相干性定理的形式。

   为什么 hom 是长度等式。我们取 [hom v w := wlen v = wlen w] 并声明 hom-集等价为恒真关系，正如 Instance/Proset.v 对偏序集所做的一样。有两个后果是至关重要的：- 每个类别、双函子以及 [Monoidal] 的定律——包括三角形和五边形——都是 [W] 的平行箭头之间的方程，因此由 [I] 居住：正确。它们都不需要证明。这如下所示 [W_thin]，这也是为什么该文件完全不包含一致性论证的原因：第 VII.2 节的一致性内容完全存在于 FREENESS 定理中，而不在 [W] 本身。 

   - [wlen] 必须使用 [+] 以结构方式定义，而不是使用累加器。然后 [wlen (WT WE x)] 可以与 [wlen x] 互换，因为 [0 + n] 可化简，所以 [W] 的左单元器字面上就是 [eq_refl]。基于累加器的长度会破坏该转换，并迫使每个单元器进行类型转换。本文件的范围。它提供了可重用的核心：词数据类型 [W] 及其幺半群结构。Mac Lane 的定理 1 —— 对于一个幺半群 [B] 和一个对象 [b]，一个唯一的保持结构的函子 [W ⟶ B] 将生成元映射到 [b] —— 是在此基础上发展的，并且是针对严格幺半群函子陈述的，这正是 Mac Lane 自己的陈述意义：他的 Moncat (§VII.1, [maclane:VII.1:construction2]) 是“所有小型幺半群范畴，箭头为严格态射的范畴”，而他的严格态射 ([maclane:VII.1:def3]) 被要求精确地将 alpha、lambda 和 rho 映射到 alpha'、lambda' 和 rho'。仅在强幺半群函子中唯一性不成立，因此严格解读并非弱化，而是定理 1 能成立的唯一情形。术语 datatype 被故意作为独立的 [Set] 导出：§VII.2 的连贯推论和 §XI 的词函子开发都需要对相同的词进行递归。
*)

(** ** Binary words / ** 二进制词 *)

(*
 [maclane:VII.2:def1].  [WE] is the empty word e0, [WI] the single generator
 (-), and [WT] the formal tensor. 

 --------
 [maclane:VII.2:def1] . [WE] 是空字 e0，[WI] 单生成元 (-)，[WT] 是形式张量。
*)
Inductive Word : Set :=
  | WE : Word
  | WI : Word
  | WT : Word → Word → Word.

(*
 Structural, with [+] — see the header note on conversion. 

 --------
 结构上的，带有 [+] — 参见关于转换的标题说明。
*)
Fixpoint wlen (w : Word) : nat :=
  match w with
  | WE      => 0
  | WI      => 1
  | WT v u  => wlen v + wlen u
  end.

(* The right-normalised word of each length. / 每个长度的右归一化单词。 *)
Fixpoint nfword (n : nat) : Word :=
  match n with
  | O   => WE
  | S k => WT WI (nfword k)
  end.

Lemma wlen_nfword (n : nat) : wlen (nfword n) = n.
Proof. induction n; simpl; auto. Qed.

(*
   * ** A generic helper: the tensor of two isomorphisms

   Stated over an arbitrary monoidal category because both [W] below and the
   target [B] of the freeness theorem use it.  It duplicates the [iso_bimap]
   of Structure/Monoidal/Drinfeld.v on purpose: importing Drinfeld here
   would drag half-braidings into every consumer of the word datatype, and
   Drinfeld is not edited by this development. 

   --------
   * ** 一个通用助手：两个同构的张量

   在任意单oidal范畴上陈述，因为下面的  [W]  和自由性定理的目标  [B]  都使用它。它故意重复了 Structure/Monoidal/Drinfeld.v 中的  [iso_bimap] ：如果在这里导入 Drinfeld，会把半编织（half-braidings）引入到每一个使用 word 类型的地方，而且 Drinfeld 并不在此开发中被编辑。
*)
Program Definition tensor_iso {C : Category} `{@Monoidal C} {x y z w : C}
  (i : x ≅ y) (j : z ≅ w) : (x ⨂ z) ≅ (y ⨂ w) := {|
  to   := to i ⨂ to j;
  from := from i ⨂ from j
|}.
Next Obligation.
  rewrite <- bimap_comp, !iso_to_from; now rewrite bimap_id_id.
Qed.
Next Obligation.
  rewrite <- bimap_comp, !iso_from_to; now rewrite bimap_id_id.
Qed.

(** ** The category W / ** 类别 W *)

(*
 One arrow per pair of equal-length words.  The hom is a proposition and the
 hom-setoid identifies everything parallel, so [W] is thin by construction. 

 --------
 每对等长单词一个箭头。hom 是一个命题，hom-集合体将所有平行的东西标识出来，因此 [W] 按构造来说是薄的。
*)
Program Definition W : Category := {|
  obj     := Word;
  hom     := fun v w => wlen v = wlen w;
  homset  := fun _ _ => {| Setoid.equiv := fun _ _ => True |};
  id      := fun _ => eq_refl;
  compose := fun _ _ _ f g => eq_trans g f
|}.

(*
 Every law of [W] — and, below, of its tensor and of [Monoidal] — is an
 equation between parallel arrows, so this single lemma discharges them all. 

 --------
 [W] 的每一条定律——以及下面其张量和 [Monoidal] 的定律——都是平行箭头之间的等式，所以这个单一引理解决了它们所有的问题。
*)
Definition W_thin : Thin W.
Proof. intros x y f g; constructor. Defined.

(*
 Mac Lane's W is a preorder-groupoid: the arrow backwards always exists. 

 --------
 Mac Lane 的 W 是一个预序-群类：箭头总是存在反向。
*)
Definition W_iso {v w : Word} (f : v ~{W}~> w) : v ≅[W] w :=
  thin_iso W_thin f (eq_sym f).

(** ** The monoidal structure / ** 单体结构 *)

Program Definition W_tensor : W ∏ W ⟶ W := {|
  fobj := fun p => WT (fst p) (snd p);
  fmap := fun _ _ f => f_equal2 Nat.add (fst f) (snd f)
|}.

(*
 [unit_left] is [eq_refl] because [0 + n] reduces; [unit_right] and
 [tensor_assoc] are the corresponding [Nat] facts.  Thinness supplies
 uniqueness of each arrow, [Nat] arithmetic supplies its existence. 

 --------
 [unit_left] 是 [eq_refl] 因为 [0 + n] 减少；[unit_right] 和 [tensor_assoc] 是相应的 [Nat] 事实。瘦弱提供每个箭头的唯一性，[Nat] 算术提供它的存在。
*)
#[export] Program Instance W_Monoidal : @Monoidal W := {|
  I            := WE;
  tensor       := W_tensor;
  (*
 The endpoints are pinned explicitly: left to inference, [Program] reads
 them off [eq_refl] and then cannot match [x] against [I ⨂ x]. 

 --------
 端点被明确固定：左边用于推断，[Program] 从 [eq_refl] 中读取它们，然后无法将 [x] 与 [I ⨂ x] 匹配。
*)
  unit_left    := fun x => @thin_iso W W_thin (WT WE x) x eq_refl eq_refl;
  unit_right   := fun x => @thin_iso W W_thin (WT x WE) x
                             (Nat.add_0_r (wlen x))
                             (eq_sym (Nat.add_0_r (wlen x)));
  tensor_assoc := fun x y z =>
    @thin_iso W W_thin (WT (WT x y) z) (WT x (WT y z))
      (eq_sym (Nat.add_assoc (wlen x) (wlen y) (wlen z)))
      (Nat.add_assoc (wlen x) (wlen y) (wlen z))
|}.

(*
 Every remaining obligation — the six naturality fields, the triangle and the
 pentagon — is an equation between parallel arrows of [W], so thinness closes
 all of them uniformly.  This is the whole reason the file carries no
 coherence argument. 

 --------
 每一个剩余的义务——六个自然性域、三角形和五边形——都是 [W] 中平行箭头之间的方程，因此薄性统一地关闭了它们所有。这就是该文件没有包含任何相干性论证的全部原因。
*)
Solve All Obligations with (intros; constructor).

(*
   * ** Acceptance tests

   Everything here computes; the point of stating them is that the
   definitional facts the header claims really are definitional. 

   --------
   * ** 验收测试

   这里的每一项都是可计算的；说明它们的目的在于确认标题所声称的定义性事实确实是定义性的。
*)

Example wlen_WE  : wlen WE = 0%nat := eq_refl.
Example wlen_WI  : wlen WI = 1%nat := eq_refl.
Example wlen_mix : wlen (WT (WT WI WE) WI) = 2%nat := eq_refl.

Example nfword_3 : nfword 3 = WT WI (WT WI (WT WI WE)) := eq_refl.

(* The tensor of [W] is the word constructor, on the nose. / [W] 的张量就是字词构造器，正中要点。 *)
Example W_tensor_obj (v w : Word) :
  (v ⨂[W_Monoidal] w)%object = WT v w := eq_refl.

(*
 The unit is the empty word, and the left unitor is [eq_refl] — the
 conversion the header's [wlen] note is about. 

 --------
 单位是空字，而左单位元是 [eq_refl]——这是标题的 [wlen] 注释所涉及的转换。
*)
Example W_unit_is_WE : @I W W_Monoidal = WE := eq_refl.
Example W_unit_left_is_refl (x : Word) :
  to (@unit_left W W_Monoidal x) = eq_refl := eq_refl.

(*
 Thinness, as it is actually used: ANY two parallel arrows of [W] agree, so
 every diagram of [W] commutes.  This is the property the freeness theorem
 will consume. 

 --------
 稀薄性，按其实际用法：[W] 中的任意两条平行箭头都相同，因此 [W] 的每个图都是可交换的。这就是自由性定理将要利用的性质。
*)
Example W_thin_concrete (v w : Word) (f g : v ~{W}~> w) : f ≈ g := W_thin v w f g.

(*
 And the arrows really are the length equations, so [W] is a groupoid. 

 --------
 而这些箭头实际上就是长度方程，所以 [W] 是一个群族。
*)
Example W_iso_concrete : WT (WT WI WE) WI ≅[W] WT WI (WT WI WE) :=
  W_iso (v:=WT (WT WI WE) WI) (w:=WT WI (WT WI WE)) eq_refl.
