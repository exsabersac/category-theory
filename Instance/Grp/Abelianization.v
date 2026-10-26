Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.Center.
Require Import Category.Instance.Grp.Quotient.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(*
   * * The commutator subgroup and the abelianization functor

   Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §I.3
   (printed p. 14) and §I.4 (printed pp. 16–17)
   [maclane:I.3:construction3, maclane:I.4:construction2]: the
   commutator subgroup [G, G] is functorial in G — homomorphisms carry
   commutators to commutators — and the factor-commutator group
   G ↦ G/[G, G] is the abelianization functor Grp ⟶ Ab, with the
   projections p_G : G → G/[G, G] a natural transformation from the
   identity functor.
   nLab: https://ncatlab.org/nlab/show/abelianization

   THE SETOID QUOTIENT.  In this library a quotient group needs no new
   carrier: G/[G, G] is G's carrier under the COARSER equivalence
   a ≈' b iff a·b⁻¹ lies in the commutator subgroup ([abel_eq]).  The
   commutator subgroup itself is the inductively generated closure
   [InCommutator]: commutators, the unit, products, inverses, and a
   setoid-respect constructor (generation must be ≈-saturated for the
   quotient relation to be well defined over setoid carriers).  The
   quotient relation is an equivalence by the group laws, the
   operations respect it by NORMALITY — the conjugate of a commutator
   element is again one, an instance of the single induction
   [hom_commutator] (every homomorphism pushes [InCommutator] forward)
   applied to the conjugation homomorphisms [Grp_conj] of
   Instance/Grp/TwoFunctors.v — and commutativity of the quotient is
   the constructor [inc_comm] itself: (a·b)·(b·a)⁻¹ IS a commutator.

   THE TWO FUNCTORS.  [Commutator_Functor : Grp ⟶ Grp] restricts each
   homomorphism to the subgroup (the sigma carrier over
   [InCommutator], compared on elements, as Instance/Grp/Center.v does
   for the center); [Abelianization_Functor : Grp ⟶ Ab] sends G to
   [AbelianizationOb G] — same carrier, coarser setoid, commutative by
   construction — and a homomorphism to itself, [hom_commutator]
   making it respect the quotient relations.  [Ab_to_Grp : Ab ⟶ Grp]
   is the evident inclusion (an abelian group is a group), built here
   since no Ab → Grp bridge existed in tree.

   THE NATURAL PROJECTION ([abel_projection]): the family
   p_G : G → G/[G, G] as a [Transform] from Id[Grp] to
   Ab_to_Grp ◯ Abelianization_Functor.  Because the quotient reuses
   the carrier, every component is the identity function and both
   naturality squares hold by reflexivity of the coarser relation —
   Mac Lane's square p_H ∘ f ≈ f' ∘ p_G with no computation left.

   TOWARD THE ADJUNCTION (the issue's optional stretch, left to a
   future change tying into Construction/Reflective.v): the germ is
   [hom_to_abelian_kills] — a homomorphism from G into (the underlying
   group of) an abelian group sends every commutator element to the
   unit, by a second induction over the same generation — which is
   exactly why such homomorphisms descend along p_G; the adjunction
   Abelianization ⊣ Ab_to_Grp packages that descent and is not built
   here.  CORRECTION (#370): the tie into Construction/Reflective.v now
   exists, in Instance/Grp/Abelianize/Reflective.v
   ([Ab_Reflective_in_Grp]); the adjunction itself is
   Instance/Grp/Abelianize.v's.

   SCOPE OF THE QUOTIENT — THE EXTRACTION HAS NOW BEEN CARRIED OUT.
   This paragraph previously disclosed that the quotient here was
   SPECIALIZED to [InCommutator], that the five congruence proofs
   below consume only the normal-subgroup interface (≈-saturation,
   unit, closure under product and inverse, normality), that a
   generic [NormalSubgroup]-quotient was therefore extractable by
   abstraction over exactly those five facts, and that unifying the
   tree's quotient constructions was future work.

   Instance/Grp/Quotient.v (issue #313) performs that extraction.
   [Subgroup] and [NormalSubgroup] there are exactly those five laws;
   [CommutatorNS] below packages [InCommutator] as one, using the
   five facts this file already proved and adding nothing; and
   [abel_eq] is [quot_rel] at that normal subgroup ([abel_eq_is_quot_rel]).
   An earlier revision added “by convertibility”: since the PR “algebraic
   carriers are sets” (2026-09-17) the two are separated by one [inhabited],
   so the identification is up to the propositional truncation and is stated
   so at [eq_refl] there.  The six lemmas that follow keep their statements
   unchanged and are one-line citations of the generic ones, each gaining a
   [constructor] or a [destruct], so this file still carries no quotient
   construction of its own.

   THE OTHER TWO CONSTRUCTIONS the paragraph named are NOT unified,
   and re-reading their record types shows why the count of “three
   unshared quotient constructions” was itself imprecise.
   Instance/Grp/Epi.v's [Grp_Coset] is a [SetoidObject] and not a
   [GrpObject] at all: it is the coset space of the image of an
   arbitrary homomorphism, and that file's argument exists precisely
   for the case where the image is NOT normal (its header and two
   later passages say so).  It is therefore not an instance of a
   normal-subgroup
   quotient and cannot be made one.  Instance/Ab.v's
   [ab_coset_eq] IS a quotient group, but of an [AbObject], and Ab.v
   sits upstream of Instance/Grp.v with the only bridge
   ([Ab_to_GrpOb]) living in this file; routing it through
   Instance/Grp/Quotient.v would move that bridge upstream and give
   Ab.v a dependency on Grp.  That is left undone deliberately.  (An
   earlier revision of that sentence cited Instance/Ab.v, where the
   definition stood before the PR “algebraic carriers are sets”
   (2026-09-17); the same PR also made [ab_coset_eq] a [Prop] -- it is
   Coq's [ex] now, not a [Type]-valued sigma -- which is the shape
   [abel_eq] here has too.)

   NON-DEGENERACY, witnessed: [commutator_GrpTwo_proper] (in an
   abelian group the subgroup omits the nonidentity),
   [commutator_S3_nontrivial] (in S₃ it contains a nonidentity
   element), and [abelianization_S3_nontrivial] (the quotient of the
   nonabelian S₃ does not collapse: the reflection stays apart from
   the unit, seen through the sign character). 

   --------
   * * 交换子子群与阿贝尔化函子

   Mac Lane，《为工作的数学家而写的范畴论》，第2版，§I.3
   （印刷页14）和§I.4（印刷页16–17）
   [maclane:I.3:construction3, maclane:I.4:construction2]：交换子子群 [G, G] 在群 G 中是函子性的——同态将交换子映射为交换子——并且因子交换子群
   G ↦ G/ [G, G] 是阿贝尔化函子 Grp ⟶ Ab，其投影 p_G : G → G/ [G, G] 是从恒等函子到自身的自然变换。
   nLab: https://ncatlab.org/nlab/show/abelianization集合商。在这个库中，一个商群不需要新的载体：G/ [G, G] 是 G 在更粗等价下的载体，即 a ≈' b 当且仅当 a·b⁻¹ 位于换位子群（[abel_eq]）中。换位子群本身是归纳生成的闭包 [InCommutator]：换位子，单位元，乘积，逆元，以及一个保持集合等价的构造器（为了使商关系在集合载体上定义良好，生成必须是 ≈-饱和的）。商关系是由群的公理决定的一个等价关系，操作遵守它通过正规性——换句话说，交换子元素的共轭仍然是一个交换子，这是在共轭同态  [Grp_conj]  上应用单归纳法  [hom_commutator]  (每个同态都会将  [InCommutator]  推前) 的一个实例 — 并且商的可交换性就是构造子  [inc_comm] 本身：(a·b)·(b·a)⁻¹ 是一个交换子。两个函子。[Commutator_Functor : Grp ⟶ Grp] 将每个同态限制到子群（σ 承载在 [InCommutator] 上，对于元素进行比较，就像 Instance/Grp/Center.v 对中心所做的那样）；[Abelianization_Functor : Grp ⟶ Ab] 将 G 映射到 [AbelianizationOb G]——相同的承载，更粗的等价集合，由构造可交换——并将同态映射到自身，[hom_commutator] 使其遵守商关系。[Ab_to_Grp : Ab ⟶ Grp] 是显而易见的包含（一个阿贝尔群是一个群），这里构建它是因为树中不存在 Ab → Grp 的桥梁。自然变换（[abel_projection]）：族 p_G : G → G/[G, G] 作为从 Id [Grp] 到 Ab_to_Grp ◯ Abelianization_Functor 的 [Transform]。由于商复用了载体，每个分量都是恒等函数，并且两个自然性方格都通过粗糙关系的自反性成立——Mac Lane 的方格 p_H ∘ f ≈ f' ∘ p_G，无需计算。关于附加（该问题的可选扩展，留待将来与 Construction/Reflective.v 关联更改）：其核心是 [hom_to_abelian_kills]——从 G 到阿贝尔群（的底层群）的同态会将每个交换子元素映射到单位元素，通过对相同生成的第二次归纳——这正是为什么这样的同态能够沿 p_G 下行；附加 Abelianization ⊣ Ab_to_Grp 封装了该下行过程，但在此未构建。修正（#370）：现在在 Instance/Grp/Abelianize/Reflective.v（[Ab_Reflective_in_Grp]）中存在与 Construction/Reflective.v 的关联；附加本身是 Instance/Grp/Abelianize.v 的。商的范围——提取现在已经完成。
   本段先前披露了这里的商是专门针对 [InCommutator] 的，下述五个同余证明仅使用了正规子群接口（≈-饱和、单位、乘积和逆的闭合性、正规性），因此，可以通过对这五个事实进行抽象提取出一个通用的 [NormalSubgroup] 商，并且统一树的商构造是未来的工作。Instance/Grp/Quotient.v（问题 #313）执行该提取。
   [Subgroup] 和 [NormalSubgroup] 那里正好有这五条定律；
   [CommutatorNS] 将下面的 [InCommutator] 打包为一个，使用该文件已证明的五个事实且不添加任何内容；
   [abel_eq] 是在那个正规子群 ([abel_eq_is_quot_rel]) 的 [quot_rel]。
   早期的修订增加了“通过可转换性”：自从 PR“代数承载是集合”（2026-09-17）以来，这两者被一个 [inhabited] 隔开，因此识别只能到命题截断，并在 [eq_refl] 处注明。接下来的六个引理保持其陈述不变，并且是对通用引理的一行引用，每个获得一个 [constructor] 或 [destruct]，因此该文件仍然没有自己的商构造。段落中提到的另外两个构造并不是统一的，重新阅读它们的记录类型就能看出，为何“三个非共享商构造”的计数本身是不精确的。Instance/Grp/Epi.v 的 [Grp_Coset] 实际上是一个 [SetoidObject]，而完全不是 [GrpObject]：它是任意同态的像的陪集空间，并且该文件的参数的存在恰好是为了处理像不是正规子群的情况（其标题和后面的两处内容都有说明）。因此，它不是一个正规子群商的实例，也无法被改造成一个正规子群商。Instance/Ab.v 的 [ab_coset_eq] 是一个商群，但它属于一个 [AbObject]，Ab.v 位于 Instance/Grp.v 的上游，唯一的桥梁（[Ab_to_GrpOb]）存在于此文件中；如果通过 Instance/Grp/Quotient.v 进行路由，会将该桥梁上移，并使 Ab.v 依赖于 Grp。这一操作被故意保留未完成。（该句的早期版本引用了 Instance/Ab.v，当时定义是在 PR “代数载体是集合” 之前（2026-09-17）；同一 PR 还将 [ab_coset_eq] 变为 [Prop] —— 它现在是 Coq 的 [ex]，而不是 [Type] 值的 sigma —— 这里的 [abel_eq] 也具有相同的形状。）非退化，见证：[commutator_GrpTwo_proper]（在阿贝尔群中，该子群省略非单位元素）、[commutator_S3_nontrivial]（在S₃中，它包含非单位元素）、以及[abelianization_S3_nontrivial]（非阿贝尔的S₃的商群不会坍缩：通过符号特征可以看到反射元素与单位元素保持分离）。
*)

(* * ** Commutators and the generated subgroup / * ** 交换子及生成的子群 *)

Definition gcomm (G : GrpObject) (g h : carrier G) : carrier G :=
  grp_mul G (grp_mul G (grp_mul G g h) (grp_inv G g)) (grp_inv G h).

(* The commutator subgroup, as an ≈-saturated inductive generation. / 换位子群，作为≈-饱和归纳生成。 *)
Inductive InCommutator (G : GrpObject) : carrier G → Type :=
  | inc_comm (g h : carrier G) : InCommutator (gcomm G g h)
  | inc_unit : InCommutator (grp_unit G)
  | inc_mul (a b : carrier G) :
      InCommutator a → InCommutator b →
      InCommutator (grp_mul G a b)
  | inc_inv (a : carrier G) :
      InCommutator a → InCommutator (grp_inv G a)
  | inc_resp (a b : carrier G) :
      a ≈ b → InCommutator a → InCommutator b.

Arguments inc_comm {G} g h.
Arguments inc_unit {G}.
Arguments inc_mul {G a b} _ _.
Arguments inc_inv {G a} _.
Arguments inc_resp {G a b} _ _.

(* Every homomorphism pushes the commutator subgroup forward: the one induction that serves functoriality, normality (via [Grp_conj]), and the descent germ below. / 每个同态都会将换位子群向前推进：这是唯一的归纳，它用于函子性、正规性（通过 [Grp_conj]）以及下面的下降芽。 *)
Lemma hom_commutator {G H : GrpObject} (f : GrpHom G H)
  (x : carrier G) : InCommutator G x → InCommutator H (grp_map f x).
Proof.
  intro Hx; induction Hx as
    [ g h | | a b Ha IHa Hb IHb | a Ha IHa | a b Hab Ha IHa ].
  - apply (inc_resp (a := gcomm H (grp_map f g) (grp_map f h))).
    + unfold gcomm.
      rewrite <- !(grp_map_inv f).
      rewrite <- !(grp_map_mul f).
      reflexivity.
    + apply inc_comm.
  - exact (inc_resp (symmetry (grp_map_unit f)) inc_unit).
  - exact (inc_resp (symmetry (grp_map_mul f a b)) (inc_mul IHa IHb)).
  - exact (inc_resp (symmetry (grp_map_inv f a)) (inc_inv IHa)).
  - exact (inc_resp (proper_morphism (grp_map f) a b Hab) IHa).
Qed.

(* Normality, as the conjugation instance. / 正常性，作为结合的实例。 *)
Lemma conj_commutator (G : GrpObject) (t x : carrier G) :
  InCommutator G x →
  InCommutator G (grp_mul G (grp_mul G t x) (grp_inv G t)).
Proof. exact (hom_commutator (Grp_conj G t) x). Qed.

(*
 Homomorphisms into abelian groups kill commutator elements — the
 descent germ for the (future) adjunction. 

 --------
 到阿贝尔群的同态会消灭对易子元素——（未来）伴随关系的下降芽。
*)
Lemma hom_to_abelian_kills {G H : GrpObject}
  (comm : ∀ a b : carrier H, grp_mul H a b ≈ grp_mul H b a)
  (f : GrpHom G H) (x : carrier G) :
  InCommutator G x → grp_map f x ≈ grp_unit H.
Proof.
  intro Hx; induction Hx as
    [ g h | | a b Ha IHa Hb IHb | a Ha IHa | a b Hab Ha IHa ].
  - unfold gcomm.
    rewrite !(grp_map_mul f), !(grp_map_inv f).
    rewrite (grp_mul_assoc H (grp_map f g) (grp_map f h)
               (grp_inv H (grp_map f g))).
    rewrite (comm (grp_map f h) (grp_inv H (grp_map f g))).
    rewrite <- (grp_mul_assoc H (grp_map f g) (grp_inv H (grp_map f g))
                  (grp_map f h)).
    rewrite (grp_mul_inv_r H (grp_map f g)).
    rewrite (grp_mul_unit_l H (grp_map f h)).
    apply (grp_mul_inv_r H).
  - apply (grp_map_unit f).
  - rewrite (grp_map_mul f a b).
    rewrite IHa, IHb.
    apply (grp_mul_unit_l H).
  - rewrite (grp_map_inv f a).
    rewrite IHa.
    apply (grp_inv_unit H).
  - now rewrite <- (proper_morphism (grp_map f) a b Hab).
Qed.

(* * ** The commutator subgroup as a normal subgroup / * ** 作为正规子群的换位子群 *)

(*
 The five facts above and in [Instance/Grp.v], packaged as
 Instance/Grp/Quotient.v's interface.  Nothing new is proved: the
 fields ARE [inc_resp], [inc_unit], [inc_mul], [inc_inv] and
 [conj_commutator]. 

 --------
 上述五个事实以及在 [Instance/Grp.v] 中的内容，被打包为 Instance/Grp/Quotient.v 的接口。没有新的内容被证明：字段是 [inc_resp]、[inc_unit]、[inc_mul]、[inc_inv] 和 [conj_commutator]。
*)
Definition CommutatorNS (G : GrpObject) : NormalSubgroup G :=
  {| ns_sub := {| sub_mem := InCommutator G
                ; sub_resp := fun a b Hab Ha => inc_resp Hab Ha
                ; sub_unit := inc_unit
                ; sub_mul := fun a b Ha Hb => inc_mul Ha Hb
                ; sub_inv := fun a Ha => inc_inv Ha |}
   ; ns_conj := fun t a Ha => conj_commutator G t a Ha |}.

(** ** The quotient relation / ** 商关系 *)

(*
 Since the PR “algebraic carriers are sets” (2026-09-17) the abelianization
 is an [AbObject] and so owes [cmon_prop], which forces its equality to be a
 [Prop].  [InCommutator] STAYS [Type]-valued -- it is the membership
 predicate of the commutator subgroup, [sub_mem] of [CommutatorNS] above,
 and the leastness arguments read witnesses out of it -- and [abel_eq] is
 its PROPOSITIONAL TRUNCATION, exactly as Instance/Mod/Quotient.v's
 [mquot_rel] is the truncation of [smod_mem].

 AN EARLIER PLAN for this phase predicted that the abelianization would have
 to take a [PropEquiv] as a hypothesis until [GrpObject] carries [grp_prop],
 on the ground that a [Prop] mirror of [abel_eq] would need to eliminate a
 [Prop] back into the [Type]-valued [InCommutator].  Truncating [abel_eq]
 ITSELF avoids that: there is nothing to go back to, and the two places that
 consume the relation land either in a [Prop] goal (the functor's
 respectfulness obligation) or in an `≈` at an [AbObject], which carries its
 own [cmon_prop] ([abel_kills] in Instance/Grp/Abelianize.v).  Taking the
 hypothesis instead was also measured to be fatal: as a section variable it
 pins [Grp]'s object universe, and [S3] is then refused. 

 --------
 自从 PR “代数载体是集合” (2026-09-17) 以来，阿贝尔化是一个 [AbObject]，因此欠 [cmon_prop]，这迫使其相等为一个 [Prop]。[InCommutator] 保持 [Type] 值 —— 它是交换子子群的成员谓词，即上面的 [sub_mem] 对应 [CommutatorNS]，并且最小性论证从中读取证人 —— [abel_eq] 是它的命题截断，正如 Instance/Mod/Quotient.v 中的 [mquot_rel] 是 [smod_mem] 的截断一样。该阶段的早期计划预测，阿贝尔化将不得不将 [PropEquiv] 作为假设，直到 [GrpObject] 承载 [grp_prop]，其理由是 [Prop] 的 [abel_eq] 镜像需要将 [Prop] 消除回 [Type] 值的 [InCommutator]。截断 [abel_eq] 本身可以避免这一点：没有回去的对象，并且消耗该关系的两个位置要么位于 [Prop] 目标中（函子所承担的尊重义务），要么位于 `≈` 的 [AbObject] 中，它承载着自身的 [cmon_prop]（在 Instance/Grp/Abelianize.v 中为 [abel_kills]）。将其作为假设也被认为是致命的：作为节变量，它固定了 [Grp] 的对象宇宙，然后 [S3] 就被拒绝了。
*)
Definition abel_eq (G : GrpObject) (a b : carrier G) : Prop :=
  inhabited (InCommutator G (grp_mul G a (grp_inv G b))).

(*
 [abel_eq] is the TRUNCATION of the generic quotient relation at
 [CommutatorNS].  An earlier revision read
 [abel_eq G a b = quot_rel (CommutatorNS G) a b] at [eq_refl]; the two are
 now separated by [inhabited], and the identification is stated up to it.
 The six one-line proofs below each gain a [constructor] or a [destruct]. 

 --------
 [abel_eq] 是在 [CommutatorNS] 处对通用商关系的截断。之前的修订在 [eq_refl] 处写为 [abel_eq G a b = quot_rel (CommutatorNS G) a b]；现在两者被 [inhabited] 隔开，并且标识一直说明到此为止。下面的六个单行证明各自获得一个 [constructor] 或一个 [destruct]。
*)
Example abel_eq_is_quot_rel (G : GrpObject) (a b : carrier G) :
  abel_eq G a b = inhabited (quot_rel (CommutatorNS G) a b).
Proof. reflexivity. Qed.

(* The finer relation implies the coarser one. / 更精细的关系暗示着更粗糙的关系。 *)
Lemma abel_eq_of_eq (G : GrpObject) (a b : carrier G) :
  a ≈ b → abel_eq G a b.
Proof. intro H; constructor; exact (quot_rel_of_equiv (CommutatorNS G) a b H). Qed.

Lemma abel_eq_refl (G : GrpObject) (a : carrier G) : abel_eq G a a.
Proof. constructor; exact (quot_rel_refl (CommutatorNS G) a). Qed.

Lemma abel_eq_sym (G : GrpObject) (a b : carrier G) :
  abel_eq G a b → abel_eq G b a.
Proof. intros [H]; constructor; exact (quot_rel_sym (CommutatorNS G) a b H). Qed.

Lemma abel_eq_trans (G : GrpObject) (a b c : carrier G) :
  abel_eq G a b → abel_eq G b c → abel_eq G a c.
Proof.
  intros [H1] [H2]; constructor.
  exact (quot_rel_trans (CommutatorNS G) a b c H1 H2).
Qed.

(*
 The operations respect the quotient relation; multiplication and
 inversion are where normality earns its keep. 

 --------
 这些运算遵守商关系；乘法和逆运算正是正规性发挥作用的地方。
*)
Lemma abel_eq_mul (G : GrpObject) (a a' b b' : carrier G) :
  abel_eq G a a' → abel_eq G b b' →
  abel_eq G (grp_mul G a b) (grp_mul G a' b').
Proof.
  intros [H1] [H2]; constructor.
  exact (quot_rel_mul (CommutatorNS G) a a' b b' H1 H2).
Qed.

Lemma abel_eq_inv (G : GrpObject) (a a' : carrier G) :
  abel_eq G a a' → abel_eq G (grp_inv G a) (grp_inv G a').
Proof.
  intros [H]; constructor.
  exact (quot_rel_inv (CommutatorNS G) a a' H).
Qed.

(** ** The abelianization of a group / ** 群的阿贝尔化 *)

(*
 The quotient setoid, NAMED so that the [PropEquiv] hypothesis below can
 mention it: a field of a [Program] record literal cannot refer to a setoid
 that is still an evar while the literal is being elaborated. 

 --------
 商集合等价类，命名为以便下面的[PropEquiv]假设可以提及它：[Program]记录字面值的字段在字面值被展开时不能引用仍然是evar的集合等价类。
*)
Program Definition abel_setoid (G : GrpObject) : Setoid (carrier G) := {|
  equiv := abel_eq G
|}.
Next Obligation.
  intro G; equivalence.
  - apply abel_eq_refl.
  - now apply abel_eq_sym.
  - now apply (abel_eq_trans G x y).
Qed.

(*
 [abel_eq] IS a [Prop] relation, so the quotient supplies its own
 [cmon_prop] and no hypothesis is taken anywhere. 

 --------
 [abel_eq] 是一个 [Prop] 关系，因此商自身提供了它的 [cmon_prop]，并且在任何地方都没有采用假设。
*)
Definition abel_PropEquiv (G : GrpObject) : PropEquiv (abel_setoid G) :=
  @PropEquiv_of_relation _ (abel_setoid G) (abel_eq G)
    (fun _ _ h => h) (fun _ _ h => h).

Program Definition AbelianizationOb (G : GrpObject) :
  AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := carrier G
                    ; is_setoid := abel_setoid G |};
    cmon_zero := grp_unit G;
    cmon_plus := grp_mul G;
    cmon_prop := abel_PropEquiv G
  |};
  ab_neg := grp_inv G
|}.
Next Obligation.
  intros G a a' Ha b b' Hb; now apply abel_eq_mul.
Qed.
Next Obligation.
  intros G a b c; apply abel_eq_of_eq, grp_mul_assoc.
Qed.
Next Obligation.
  (* Commutativity IS the generating constructor. / 交换律就是生成构造器。 *)
  intros G a b; unfold abel_eq; constructor.
  apply (inc_resp (a := gcomm G a b)); [| apply inc_comm ].
  unfold gcomm.
  rewrite (grp_inv_mul G b a).
  rewrite (grp_mul_assoc G (grp_mul G a b) (grp_inv G a) (grp_inv G b)).
  reflexivity.
Qed.
Next Obligation.
  intros G a; apply abel_eq_of_eq, grp_mul_unit_l.
Qed.
Next Obligation.
  intros G a a' Ha; now apply abel_eq_inv.
Qed.
Next Obligation.
  intros G a; apply abel_eq_of_eq, grp_mul_inv_l.
Qed.

(* * ** The commutator subgroup, as a functor Grp ⟶ Grp / * ** 交换子子群，作为函子 Grp ⟶ Grp *)

Definition commutator_carrier (G : GrpObject) : Type :=
  { x : carrier G & InCommutator G x }.

Definition mk_comm (G : GrpObject) (x : carrier G)
  (Hx : InCommutator G x) : commutator_carrier G :=
  existT (fun x : carrier G => InCommutator G x) x Hx.

(*
 The carrier setoid is named rather than written inline in the record
 below: since the PR “algebraic carriers are sets” (2026-09-17) the record
 also carries [grp_prop], and a [Program] record literal cannot carry a
 [PropEquiv] field naming a setoid written inline in the same literal. 

 --------
 载体集合子在下面的记录中是命名的，而不是内联书写的：自从 PR “代数载体是集合”（2026-09-17）以来，该记录也携带了 [grp_prop]，并且一个 [Program] 记录字面量不能携带一个 [PropEquiv] 字段来命名在同一字面量中内联书写的集合子。
*)
Program Definition commutator_setoid (G : GrpObject) : SetoidObject := {|
  carrier := commutator_carrier G;
  is_setoid := {| equiv := fun a b => `1 a ≈ `1 b |}
|}.
Next Obligation. intro G; equivalence; now transitivity (`1 y). Qed.

Program Definition CommutatorGrp (G : GrpObject) : GrpObject := {|
  grp_setoid := commutator_setoid G;
  grp_unit := mk_comm G (grp_unit G) inc_unit;
  grp_mul := fun a b =>
    mk_comm G (grp_mul G (`1 a) (`1 b)) (inc_mul (`2 a) (`2 b));
  grp_inv := fun a => mk_comm G (grp_inv G (`1 a)) (inc_inv (`2 a));
  (* The commutator subgroup's `≈` compares first projections in [G]. / 交换子子群的 `≈` 在 [G] 中比较第一投影。 *)
  grp_prop :=
    sigma_first_PropEquiv (is_setoid (commutator_setoid G))
      (fun _ _ h => h) (fun _ _ h => h) (grp_prop G)
|}.
Next Obligation.
  intros G a a' Ha b b' Hb; simpl in *; now rewrite Ha, Hb.
Qed.
Next Obligation. intros G a b c; simpl; apply grp_mul_assoc. Qed.
Next Obligation. intros G a; simpl; apply grp_mul_unit_l. Qed.
Next Obligation. intros G a; simpl; apply grp_mul_inv_l. Qed.

Program Definition Commutator_Functor : Grp ⟶ Grp := {|
  fobj := CommutatorGrp;
  fmap := fun G H (f : GrpHom G H) =>
    {| grp_map := {| morphism := fun a =>
         mk_comm H (grp_map f (`1 a)) (hom_commutator f (`1 a) (`2 a)) |}
    |}
|}.
Next Obligation.
  intros G H f a b Hab; simpl in *.
  exact (proper_morphism (grp_map f) _ _ Hab).
Qed.
Next Obligation. intros G H f; simpl; apply (grp_map_unit f). Qed.
Next Obligation. intros G H f a b; simpl; apply (grp_map_mul f). Qed.
Next Obligation.
  intros G H f g Hfg a; simpl.
  exact (Hfg (`1 a)).
Qed.
Next Obligation. intros G a; simpl; reflexivity. Qed.
Next Obligation. intros G H K f g a; simpl; reflexivity. Qed.

(** ** The inclusion Ab ⟶ Grp / ** 包含 Ab ⟶ Grp *)

Program Definition Ab_to_GrpOb (A : AbObject) : GrpObject := {|
  grp_setoid := cmon_setoid A;
  grp_unit := cmon_zero A;
  grp_mul := cmon_plus A;
  grp_inv := ab_neg A;
  (* Inherited: the same carrier setoid, so the same witness. / 继承：相同的载体集合，所以相同的证人。 *)
  grp_prop := cmon_prop A
|}.
Next Obligation. intros A a b c; apply cmon_plus_assoc. Qed.
Next Obligation. intros A a; apply cmon_plus_zero_l. Qed.
Next Obligation. intros A a; apply ab_neg_left. Qed.

Program Definition Ab_to_Grp : Ab ⟶ Grp := {|
  fobj := Ab_to_GrpOb;
  fmap := fun A B (f : AbHom A B) =>
    {| grp_map := cmon_map f
     ; grp_map_unit := cmon_map_zero f
     ; grp_map_mul := cmon_map_plus f |}
|}.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g a; simpl; reflexivity. Qed.

(** ** The abelianization functor / ** 阿贝尔化函子 *)

Program Definition Abelianization_Functor : Grp ⟶ Ab := {|
  fobj := AbelianizationOb;
  fmap := fun G H (f : GrpHom G H) =>
    {| cmon_map := {| morphism := fun a : carrier G => grp_map f a |}
     |}
|}.
Next Obligation.
  (* respect for the coarser relations: push the witness forward / 对粗俗关系的尊重：推动证人向前 *)
  intros G H f a b Hab; simpl in *.
  unfold abel_eq in *.
  destruct Hab as [Hab]; constructor.
  apply (inc_resp (a := grp_map f (grp_mul G a (grp_inv G b)))).
  - rewrite (grp_map_mul f a (grp_inv G b)).
    rewrite (grp_map_inv f b).
    reflexivity.
  - exact (hom_commutator f _ Hab).
Qed.
Next Obligation.
  intros G H f; simpl.
  apply abel_eq_of_eq, (grp_map_unit f).
Qed.
Next Obligation.
  intros G H f a b; simpl.
  apply abel_eq_of_eq, (grp_map_mul f).
Qed.
Next Obligation.
  intros G H f g Hfg a; simpl.
  apply abel_eq_of_eq; exact (Hfg a).
Qed.
Next Obligation. intros G a; simpl; apply abel_eq_refl. Qed.
Next Obligation. intros G H K f g a; simpl; apply abel_eq_refl. Qed.

(** ** The natural projection / ** 自然投影 *)

(*
 The component at G: the identity function, read from the fine
 setoid into the coarse one. 

 --------
 位于 G 的组件：从精细集合到粗糙集合读取的恒等函数。
*)
Program Definition abel_proj (G : GrpObject) :
  G ~{Grp}~> Ab_to_GrpOb (AbelianizationOb G) := {|
  grp_map := {| morphism := fun a : carrier G => a |}
|}.
Next Obligation. intros G a b Hab; apply abel_eq_of_eq, Hab. Qed.
Next Obligation. intros G; simpl; apply abel_eq_refl. Qed.
Next Obligation. intros G a b; simpl; apply abel_eq_refl. Qed.

(*
 Mac Lane's naturality square p_H ∘ f ≈ f' ∘ p_G, with both legs the
 identity on elements: reflexivity of the coarser relation. 

 --------
 Mac Lane 的自然性方阵 p_H ∘ f ≈ f' ∘ p_G，两个边都是元素上的恒等：较粗关系的自反性。
*)
Program Definition abel_projection :
  @Id Grp ⟹ Ab_to_Grp ◯ Abelianization_Functor := {|
  transform := abel_proj
|}.
Next Obligation.
  intros G H f a; simpl; apply abel_eq_refl.
Qed.
Next Obligation.
  intros G H f a; simpl; apply abel_eq_refl.
Qed.

(** ** Non-degeneracy witnesses / ** 非退化见证 *)

(* In an abelian group the commutator subgroup misses the nonidentity: [InCommutator] does not collapse to the total predicate. / 在阿贝尔群中，换元子群会遗漏非单位元：[InCommutator] 不会简化为全称谓词。 *)
Lemma commutator_GrpTwo_proper :
  InCommutator GrpTwo grp_two_one → False.
Proof.
  intro K.
  pose proof (hom_to_abelian_kills GrpTwo_abelian
                (@grp_hom_id GrpTwo) grp_two_one K) as E.
  exact E.
Qed.

(*
 In S₃ the subgroup is nontrivial: the commutator of the two
 generators is a member and is not the identity. 

 --------
 在 S₃ 中，该子群是非平凡的：两个生成元的换位子是其中的一个元素，并且不是恒等元。
*)
Lemma commutator_S3_nontrivial :
  InCommutator S3 (gcomm S3 S3_r S3_s) *
  (gcomm S3 S3_r S3_s ≈ s3_unit → False).
Proof.
  split.
  - apply inc_comm.
  - intro E; vm_compute in E; discriminate E.
Qed.

(* The abelianization of the nonabelian S₃ does not collapse: the reflection stays apart from the unit in the quotient, because the sign character kills commutators but not the reflection. / 非交换群 S₃ 的交换化不会塌缩：在商群中，反射仍然独立于单位元，因为符号特征会消去交换子，但不会消去反射。 *)
Lemma abelianization_S3_nontrivial :
  abel_eq S3 S3_s s3_unit → False.
Proof.
  intros [K].
  pose proof (hom_to_abelian_kills GrpTwo_abelian s3_sign _ K) as E.
  vm_compute in E.
  exact E.
Qed.
