Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

Generalizable All Variables.

Section Subcategory.

Context (C : Category).

(** A subcategory D of a category C. / 类别 C 的子类别 D。 *)

(*
 nLab: https://ncatlab.org/nlab/show/subcategory
 Wikipedia: https://en.wikipedia.org/wiki/Subcategory

 A subcategory D of C is given by a subcollection [sobj] of the objects of C
 together with, for each pair of selected objects, a subcollection [shom] of
 the C-morphisms between them, closed under identity ([sid]) and composition
 ([scomp]). The source/target closure condition (if f : x ~> y is in D then
 so are x and y) holds here by construction: [shom] is only indexed by
 objects ox, oy already selected from [sobj].

 These conditions make D a category in its own right ([Sub] below) for which
 the inclusion D ⟶ C ([Incl]) is a functor; that inclusion is always
 faithful, since on each hom-set it is the first projection out of a sigma
 type — proved as [Incl_Faithful] below. A subcategory is full when [shom]
 retains every C-morphism between selected objects ([Full]), and wide (lluf)
 when [sobj] selects every object of C ([Wide]).  In a full subcategory an
 ambient isomorphism lifts ([Full_sub_iso]) and, in particular, two
 membership proofs for one object give isomorphic objects of [Sub]
 ([Full_membership_iso]) -- which is why a skeleton's uniqueness clause is
 stated at the level of [Sub]'s objects rather than their carriers
 (Theory/Skeleton.v). 

 --------
 nLab:  https://ncatlab.org/nlab/show/subcategory 
 维基百科:  https://en.wikipedia.org/wiki/Subcategory 

 一个C的子范畴D由C的对象的子集合[sobj]给出，同时对于每一对选定的对象，给出C-态射之间的子集合[shom]，并且该集合在恒等态射([sid])和复合([scomp])下封闭。源/目标封闭条件（如果f : x ~> y在D中，则x和y也在D中）在这里通过构造而成立：[shom]仅由已经从[sobj]选定的对象ox, oy索引。这些条件使 D 本身成为一个类别（见下文 [Sub]），对于它的包含 D ⟶ C（见下文 [Incl]）是一个函子；这个包含总是忠实的，因为在每个同态集合上它是一个 σ 型的第一个投影——如下文 [Incl_Faithful] 所证明。一个子类别是全子类别，当 [shom] 保留所选对象之间的每个 C-态射（见下文 [Full]），并且是宽子类别（lluf），当 [sobj] 选择 C 的每一个对象（见下文 [Wide]）。在一个全子类别中，一个环境同构可以提升（见下文 [Full_sub_iso]），特别地，对于一个对象的两个成员证明会得到 [Sub] 中同构的对象（见下文 [Full_membership_iso]）——这就是为什么骨架的唯一性条款是在 [Sub] 对象的层面上陈述，而不是它们的承载对象上（Theory/Skeleton.v）。
*)

(*
   【Record Subcategory 语法与字段展开】/ Subcategory walkthrough
   （口吻对齐 Theory/Category.v；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      子范畴 = 选出一些对象 + 它们之间的一些态射，且对 id 与复合封闭。
      Selected objects + selected morphisms, closed under id and compose.
      Haskell 对照：像「带约束的 newtype + 只暴露部分操作」，但是要交封闭证明。
      Like a restricted API, with closure proofs.

   2) Record 字段 / Record fields
      - sobj : C → Type          — 「x 被选中」的证据类型
      - shom … : (x ~> y) → Type — 「f 被选中」的证据
      - scomp / sid              — 复合与恒等的封闭性（证明义务）

   3) 组装出的范畴 / Built category
      Sub：对象 { x & sobj x }，态射 { f & shom … f }；
      Incl : Sub ⟶ C 总是忠实（Faithful）—— ≈ 定义成底层 ≈。
      Incl is always faithful by encoding.

   4) 修饰词 / Adjectives
      Full：选中对象之间保留全部态射；Wide：选中全部对象。
      Full = all homs between selected objs; Wide = all objects.

   阅读：sobj → shom → sid/scomp → Sub → Incl。
   Read: sobj → shom → closure → Sub → Incl.
*)

Record Subcategory := {
  sobj : C → Type;                  (* sub-collection of the objects of C / C 的对象的子集合 *)

  (* sub-collection of the C-morphisms between selected objects / 所选对象之间 C-态射的子集合 *)
  shom {x y : C} : sobj x → sobj y → (x ~> y) → Type;

  (*
 closed under composition: if f : y ~> z and g : x ~> y are in D, then so
 is the composite f ∘ g : x ~> z 

 --------
 在复合下封闭：如果 f : y ~> z 和 g : x ~> y 属于 D，那么复合 f ∘ g : x ~> z 也属于 D
*)
  scomp {x y z : C} (ox : sobj x) (oy : sobj y) (oz : sobj z)
        {f : y ~> z} {g : x ~> y} :
    shom oy oz f → shom ox oy g → shom ox oz (f ∘ g);

  (*
 closed under identity: if x is in D then so is the identity 1ₓ 

 --------
 在恒等映射下封闭：如果 x 在 D 中，那么恒等元 1ₓ 也在 D 中
*)
  sid {x : C} (ox : sobj x) : shom ox ox (@id C x)
}.

Variable S : Subcategory.

(*
 These conditions ensure that D is a category in its own right... 

 --------
 这些条件确保 D 本身就是一个范畴...
*)
Program Definition Sub : Category := {|
  obj     := { x : C & sobj S x };
  hom     := fun x y => { f : `1 x ~> `1 y & shom S `2 x `2 y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun x => (id; sid S `2 x);
  compose := fun x y z f g  => (`1 f ∘ `1 g; scomp S `2 x `2 y `2 z `2 f `2 g)
|}.

(* ... and the inclusion D ⟶ C is a functor. / ... 并且包含映射 D ⟶ C 是一个函子。 *)
Program Instance Incl : Sub ⟶ C := {
  fobj := fun x => `1 x;
  fmap := fun x y f => `1 f
}.

(*
 The inclusion is faithful, for every [S] whatsoever.

 Book: Riehl, "Category Theory in Context", Dover 2016, §1.5, Remark 1.5.8,
 printed p. 33

 This lemma is as shallow as it looks, and it is worth saying so plainly
 rather than dressing it up: [Sub]'s hom-setoid is DEFINITIONALLY `≈` of
 first projections (`equiv := fun f g => `1 f ≈ `1 g` in [Sub] above), and
 [Incl]'s action on morphisms is that same first projection, so the
 hypothesis and the conclusion are literally the same statement and the
 proof is [exact]. Nothing about [S] is used — neither closure field, nor
 even that [shom] is inhabited. What the lemma buys is that the argument is
 now made once, generically, instead of per subcategory: it is exactly the
 proof re-derived for one particular subcategory at
 Theory/Sheaf/Category.v.

 The substance of a faithfulness claim sits in the hom-setoid being injected
 out of, not in the injection; see Construction/Subcategory/Finite.v for an
 instance of [Sub] carrying two parallel morphisms shown distinct. 

 --------
 包含是忠实的，对于任意的 [S] 都成立。

 书籍：Riehl，《情境中的范畴论》，多佛出版社 2016，第1.5节，备注1.5.8，印刷页33这个引理表面看起来很浅显，值得直接这么说，而不必加以包装：[Sub] 的同态集在定义上就是 `≈` 的第一投影（`equiv := fun f g => ` 1 f ≈ `1 g` 在上面的 [Sub] 中），而 [Incl] 对态射的作用也是同样的第一投影，因此假设和结论实际上是相同的陈述，而证明是 [exact]。[S] 的任何内容都没有被使用——既没有闭包域，也没有使用 [shom] 的存在性。这个引理的价值在于现在这个论证可以一次性、通用地完成，而不是针对每个子范畴分别进行：它正是为某一个特定子范畴在 Theory/Sheaf/Category.v 中重新推导的证明。忠实性主张的实质在于被注入的同构集合，而不在注射中；参见 Construction/Subcategory/Finite.v，了解一个 [Sub] 的例子，它携带两个被展示为不同的平行态射。
*)

Lemma Incl_Faithful : Functor.Faithful Incl.
Proof.
  constructor; simpl; intros x y f g Hfg; exact Hfg.
Qed.

(*
 Additionally, we say that D is...

 A full subcategory if for any x and y in D, every morphism f : x → y in C
 is also in D... 

 --------
 此外，我们说 D 是…

 一个满子范畴，如果对于 D 中的任意 x 和 y，C 中的每一个态射 f : x → y
 也在 D 中…
*)

Definition Full : Type :=
  ∀ (x y : C) (ox : sobj S x) (oy : sobj S y) (f : x ~> y), shom S ox oy f.

(* ... (that is, the inclusion functor D ⟶ C is full) / ...（也就是说，包含函子 D ⟶ C 是满的） *)

Lemma Full_Implies_Full_Functor : Full → Functor.Full Incl.
Proof.
  unfold Full; intros.
  construct.
  - exists g.
    destruct x, y.
    apply X; auto.
  - reflexivity.
Qed.

(*
 In a full subcategory every ambient isomorphism between selected objects
 lifts, because both legs are retained by [Full] and the two laws are
 compared by [Sub]'s hom-setoid, i.e. on carriers. 

 --------
 在一个满子范畴中，所选对象之间的每个环境同构都会被提升，因为两条边都被 [Full] 保留，并且两个定律通过 [Sub] 的同态集进行比较，即在载体上。
*)

Program Definition Full_sub_iso (full : Full) {x y : C}
        (ox : sobj S x) (oy : sobj S y) (f : x ≅ y) :
  ((x; ox) : Sub) ≅[Sub] (y; oy) := {|
  to   := (to f; full x y ox oy (to f));
  from := (from f; full y x oy ox (from f))
|}.
Next Obligation. apply iso_to_from. Qed.
Next Obligation. apply iso_from_to. Qed.

(*
 The special case at the identity: two membership proofs for one object
 give isomorphic — never equal — objects of [Sub].  Theory/Skeleton.v
 quotes this when explaining why a skeleton's uniqueness clause is stated
 at the level of [Sub]'s objects rather than their carriers.  Provided
 for reference; it is [Full_sub_iso] at [iso_id]. 

 --------
 身份的特殊情况：同一个对象的两个成员证明给出的是同构的——永远不相等——的 [Sub] 对象。Theory/Skeleton.v 在解释为什么骨架的唯一性条款是在 [Sub] 的对象层面而不是它们的承载体层面说明时引用了这一点。提供参考；它在 [iso_id] 的 [Full_sub_iso]。
*)

Program Definition Full_membership_iso (full : Full) (x : C)
        (p q : sobj S x) : ((x; p) : Sub) ≅[Sub] (x; q) := {|
  to   := (id[x]; full x x p q id);
  from := (id[x]; full x x q p id)
|}.

(*
 ... and back again.

 Reading the previous lemma in reverse runs into the setoid discipline.
 [Functor.Full Incl] returns, for a C-morphism f between selected objects, a
 morphism OF THE SUBCATEGORY, and [fmap_sur] compares it to f in the
 hom-setoid: what comes back is some g with g ≈ f carrying a [shom] witness,
 not a witness for f itself. That up-to-≈ statement is what fullness of the
 inclusion yields on its own, and it is recorded first. 

 --------
 ...然后再回过来。

 以相反顺序阅读前面的引理会遇到集合论规范的问题。
 对于选定对象之间的 C-态射 f，[Functor.Full Incl] 返回一个子范畴的
 态射，而 [fmap_sur] 则在同态集论中将其与 f 进行比较：返回的是某个 g，其满足 g ≈ f，并带有 [shom] 的证据，而不是 f 本身的证据。这个“至 ≈ 的”陈述就是包含函子自身所带来的充满性，并且它首先被记录下来。
*)

Lemma Full_Functor_Implies_Full_upto (HF : Functor.Full Incl) :
  ∀ (x y : C) (ox : sobj S x) (oy : sobj S y) (f : x ~> y),
    { g : x ~> y & (g ≈ f) ∧ shom S ox oy g }.
Proof.
  intros x y ox oy f.
  pose (p := @prefmap _ _ Incl HF (x; ox) (y; oy) f).
  exists (`1 p).
  split.
  - exact (@fmap_sur _ _ Incl HF (x; ox) (y; oy) f).
  - exact (`2 p).
Qed.

(*
 To close the gap and land on [Full] as stated, one needs [shom] to be
 closed under the hom-setoid equivalence. The [Subcategory] record above has
 no such field — its two closure conditions are for composition and
 identities — so the property is named here and taken as a hypothesis rather
 than derived. It holds trivially for the usual case of a full subcategory
 cut out by a predicate on objects alone, where [shom] ignores its morphism
 argument: Theory/Sheaf/Category.v and Construction/Subcategory/Finite.v
 are both of that shape, and the latter discharges it. 

 --------
 为了如上所述缩小差距并达成 [Full]，需要 [shom] 在同态集合等价下是闭合的。上述 [Subcategory] 记录没有这样的字段——它的两个闭合条件是针对组合和恒等元的——因此该属性在此被命名并作为假设而不是推导得出。对于通常的情况，即仅由对象上的谓词切出的完全子范畴，该属性显然成立，其中 [shom] 忽略其态射参数：Theory/Sheaf/Category.v 和 Construction/Subcategory/Finite.v 都是这种形式，后者已经实现了它。
*)

Definition ShomRespects : Type :=
  ∀ (x y : C) (ox : sobj S x) (oy : sobj S y) (f g : x ~> y),
    f ≈ g → shom S ox oy f → shom S ox oy g.

(*
 The converse of [Full_Implies_Full_Functor] under that hypothesis, which
 with it completes the "full subcategory iff full inclusion" biconditional.
 Only the hypothesis's transport along ≈ is used; the two directions are
 otherwise independent.

 The hypothesis is NECESSARY, not merely convenient:
 Construction/Subcategory/FullConverse.v exhibits a subcategory whose
 inclusion is full as a functor while the subcategory is not full as data,
 over a hom-setoid with two classes, refuting the unhypothesised converse
 outright. 

 --------
 在该假设下 [Full_Implies_Full_Functor] 的逆命题，与之共同完成“完全子范畴当且仅当完全包含”这个双条件命题。仅使用了假设沿 ≈ 的传递；两种方向在其他方面是独立的。

 该假设是必要的，而不仅仅是方便的：Construction/Subcategory/FullConverse.v 展示了一个子范畴，其包含作为函子是完全的，但子范畴作为数据却不是完全的，基于具有两个类的同态集合，从而直接驳斥了无假设的逆命题。
*)

Lemma Full_Functor_Implies_Full : ShomRespects → Functor.Full Incl → Full.
Proof.
  intros HR HF x y ox oy f.
  destruct (Full_Functor_Implies_Full_upto HF x y ox oy f) as [g [Hgf Hg]].
  exact (HR _ _ _ _ _ _ Hgf Hg).
Qed.

(*
 A replete subcategory if for any x in D and any isomorphism f : x ≅ y in C,
 both y and f are also in D. 

 --------
 如果对于 D 中的任意 x 以及 C 中的任何同构 f : x ≅ y，y 和 f 也都在 D 中，则该子范畴是充实的。
*)

Definition Replete : Type :=
  ∀ (x : C) (ox : sobj S x) (y : C) (f : x ≅ y),
    { oy : sobj S y & shom S ox oy (to f) ∧ shom S oy ox (from f) }.

(*
 A wide subcategory if every object of C is also an object of D. 

 --------
 如果 C 的每个对象也是 D 的对象，则为一个广义子类别。
*)

Definition Wide : Type := ∀ x : C, sobj S x.

End Subcategory.

#[export] Existing Instance Incl_Faithful.
