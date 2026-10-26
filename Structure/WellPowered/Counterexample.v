Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Lattice.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.WellPowered.
Require Import Coq.Logic.Hurkens.

Generalizable All Variables.

(* * * A category that is not well-powered / * * 一个能力不足的类别 *)

(*
 nLab:      https://ncatlab.org/nlab/show/well-powered+category
 nLab:      https://ncatlab.org/nlab/show/Burali-Forti%27s+paradox
 Wikipedia: https://en.wikipedia.org/wiki/System_U#Girard's_paradox

 Mac Lane, “Categories for the Working Mathematician”, 2nd ed., §V.8,
 book p. 130, calls a category well-powered when the subobjects of each
 object form a small set; nLab's page states the same (“every object has
 a small poset of subobjects”) and records that the property can be
 absent even from a locally small category with a strong generator.
 Structure/WellPowered.v states the notion with the index universe
 pinned at or below the hom universe, and its witnesses are all
 POSITIVE.  This file supplies the matching negative: a formal category,
 built with no axiom, that is provably NOT well-powered at the pin, so
 that the pin is seen to exclude something.

 ** The category

 [AntichainTop@{i o h}], the antichain with a top, has as objects
 [option Type@{i}]: a top object [None] and one object [Some A] for
 every type [A] of [Type@{i}], so its objects sit at [o] with [i < o].
 Its arrows are [Some A ~> Some B := A = B], [Some A ~> None := unit],
 [None ~> None := unit] and [None ~> Some B := False], every hom-set
 carrying the setoid in which all arrows are equal.  It is thin, so
 every arrow is monic, and each type [A] gives a subobject [at_sub A] of
 [None] by the arrow into the top.  Two such subobjects are isomorphic
 only when their types are equal, so the subobjects of [None] are at
 least as many as the types of [Type@{i}].

 ** The refutation

 Given a well-poweredness datum [W] at [None] whose index sits at or
 below [i], [fun X => wp_from W (at_sub X)] and [at_up W], which reads
 the object [Some B] off the domain of [wp_to W j], make [Type@{i}] a
 RETRACT of the index: [at_up_down] is read off the domain isomorphism
 that the exhaustiveness clause [wp_to_from] supplies.  A universe that
 is a retract of one of its own types is inconsistent by Hurkens'
 paradox.  The standard library proves this in
 [Coq.Logic.Hurkens.TypeNeqSmallType] for an EQUATION between a universe
 and a type, and says in its comment that only the retract is used;
 [retract_paradox] below restates it over the retract, with the same
 proof through the universe-polymorphic [Generic.paradox].  The result,
 [AntichainTop_not_WellPoweredAt], refutes the datum at every index
 universe [w <= i], and [AntichainTop_not_WellPowered] reads that at the
 pin: with the homs at [h <= i], [WellPowered AntichainTop] is refuted
 outright.  Every hom type is [A = B], which lies in [Prop], or [unit]
 or [False], so [h] may be taken as low as [Set]
 ([AntichainTop_Set_not_WellPowered]).  Read at [AntichainTop^op] the
 same theorem says that [AntichainTop^op] is not co-well-powered
 ([AntichainTop_op_not_CoWellPowered]), since [(AntichainTop^op)^op]
 converts to [AntichainTop].

 ** Positive controls, and what the refutation measures

 The refutation is about SIZE, and size relative to the hom universe
 the category is instantiated at.  Two controls inhabit the same
 per-object record at [None]:

 - [AntichainTop_trivial], one universe up at the object universe
 [o], with the trivial index [SubObj None] of Structure/
 WellPowered.v's [wp_trivial]; the pinned [WellPowered] excludes it
 because [o] exceeds the hom universe;
 - [AntichainTop_WellPoweredAt_up], AT the pin, once the homs are
 instantiated above the types the objects name ([i < h]): the index
 is [option Type@{i}] itself, [wp_to] ([at_name]) sends [None] to
 Theory/Subobject/Lattice.v's [sub_top] and [Some A] to [at_sub A],
 [wp_from] is [sub_dom], and exhaustiveness holds by thinness.

 So the verdict depends on the hom instantiation: [AntichainTop@{i o h}]
 is not well-powered at the pin when [h <= i], and its top object has a
 pinned datum when [i < h] (measured by the two constants).  That is the
 general shape of the pin, recorded in Structure/WellPowered.v's
 UNIVERSE paragraph: “small” means at or below the category's OWN hom
 universe, and a category whose hom universe is a free parameter, as a
 thin one's is, can be instantiated with its homs raised.  Where the hom
 universe is tied to the objects' carriers, as in [Sets] and the
 algebraic categories, it cannot be raised that way.

 ** Universes, measured

 Read with [Set Printing Universes] and [About], stdlib bounds omitted:

 AntichainTop@{i o h} : Category@{o h h}              ( * i < o * )
 AntichainTop_not_WellPoweredAt@{i o h w s t} :
 WellPoweredAt@{w o s h t} None → False
 ( * i < o, h < t, o <= s, h <= s, w <= i * )
 AntichainTop_not_WellPowered@{i o h w s t} :
 WellPowered@{o h w s t} AntichainTop@{i o h} → False
 ( * i < o, h < t, o <= s, h <= s, w <= h, h <= i * )
 AntichainTop_op_not_CoWellPowered@{i o h w s t} :
 CoWellPowered@{o h w s t} (AntichainTop@{i o h}^op) → False
 ( * the block of AntichainTop_not_WellPowered * )
 AntichainTop_trivial@{i o h t} : WellPoweredAt@{o o o h t} None
 ( * i < o, h < t, h <= o * )
 AntichainTop_WellPoweredAt_up@{i o h s t} :
 WellPoweredAt@{h o s h t} None
 ( * i < o, i < h, h < t, o <= s, h <= s * )

 ** Axioms

 None.  [Print Assumptions] reports every constant below closed under
 the global context; stdlib's Hurkens development is a theorem, not an
 axiom, and [retract_paradox] reports closed as well.

 ** Not delivered

 No non-well-powered category from the tree's concrete instances:
 [Sets] and [Grp] are well-powered one universe up (Instance/Sets/
 WellPowered.v, Instance/Grp/WellPowered.v; this parenthesis said “the
 other algebraic categories were not measured”, which is corrected here:
 since #454 Instance/Mod/WellPowered.v shows [RMod R] well-powered and
 co-well-powered one universe up, and both at the pin under
 [Untruncate], the remaining algebraic categories being still
 unmeasured), and whether any of them is well-powered at the pin
 without a hypothesis is left open here.  The
 co-well-powered counterexample is only the dual one,
 [AntichainTop_op_not_CoWellPowered] at [AntichainTop^op], which is
 [AntichainTop_not_WellPowered] itself because [(AntichainTop^op)^op]
 converts to [AntichainTop]; no category that is well-powered but not
 co-well-powered is exhibited.  [AntichainTop] at [i < h] is not shown
 well-powered at objects other than [None]. 

 --------
 nLab:       https://ncatlab.org/nlab/show/well-powered+category 
 nLab:       https://ncatlab.org/nlab/show/Burali-Forti%27s+paradox 
 Wikipedia:  https://en.wikipedia.org/wiki/System_U#Girard's_paradox 

 Mac Lane，《从业数学家的范畴论》，第2版，第§V.8节，书本第130页，将一个范畴称为良幂的，当且仅当每个对象的子对象形成一个小集合；nLab页面也说明了同样的内容（“每个对象都有一个小的子对象偏序集”），并记录了即使在具有强生成元的局部小范畴中，这一性质也可能不存在。Structure/WellPowered.v 将该概念与指标宇宙固定在同态宇宙或其以下，并且它的证据都是积极的。该文件提供了匹配的消极例子：一个形式范畴，在没有任何公理的情况下构建，能够证明在该固定点处不是良幂的，从而可以看到固定点会排除某些东西。

 ** 该范畴[AntichainTop@{i o h}]，带有顶点的反链，其对象为 [option Type@{i}]：一个顶对象 [None] 和每个类型 [A] 的一个对象 [Some A]，因此它的对象位于 [o] 与 [i < o]。 它的箭头是 [Some A ~> Some B := A = B]、[Some A ~> None := unit]、[None ~> None := unit] 和 [None ~> Some B := False]，每个 Hom 集都承载所有箭头相等的等价集合。 它是薄的，因此每个箭头都是单射，每个类型 [A] 通过箭头进入顶对象给出 [None] 的子对象 [at_sub A]。 两个这样的子对象仅在它们的类型相同时才同构，因此 [None] 的子对象至少与 [Type@{i}] 的类型一样多。 

 ** 驳斥给定一个在 [None] 上的充足数据 [W]，其索引位于或低于 [i]、[fun X => wp_from W (at_sub X)] 和 [at_up W]，该数据从 [wp_to W j] 的域中读取对象 [Some B]，使 [Type@{i}] 成为索引的一个收缩：[at_up_down] 是从 [wp_to_from] 提供的穷尽性条款中的域同构中读取的。一个宇宙如果是其自身某种类型的收缩，则根据 Hurkens' 悖论是不一致的。标准库在 [Coq.Logic.Hurkens.TypeNeqSmallType] 中证明了这一点，用于宇宙与某个类型之间的等式，并在注释中说明仅使用了收缩；下面的 [retract_paradox] 在收缩上重新陈述了它，通过宇宙多态 [Generic.paradox] 使用相同的证明。结果，
 [AntichainTop_not_WellPoweredAt]，在每个索引处都反驳了数据
 宇宙 [w <= i]，并且 [AntichainTop_not_WellPowered] 显示在引脚处：在 [h <= i] 的同态下，[WellPowered AntichainTop] 被直接反驳。每种同态类型都是 [A = B]，它位于 [Prop]，或 [unit] 或 [False]，所以 [h] 可以降到 [Set]（[AntichainTop_Set_not_WellPowered]）。在 [AntichainTop^op] 读取时，同一个定理指出 [AntichainTop^op] 不是共良有势的（[AntichainTop_op_not_CoWellPowered]），因为 [(AntichainTop^op)^op] 转化为 [AntichainTop]。

 **阳性对照，以及反驳测量的内容

 反驳涉及大小，以及相对于该类别实例化的同态宇宙的大小。在 [None] 两个对照占据相同的每对象记录：-  [AntichainTop_trivial]，在对象宇宙的上一个宇宙  
 [o]，具有 Structure/WellPowered.v 的平凡索引 [SubObj None] ; 固定的 [WellPowered] 排除了它，因为 [o] 超过了同态宇宙；  
 -  [AntichainTop_WellPoweredAt_up]，在固定点处，一旦同态在类型之上实例化对象的名称（[i < h]）：索引就是 [option Type@{i}] 本身，[wp_to]（[at_name]）将 [None] 发送到 Theory/Subobject/Lattice.v 的 [sub_top] ，并将 [Some A] 发送到 [at_sub A] ，[wp_from] 是 [sub_dom]，并且通过薄性保证了穷尽性。因此，判决取决于同态实例化：[AntichainTop@{i o h}] 在 [h <= i] 时在销上不是强大的，并且其顶对象在 [i < h] 时具有一个固定的数据（由两个常数测量）。这就是销的一般形状，记录在 Structure/WellPowered.v 的 UNIVERSE 段落中：“小”意味着在该类别自身的同态宇宙之下或等于它，而同态宇宙是自由参数的类别，如薄类别，可以用提升其同态的方式实例化。当同态宇宙与对象的承载体绑定时，如在 [Sets] 和代数类别中，就不能以这种方式提升。  

 ** 宇宙，测量

 与 [Set Printing Universes] 和 [About] 一起阅读，省略 stdlib 上限：AntichainTop@{i o h} : Category@{o h h}              ( * i < o * )
 AntichainTop_not_WellPoweredAt@{i o h w s t} :
 WellPoweredAt@{w o s h t} None → False
 ( * i < o, h < t, o <= s, h <= s, w <= i * )
 AntichainTop_not_WellPowered@{i o h w s t} :
 WellPowered@{o h w s t} AntichainTop@{i o h} → False
 ( * i < o, h < t, o <= s, h <= s, w <= h, h <= i * )
 AntichainTop_op_not_CoWellPowered@{i o h w s t} :
 CoWellPowered@{o h w s t} (AntichainTop@{i o h}^op) → False
 ( * AntichainTop_not_WellPowered 的模块 * )
 AntichainTop_trivial@{i o h t} : WellPoweredAt@{o o o h t} None
 ( * i < o, h < t, h <= o * )
 AntichainTop_WellPoweredAt_up@{i o h s t} :
 WellPoweredAt@{h o s h t} None
 ( * i < o, i < h, h < t, o <= s, h <= s * )

 ** 公理无。[Print Assumptions] 报告在全局上下文中每个常数都已闭合；stdlib 的 Hurkens 开发是一个定理，而不是公理，并且 [retract_paradox] 也报告已闭合。

 ** 未交付没有来自树的具体实例的非良幂范畴：
 [Sets] 和 [Grp] 在高一层宇宙中是良幂的（Instance/Sets/WellPowered.v, Instance/Grp/WellPowered.v；这里的括号说“其他代数范畴未被测量”，这里修正为：因为 #454 Instance/Mod/WellPowered.v 显示 [RMod R] 在高一层宇宙中既是良幂的又是余良幂的，而且两者都在 [Untruncate] 下的针处，其余代数范畴仍未测量），是否其中任何一个在没有假设的情况下在针处是良幂的，在此仍未确定。

 余良幂的反例只有对偶的，[AntichainTop_op_not_CoWellPowered] 在 [AntichainTop^op] 处，这就是 [AntichainTop_not_WellPowered] 本身，因为 [(AntichainTop^op)^op] 转换为 [AntichainTop]；没有展示出任何良幂但非余良幂的范畴。[AntichainTop] 在 [i < h] 上显示不佳，在除了 [None] 之外的对象上表现不足。
*)

(* * ** Hurkens' paradox over a retract / * ** Hurkens 关于收缩的悖论 *)

Lemma retract_paradox@{i +} (A : Type@{i}) (down : Type@{i} → A)
  (up : A → Type@{i}) (up_down : ∀ X : Type@{i}, up (down X) = X) : False.
Proof.
  Generic.paradox p.
  + exact Type@{i}.
  + exact (fun X => X).
  + cbn. exact (fun X F => ∀ x : X, F x).
  + cbn. exact (fun _ _ x => x).
  + cbn. exact (fun _ _ x => x).
  + exact (fun F => ∀ x : A, F (up x)).
  + cbn. exact (fun _ f => fun x : A => f (up x)).
  + cbn. intros * f X.
    specialize (f (down X)).
    rewrite up_down in f.
    exact f.
  + exact A.
  + cbn. exact up.
  + cbn. exact (fun _ F => down (∀ x, up (F x))).
  + cbn. exact (fun _ F => down (∀ x, up (F x))).
  + cbn. exact (down False).
  + rewrite up_down in p.
    exact p.
  + cbn. easy.
  + cbn. intros ? f X.
    destruct (up_down X). cbn.
    reflexivity.
  + cbn. intros ? ? f.
    rewrite up_down.
    exact f.
  + cbn. intros ? ? f.
    rewrite up_down in f.
    exact f.
  + cbn. intros ? ? f.
    rewrite up_down.
    exact f.
  + cbn. intros ? ? f.
    rewrite up_down in f.
    exact f.
Qed.

(** ** The antichain with a top / ** 带有顶部的反链 *)

Section AntichainTop.

Universes i o h.
Constraint i < o.

Definition at_hom (a b : option Type@{i}) : Type@{h} :=
  match a, b with
  | Some A, Some B => A = B
  | Some _, None => Datatypes.unit
  | None, None => Datatypes.unit
  | None, Some _ => False
  end.

Definition at_id (a : option Type@{i}) : at_hom a a :=
  match a with Some A => eq_refl | None => tt end.

Definition at_comp {a b c : option Type@{i}} :
  at_hom b c → at_hom a b → at_hom a c :=
  match a, b, c return at_hom b c → at_hom a b → at_hom a c with
  | Some A, Some B, Some C => fun g f => eq_trans f g
  | Some A, Some B, None => fun _ _ => tt
  | Some A, None, None => fun _ _ => tt
  | Some A, None, Some C => fun g _ => match g with end
  | None, None, None => fun _ _ => tt
  | None, None, Some C => fun g _ => match g with end
  | None, Some B, _ => fun _ f => match f with end
  end.

(* Every two parallel arrows are equal. / 每两条平行箭头相等。 *)
Definition at_setoid (a b : option Type@{i}) : Setoid@{h h} (at_hom a b) :=
  {| equiv := fun _ _ => True ;
     setoid_equiv := {| Equivalence_Reflexive := fun _ => I ;
                        Equivalence_Symmetric := fun _ _ _ => I ;
                        Equivalence_Transitive := fun _ _ _ _ _ => I |} |}.

Definition AntichainTop : Category@{o h h} :=
  {| obj := option Type@{i} ;
     hom := at_hom ;
     homset := at_setoid ;
     id := at_id ;
     compose := @at_comp ;
     compose_respects := fun _ _ _ _ _ _ _ _ _ => I ;
     id_left := fun _ _ _ => I ;
     id_right := fun _ _ _ => I ;
     comp_assoc := fun _ _ _ _ _ _ _ => I ;
     comp_assoc_sym := fun _ _ _ _ _ _ _ => I |}.

(* The subobject of the top named by a type. / 由类型命名的顶部子对象。 *)
Definition at_sub (A : Type@{i}) : @SubObj AntichainTop None :=
  {| sub_dom := (Some A : obj[AntichainTop]) ;
     sub_mono := (tt : @hom AntichainTop (Some A) None) ;
     sub_is_monic := @Build_Monic AntichainTop (Some A) None
                       (tt : @hom AntichainTop (Some A) None)
                       (fun _ _ _ _ => I) |}.

(* Reading a type back off an index: the domain of the subobject it names. / 从索引读取类型回溯：它命名的子对象的域。 *)
Definition at_up (W : @WellPoweredAt AntichainTop None) (j : wp_index W) :
  Type@{i} :=
  match sub_dom (wp_to W j) with Some B => B | None => Datatypes.unit end.

(*
 The retract equation, from the domain isomorphism that exhaustiveness
 supplies: its forward arrow is [B = X] when the domain is [Some B], and
 inhabits [False] when it is [None]. 

 --------
 从穷尽性提供的域同构得到的收缩方程：当域为 [Some B] 时，它的前向箭头是 [B = X]，当域为 [None] 时，它属于 [False]。
*)
Lemma at_up_down (W : @WellPoweredAt AntichainTop None) (X : Type@{i}) :
  at_up W (wp_from W (at_sub X)) = X.
Proof.
  unfold at_up.
  destruct (wp_to_from W (at_sub X)) as [iso _].
  generalize (to iso). simpl.
  destruct (sub_dom (wp_to W (wp_from W (at_sub X)))) as [B|]; simpl.
  - intro e; exact e.
  - intro f; destruct f.
Qed.

End AntichainTop.

(** ** The refutation / ** 反驳 *)

(*
 No well-poweredness datum at the top object with index at or below
 [i]. 

 --------
 在索引等于或低于 [i] 的顶层对象中没有充足效能的数据。
*)
Theorem AntichainTop_not_WellPoweredAt@{i o h w s t |
    i < o, w <= i, h < t, o <= s, h <= s +}
  (W : @WellPoweredAt@{w o s h t} AntichainTop@{i o h} None) : False.
Proof.
  exact (retract_paradox (wp_index W) (fun X => wp_from W (at_sub X))
           (at_up W) (at_up_down W)).
Qed.

(* At the pin: with the homs at or below [i], [AntichainTop] is not well-powered. / 在引脚处：当homs在或低于[i]时，[AntichainTop]的功率不足。 *)
Theorem AntichainTop_not_WellPowered@{i o h w s t |
    i < o, h <= i, w <= h, h < t, o <= s, h <= s +}
  (WP : WellPowered@{o h w s t} AntichainTop@{i o h}) : False.
Proof. exact (AntichainTop_not_WellPoweredAt@{i o h w s t} (WP None)). Qed.

(*
 Every hom type lies in [Prop] or [Set], so the homs may sit at
 [Set]. 

 --------
 每个 hom 类型都位于 [Prop] 或 [Set] 中，因此 hom 可以位于
 [Set]。
*)
Theorem AntichainTop_Set_not_WellPowered@{i o s t | i < o, Set < t, o <= s +}
  (WP : WellPowered@{o Set Set s t} AntichainTop@{i o Set}) : False.
Proof. exact (AntichainTop_not_WellPowered@{i o Set Set s t} WP). Qed.

(*
 The dual: [AntichainTop^op] is not co-well-powered, since
 [(AntichainTop^op)^op] is [AntichainTop] by conversion. 

 --------
 对偶体：[AntichainTop^op] 不是共完备的，因为 [(AntichainTop^op)^op] 通过转换是 [AntichainTop]。
*)
Theorem AntichainTop_op_not_CoWellPowered@{i o h w s t |
    i < o, h <= i, w <= h, h < t, o <= s, h <= s +}
  (CWP : CoWellPowered@{o h w s t} (AntichainTop@{i o h}^op)) : False.
Proof. exact (AntichainTop_not_WellPowered@{i o h w s t} CWP). Qed.

(*
 Positive control: one universe up, at the objects, the trivial datum
 exists, so the refutation measures size and nothing else. 

 --------
 阳性对照：一个宇宙上，在那些物体上，平凡的数据存在，因此反驳只测量大小，而不测量其他。
*)
Definition AntichainTop_trivial@{i o h t | i < o, h < t, h <= o +} :
  @WellPoweredAt@{o o o h t} AntichainTop@{i o h} None :=
  @wp_trivial@{o h o o t} AntichainTop@{i o h} None.

(*
 Second positive control: with the homs one universe above the types
 the objects name ([i < h]), the top object has a datum AT the pin,
 indexed by the objects themselves.  [at_name] names each object's
 subobject of [None]: the top one for [None], [at_sub A] for [Some A]. 

 --------
 第二个阳性对照：对于比类型高一级的同源体  
 对象的名称（[i < h]），顶层对象在引脚处有一个数据点，  
 由对象本身索引。[at_name] 命名每个对象的 [None] 子对象：[None] 的顶层，[Some A] 的 [at_sub A]。
*)
Definition at_name@{i o h | i < o +} (a : option Type@{i}) :
  @SubObj AntichainTop@{i o h} None :=
  match a with
  | Some A => at_sub A
  | None => @sub_top AntichainTop@{i o h} None
  end.

Definition AntichainTop_WellPoweredAt_up@{i o h s t |
    i < o, i < h, h < t, o <= s, h <= s +} :
  @WellPoweredAt@{h o s h t} AntichainTop@{i o h} None.
Proof.
  unshelve refine {| wp_index := option Type@{i};
                     wp_to := at_name;
                     wp_from := fun u => sub_dom u |}.
  intros [d m Hm]; simpl.
  unshelve eexists.
  - destruct d as [A|]; simpl.
    + refine {| to := (eq_refl : @hom AntichainTop@{i o h} (Some A) (Some A));
                from := eq_refl; iso_to_from := I; iso_from_to := I |}.
    + refine {| to := (tt : @hom AntichainTop@{i o h} None None);
                from := tt; iso_to_from := I; iso_from_to := I |}.
  - exact I.
Defined.
