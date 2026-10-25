Require Import Category.Lib.

Generalizable All Variables.

(* * * Setoids whose equality is propositional / * * 相等为命题性的 setoid *)

(*
 nLab:    https://ncatlab.org/nlab/show/setoid
 nLab:    https://ncatlab.org/nlab/show/h-set
 nLab:    https://ncatlab.org/nlab/show/mere+proposition
 Book:    The Univalent Foundations Program, "Homotopy Type Theory:
 Univalent Foundations of Mathematics", IAS 2013, Definition 3.1.1
 (a SET is a type whose identity types have at most one inhabitant)
 and Definition 3.3.1 (a MERE PROPOSITION is a type any two of whose
 inhabitants are equal)
 Book:    Bishop, "Foundations of Constructive Analysis", McGraw-Hill 1967,
 chapter one ("A constructivist manifesto")
 Library: UniMath, Foundations/PartA.v ([isaprop]) and Foundations/Sets.v
 ([isaset], [hSet])
 Library: Agda standard library, Relation.Binary.Bundles.Setoid -- the
 bundle agda-categories builds its hom-setoids from
 Book:    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §V.6 (the general adjoint functor theorem) and §V.7, printed
 p. 128 (the solution-set condition, and the tensor product of
 modules obtained from it)

 TWO KINDS OF SETOID.  A setoid is a carrier together with a chosen
 equivalence relation (nLab: setoid), and Bishop's prescription for defining
 a set -- say what must be done to construct an element and what must be done
 to show two elements equal (Bishop 1967, chapter one) -- says nothing about
 whether a proof of an equation carries information.  Type theory therefore
 has two setoids, and the distinction is exactly the one the HoTT book draws:
 in the PROOF-RELEVANT setoid the relation is valued in a universe of types,
 so an equality proof is data; in the PROPOSITIONAL setoid it is valued in
 [Prop], so any two proofs of one equation are interchangeable -- a MERE
 PROPOSITION in the sense of Definition 3.3.1, the condition under which the
 carrier behaves as a SET in the sense of Definition 3.1.1.  UniMath spells
 the two predicates [isaprop] and [isaset] and bundles the second as [hSet].
 The Agda standard library's [Setoid], which agda-categories uses for its
 hom-setoids, parameterises its relation by a universe level and so is
 proof-relevant by default, exactly as this library is.

 WHY THIS LIBRARY'S `≈` IS Type-VALUED, AND STAYS SO.  Lib/Setoid.v
 fixes the choice: [equiv] lives in [crelation], "a [Type]-valued, hence
 proof-relevant, relation ... so that equivalence proofs may carry
 computational content".  That is load-bearing rather than decorative.  Cat's
 hom-setoid is [Functor_Setoid] (Theory/Functor.v, installed as Cat's
 [homset] at Instance/Cat.v), and there an [F ≈ G] IS a family of
 isomorphisms [∀ x : C, F x ≅ G x] paired with its coherence condition: the
 first projection of such a proof is an isomorphism of D, a value in [Type].
 Truncating `≈` library-wide would discard that family, and nothing recovers
 it -- Test/ProbePropEquiv.v's first negative measures the refusal, taking an
 [inhabited (F ≈ G)] and asking for the isomorphism at [x].  Propositional
 equality therefore cannot be a change to [Class Setoid].  It is a PROPERTY
 that particular setoids have, and [PropEquiv] below is that property.

 THE SIZE FACT, IN THREE LINES.  A [Prop]-valued relation on a carrier
 [A : Type@{u}] inhabits [A → A → Prop], whose sort is [Type@{max(Set+1,u)}]
 -- the carrier's own universe, as soon as [u] is above [Set].  A
 [Type]-valued relation inhabits [A → A → Type@{p}], whose sort is
 [Type@{max(u,p+1)}], strictly above the proof universe [p]; and every setoid
 of this library's concrete algebra is used at [Setoid@{u u}], so its relation
 space is [Type@{u+1}], one universe ABOVE the carrier.  Hence a type of
 congruences on a carrier is carrier-sized exactly when the congruences are
 [Prop]-valued.  Test/ProbePropEquiv.v measures all three sorts and pins the
 middle one with a refusal.

 WHY THAT MATTERS HERE.  Mac Lane's general adjoint functor theorem asks for
 a SOLUTION SET (CWM 2nd ed., §V.6), and §V.7, printed p. 128, runs the
 argument for the tensor product of modules.  Adjunction/GAFT.v demands that
 the solution set's index sit at the carrier universe, while the intended
 index for a concrete algebraic category -- the congruences on a term algebra
 -- is a type of relations on that carrier.  By the previous paragraph the
 index fits only when those relations are [Prop]-valued.  That is the entire
 reason this property is worth naming.

 WHAT THE CLASS IS, AND WHAT IT IS NOT.  [PropEquiv S] supplies a
 [Prop]-valued relation [pequiv] together with implications BOTH ways between
 it and `≈`.  It is a logical equivalence, never an identification: `≈` keeps
 its [Type]-valued type and its data, and [pequiv] is a separate relation that
 happens to hold exactly when `≈` does.  What it buys is one elimination,
 [pequiv_elim_inhabited]: an [inhabited (x ≈ y)] can be eliminated into the
 [Prop] goal [pequiv x y], which [pequiv_to] then converts back to [x ≈ y].
 What it does NOT buy: it says nothing about proofs of `≈` being equal to one
 another, gives no uniqueness of identity proofs for the carrier, and is not
 inherited by a carrier under a different `≈` -- it is a property of the
 SETOID, not of the type.

 ONE SYNTACTIC TRAP, RECORDED HERE BECAUSE IT LOOKS LIKE A SHORTCUT.  The
 sort ascription [(x ≈ y : Prop)] is refused even for [eq_Setoid], because
 Coq types [equiv x y] at [Type] whatever the relation underneath happens to
 be; there is no ascription that narrows it after the fact.  The relation must
 be NAMED instead, which is what [PropEquiv_of_relation] below is for.
 Test/ProbePropEquiv.v's second negative pins that refusal.

 COVERAGE.  Lib/Setoid.v defines four setoid constructors -- [unit_setoid],
 [eq_Setoid], [funext_Setoid] and [Fin_Setoid] -- and Lib/Datatypes.v six
 more -- [prod_setoid], [sum_setoid], [option_setoid], [list_setoid],
 [nat_setoid] and [fun_setoid].  Every one of them has an instance below.
 Neither file defines a sigma setoid, so there is none to transport; the
 typed-list setoids of Lib/TList.v and Lib/NETList.v belong to the solver's
 term language and are not covered here.  The [Sets]-level transports --
 hom-setoids, binary and indexed products, limits, and the
 [LocallyPropositional] vocabulary for categories -- are in
 Instance/Sets/Propositional.v.

 AN EARLIER REVISION of this paragraph stopped there.  Since the PR
 "algebraic carriers are sets" (2026-09-17) the file also carries two
 TRANSPORTS -- [dep_fun_PropEquiv] and [sigma_first_PropEquiv] -- for setoids
 the concrete algebra builds INLINE rather than through one of the ten
 constructors above.  They are stated at the end of the file, and the reason
 they take their two implications as arguments rather than naming a canonical
 setoid is recorded there. 

 --------
 nLab:    https://ncatlab.org/nlab/show/setoid
 nLab:    https://ncatlab.org/nlab/show/h-set
 nLab:    https://ncatlab.org/nlab/show/mere+proposition
 Book:    The Univalent Foundations Program, "Homotopy Type Theory:
 Univalent Foundations of Mathematics", IAS 2013, Definition 3.1.1
 （SET 是其恒等类型至多有一个居留者的类型）
 与 Definition 3.3.1（MERE PROPOSITION 是任意两居留者皆相等的类型）
 Book:    Bishop, "Foundations of Constructive Analysis", McGraw-Hill 1967,
 第一章（“构造主义宣言”）
 Library: UniMath, Foundations/PartA.v（[isaprop]）与 Foundations/Sets.v
 （[isaset]、[hSet]）
 Library: Agda 标准库 Relation.Binary.Bundles.Setoid —— agda-categories
 用以构建其 hom-setoid 的捆
 Book:    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
 §V.6（一般伴随函子定理）与 §V.7，印本 p.128
 （解集条件，以及由此得到的模的张量积）

 两类 setoid。setoid 是载体连同选定等价关系（nLab: setoid）；Bishop 对定义集合的处方——说明如何构造元素、如何表明两元素相等（Bishop 1967，第一章）——并不规定相等证明是否携带信息。因此类型论中有两种 setoid，区分恰如 HoTT 书所划：在证明相关 setoid 中关系取值于类型宇宙，相等证明是数据；在命题性 setoid 中关系取值于 [Prop]，同一等式的任意两证明可互换——即 Definition 3.3.1 意义下的单纯命题，在此条件下载体表现为 Definition 3.1.1 意义下的集合。UniMath 把两谓词写作 [isaprop] 与 [isaset]，并把后者捆为 [hSet]。Agda 标准库的 [Setoid]（agda-categories 用于 hom-setoid）用宇宙层级参数化其关系，故默认证明相关，与本库相同。

 为何本库的 `≈` 取值于 Type，并保持如此。Lib/Setoid.v 固定选择：[equiv] 居于 [crelation]，“`Type` 值、故而证明相关的关系……使等价证明可携带计算内容”。这是承重而非装饰。Cat 的 hom-setoid 是 [Functor_Setoid]（Theory/Functor.v，在 Instance/Cat.v 安装为 Cat 的 [homset]），其中 [F ≈ G] 是一族同构 [∀ x : C, F x ≅ G x] 配以其连贯条件：此种证明的第一投影是 D 中的同构，即 [Type] 中的值。若全库截断 `≈` 会丢掉该族且无法恢复——Test/ProbePropEquiv.v 的第一个反例度量此拒绝：取 [inhabited (F ≈ G)] 并索要 [x] 处的同构。因此命题相等不能改成对 [Class Setoid] 的变更；它是特定 setoid 所具有的性质，下文 [PropEquiv] 即该性质。

 三行说清规模事实。[A : Type@{u}] 上的 [Prop] 值关系居于 [A → A → Prop]，其排序为 [Type@{max(Set+1,u)}]——一旦 [u] 高于 [Set] 即载体自身宇宙。[Type] 值关系居于 [A → A → Type@{p}]，排序为 [Type@{max(u,p+1)}]，严格高于证明宇宙 [p]；本库具体代数的每个 setoid 都在 [Setoid@{u u}] 使用，故其关系空间为 [Type@{u+1}]，比载体高一宇宙。因此载体上同余的类型恰在同余为 [Prop] 值时具有载体规模。Test/ProbePropEquiv.v 度量三种排序并用拒绝钉死中间者。

 为何此处重要。Mac Lane 的一般伴随函子定理要求解集（CWM 2nd ed., §V.6），§V.7 印本 p.128 对模的张量积运行该论证。Adjunction/GAFT.v 要求解集指标落在载体宇宙，而具体代数范畴的意图指标——项代数上的同余——是该载体上的关系类型。由上段，仅当这些关系为 [Prop] 值时指标才合适。这是命名此性质的全部理由。

 该类是什么、不是什么。[PropEquiv S] 提供 [Prop] 值关系 [pequiv]，以及它与 `≈` 之间双向蕴涵。这是逻辑等价，绝非等同：`≈` 保持其 [Type] 值类型与数据，[pequiv] 是恰好在 `≈` 成立时成立的另一关系。它买到的是一次消去 [pequiv_elim_inhabited]：[inhabited (x ≈ y)] 可消去到 [Prop] 目标 [pequiv x y]，再经 [pequiv_to] 转回 [x ≈ y]。它不买到的：不声称 `≈` 的证明彼此相等，不给出载体恒等证明的唯一性，也不在不同 `≈` 下被载体继承——它是 setoid 的性质，不是类型的性质。

 一处句法陷阱，因看似捷径而记录于此。即便对 [eq_Setoid]，排序标注 [(x ≈ y : Prop)] 也被拒绝，因为无论底层关系如何，Coq 都把 [equiv x y] 排在 [Type]；没有事后收窄的标注。关系必须被命名，这正是下文 [PropEquiv_of_relation] 的用途。Test/ProbePropEquiv.v 的第二个反例钉死此拒绝。

 覆盖。Lib/Setoid.v 定义四个 setoid 构造子——[unit_setoid]、[eq_Setoid]、[funext_Setoid]、[Fin_Setoid]——Lib/Datatypes.v 另六个——[prod_setoid]、[sum_setoid]、[option_setoid]、[list_setoid]、[nat_setoid]、[fun_setoid]。每一个在下文都有实例。两文件皆未定义 sigma setoid，故无可传送；Lib/TList.v 与 Lib/NETList.v 的类型列表 setoid 属于求解器项语言，此处不覆盖。[Sets] 级传送——hom-setoid、二元与指标积、极限，以及范畴的 [LocallyPropositional] 语汇——见 Instance/Sets/Propositional.v。

 本段更早修订止于此。自 PR “代数载体是集合”（2026-09-17）起，本文件还携带两个传送——[dep_fun_PropEquiv] 与 [sigma_first_PropEquiv]——用于具体代数内联构建、而非经上述十个构造子之一的 setoid。它们陈述于文件末尾；为何以两蕴涵为参数而非命名典范 setoid，理由记在该处。
*)

(*
 [PropEquiv S] says that the setoid [S] has a [Prop]-valued equality: a
 relation [pequiv] in [Prop] that holds exactly when `≈` does.

 MEASURED UNIVERSES (About under Set Printing Universes):

 PropEquiv@{u p} :
 ∀ {A : Type@{u}}, Setoid@{u p} A → Type@{max(Set+1,u,p)}

 -- so at the [Setoid@{u u}] used by [Sets] and by every concrete algebraic
 carrier the class itself lands at [Type@{u}], the CARRIER universe, provided
 [u] is above [Set].  The [Set+1] in the maximum is the sort of [Prop] and is
 not avoidable; it is also harmless, since [Unset Universe Minimization
 ToSet] (Lib.v) keeps carrier universes off [Set]. 

 --------
 [PropEquiv S] 表示 setoid [S] 具有 [Prop] 值相等：关系 [pequiv] 在 [Prop] 中，且恰在 `≈` 成立时成立。

 度量宇宙（Set Printing Universes 下 About）：

 PropEquiv@{u p} :
 ∀ {A : Type@{u}}, Setoid@{u p} A → Type@{max(Set+1,u,p)}

 ——因而在 [Sets] 与每个具体代数载体所用的 [Setoid@{u u}] 上，该类本身落在载体宇宙 [Type@{u}]（只要 [u] 高于 [Set]）。最大值中的 [Set+1] 是 [Prop] 的排序，不可避免；但也无害，因 [Unset Universe Minimization ToSet]（Lib.v）使载体宇宙离开 [Set]。
*)
Class PropEquiv@{u p} {A : Type@{u}} (S : Setoid@{u p} A) := {
  pequiv : A -> A -> Prop;                              (* the Prop equality / Prop 相等 *)
  pequiv_to : forall x y, pequiv x y -> @equiv A S x y;   (* it implies `≈` / 它蕴涵 `≈` *)
  pequiv_from : forall x y, @equiv A S x y -> pequiv x y  (* and follows from it / 且由其推出 *)
}.

(* * ** Derived structure / * ** 派生结构 *)

Section Derived.

Context {A : Type}.
Context {S : Setoid A}.
Context {P : PropEquiv S}.

(*
 [pequiv] inherits the equivalence laws by transporting each one across the
 two implications.  This is the ambient [Equivalence] of the library, i.e.
 the [Type]-valued one of Coq.Classes.CRelationClasses that Lib/Foundation.v
 exports; a [Prop]-valued relation inhabits a [crelation] by cumulativity. 

 --------
 [pequiv] 经两蕴涵传送继承等价律。这是库的环境 [Equivalence]，即 Lib/Foundation.v 导出的 Coq.Classes.CRelationClasses 的 [Type] 值版本；[Prop] 值关系凭累积性居于 [crelation]。
*)
#[export] Instance pequiv_Equivalence : Equivalence (@pequiv A S P).
Proof.
  constructor.
  - intro x; exact (pequiv_from x x (reflexivity x)).
  - intros x y H; exact (pequiv_from y x (symmetry (pequiv_to x y H))).
  - intros x y z H1 H2;
      exact (pequiv_from x z (transitivity (pequiv_to x y H1) (pequiv_to y z H2))).
Defined.

(*
 The same laws as an instance of the [Prop]-level class of
 Coq.Classes.RelationClasses, for callers whose rewriting machinery is the
 [Prop] one rather than the library's [Type]-valued [CMorphisms]. 

 --------
 同样定律作为 Coq.Classes.RelationClasses 的 [Prop] 层级类实例，供重写机制为 [Prop] 而非库的 [Type] 值 [CMorphisms] 的调用方使用。
*)
#[export] Instance pequiv_Equivalence_Prop :
  RelationClasses.Equivalence (@pequiv A S P).
Proof.
  constructor.
  - intro x; exact (pequiv_from x x (reflexivity x)).
  - intros x y H; exact (pequiv_from y x (symmetry (pequiv_to x y H))).
  - intros x y z H1 H2;
      exact (pequiv_from x z (transitivity (pequiv_to x y H1) (pequiv_to y z H2))).
Defined.

(*
 [pequiv] respects `≈` in both arguments, up to [iff].  Note that [iff] here
 is Coq's [Prop]-valued biconditional, NOT the library's `↔`, which
 Lib/Foundation.v binds to [iffT]. 

 --------
 [pequiv] 在两自变量上至 [iff] 尊重 `≈`。注意此处 [iff] 是 Coq 的 [Prop] 值双条件，而非库的 `↔`（Lib/Foundation.v 将其绑定为 [iffT]）。
*)
#[export] Instance pequiv_Proper :
  Proper (equiv ==> equiv ==> iff) (@pequiv A S P).
Proof.
  intros x x' Hx y y' Hy; split; intro H.
  - apply pequiv_from.
    rewrite <- Hx, <- Hy.
    exact (pequiv_to _ _ H).
  - apply pequiv_from.
    rewrite Hx, Hy.
    exact (pequiv_to _ _ H).
Qed.

(*
 THE elimination [PropEquiv] buys.  [inhabited] is [Prop]-valued, so it
 eliminates only into [Prop]; the goal [x ≈ y] is in [Type] and is therefore
 out of reach directly.  Going through [pequiv] puts a [Prop] goal in front
 of the elimination, after which [pequiv_to] returns to `≈`.  Every
 truncation this library performs on an algebraic quotient is discharged by
 this one lemma. 

 --------
 [PropEquiv] 买到的消去。[inhabited] 为 [Prop] 值，故只能消去到 [Prop]；目标 [x ≈ y] 在 [Type] 中，因而无法直接触及。经 [pequiv] 把 [Prop] 目标置于消去之前，再用 [pequiv_to] 回到 `≈`。本库对代数商所做的每次截断都由这一引理消解。
*)
Lemma pequiv_elim_inhabited (x y : A) : inhabited (x ≈ y) -> x ≈ y.
Proof using A S P.
  intro H.
  apply (pequiv_to x y).
  destruct H as [h].
  exact (pequiv_from x y h).
Qed.

End Derived.

(*
 [P] is left implicit so that the elimination above is usable with no
 instance argument: an implicit argument of class type is closed by instance
 resolution, which is what makes [pequiv_elim_inhabited x y h] elaborate
 wherever the setoid has a registered [PropEquiv]. 

 --------
 [P] 保持左隐式，使上述消去无需实例参数即可用：类类型的隐式参数由实例解析关闭，这使 [pequiv_elim_inhabited x y h] 凡在 setoid 已注册 [PropEquiv] 处皆可细化。
*)
Arguments pequiv_elim_inhabited {A S P} x y _.

(*
 The constructor for a setoid whose `≈` already IS a [Prop]-valued relation.
 The relation has to be handed over by NAME: as the header says, writing
 [(x ≈ y : Prop)] is refused, since [equiv x y] is typed at [Type] whatever
 sits underneath.  Test/ProbePropEquiv.v pins that refusal. 

 --------
 `≈` 已经是 [Prop] 值关系的 setoid 的构造子。关系须按名称交出：如头注释所言，写 [(x ≈ y : Prop)] 会被拒绝，因无论底层为何，[equiv x y] 都排在 [Type]。Test/ProbePropEquiv.v 钉死该拒绝。
*)
Definition PropEquiv_of_relation@{u p} {A : Type@{u}} {S : Setoid@{u p} A}
  (R : A -> A -> Prop)
  (to : forall x y, R x y -> @equiv A S x y)
  (from : forall x y, @equiv A S x y -> R x y) : PropEquiv@{u p} S :=
  {| pequiv := R ; pequiv_to := to ; pequiv_from := from |}.

(* * ** Instances for the setoid constructors of Lib/Setoid.v / * ** Lib/Setoid.v 中 setoid 构造子的实例 *)

(*
 The discrete setoid: `≈` is Coq's [eq], which is already in [Prop].

 eq_PropEquiv@{u} : ∀ A : Type@{u}, PropEquiv@{u u} (eq_Setoid@{u} A)
 (* u |= u <= Logic_lemmas.equality.u0 *) 

 --------
 离散 setoid：`≈` 是 Coq 的 [eq]，已在 [Prop] 中。

 eq_PropEquiv@{u} : ∀ A : Type@{u}, PropEquiv@{u u} (eq_Setoid@{u} A)
 (* u |= u <= Logic_lemmas.equality.u0 *)
*)
#[export] Instance eq_PropEquiv@{u} (A : Type@{u}) :
  PropEquiv@{u u} (eq_Setoid@{u} A).
Proof.
  unshelve refine {| pequiv := @eq A |}.
  - intros x y h; exact h.
  - intros x y h; exact h.
Defined.

(*
 The terminal setoid [poly_unit] under [eq].

 unit_PropEquiv@{t u} : PropEquiv@{t u} unit_setoid@{t u}
 (* t u |= t <= Logic_lemmas.equality.u0 *) 

 --------
 [eq] 下的终 setoid [poly_unit]。

 unit_PropEquiv@{t u} : PropEquiv@{t u} unit_setoid@{t u}
 (* t u |= t <= Logic_lemmas.equality.u0 *)
*)
#[export] Instance unit_PropEquiv@{t u} : PropEquiv@{t u} unit_setoid@{t u}.
Proof.
  unshelve refine {| pequiv := @eq poly_unit@{t} |}.
  - intros x y h; exact h.
  - intros x y h; exact h.
Defined.

(*
 The standard finite types under [eq].

 Fin_PropEquiv@{} : ∀ {n : nat}, PropEquiv@{Set Set} Fin_Setoid 

 --------
 [eq] 下的标准有限类型。

 Fin_PropEquiv@{} : ∀ {n : nat}, PropEquiv@{Set Set} Fin_Setoid
*)
#[export] Instance Fin_PropEquiv {n} : PropEquiv (@Fin_Setoid n).
Proof.
  unshelve refine {| pequiv := @eq (Fin.t n) |}.
  - intros x y h; exact h.
  - intros x y h; exact h.
Defined.

(*
 The pointwise setoid on a dependent function space: propositional
 pointwise, given that the codomain is propositional.

 funext_PropEquiv@{u u0 u1 u2 u3 u4} :
 ∀ {T : Type@{u}} (t : T → Type@{u0}) (a b : T)
 {Sb : Setoid@{u0 u4} (t b)},
 PropEquiv@{u0 u4} Sb → PropEquiv@{u0 u1} (funext_Setoid t a b)
 (* u4 < u2, u0 <= u1, u0 <= u3, u2 <= u3, u4 <= u1 *) 

 --------
 依赖函数空间上的逐点 setoid：在陪域为命题性时，命题性逐点。

 funext_PropEquiv@{u u0 u1 u2 u3 u4} :
 ∀ {T : Type@{u}} (t : T → Type@{u0}) (a b : T)
 {Sb : Setoid@{u0 u4} (t b)},
 PropEquiv@{u0 u4} Sb → PropEquiv@{u0 u1} (funext_Setoid t a b)
 (* u4 < u2, u0 <= u1, u0 <= u3, u2 <= u3, u4 <= u1 *)
*)
#[export] Instance funext_PropEquiv {T : Type} (t : T -> Type) (a b : T)
  {Sb : Setoid (t b)} (Pb : PropEquiv Sb) :
  PropEquiv (@funext_Setoid T t a b Sb).
Proof.
  unshelve refine {| pequiv := fun f g => forall x : t a, @pequiv _ _ Pb (f x) (g x) |}.
  - intros f g H x; exact (pequiv_to _ _ (H x)).
  - intros f g H x; exact (pequiv_from _ _ (H x)).
Defined.

(* * ** Instances for the setoid constructors of Lib/Datatypes.v / * ** Lib/Datatypes.v 中 setoid 构造子的实例 *)

(*
 The non-dependent function setoid.

 fun_PropEquiv@{u u0 u1 u2 u3 u4 u5 u6} :
 ∀ {A : Type@{u}} {B : Type@{u0}} {SB : Setoid@{u0 u6} B},
 PropEquiv@{u0 u6} SB → PropEquiv@{u1 u2} (fun_setoid A B)
 (* u6 < u3, u <= u1, u <= u2, u0 <= u1, u0 <= u4, u0 <= u5,
 u3 <= u4, u6 <= u2, u6 <= u5 *) 

 --------
 非依赖函数 setoid。

 fun_PropEquiv@{u u0 u1 u2 u3 u4 u5 u6} :
 ∀ {A : Type@{u}} {B : Type@{u0}} {SB : Setoid@{u0 u6} B},
 PropEquiv@{u0 u6} SB → PropEquiv@{u1 u2} (fun_setoid A B)
 (* u6 < u3, u <= u1, u <= u2, u0 <= u1, u0 <= u4, u0 <= u5,
 u3 <= u4, u6 <= u2, u6 <= u5 *)
*)
#[export] Instance fun_PropEquiv {A : Type} {B : Type} {SB : Setoid B}
  (PB : PropEquiv SB) : PropEquiv (@fun_setoid A B SB).
Proof.
  unshelve refine {| pequiv := fun f g => forall x : A, @pequiv _ _ PB (f x) (g x) |}.
  - intros f g H x; exact (pequiv_to _ _ (H x)).
  - intros f g H x; exact (pequiv_from _ _ (H x)).
Defined.

(*
 The product setoid, componentwise.  The conjunction is Coq's [and] (written
 `/\`), not the library's `∧`, which Lib/Foundation.v binds to [prod] and
 which would put the relation back in [Type].

 prod_PropEquiv@{u u0 u1 u2 u3 u4} :
 ∀ {A : Type@{u}} {B : Type@{u0}} {SA : Setoid@{u u3} A}
 {SB : Setoid@{u0 u4} B},
 PropEquiv@{u u3} SA → PropEquiv@{u0 u4} SB →
 PropEquiv@{u1 u2} prod_setoid
 (* u <= u1, u0 <= u1, u3 <= u2, u4 <= u2, and the stdlib bounds
 u <= prod_rect.u1, u0 <= prod_rect.u2, u3 <= projections.u0,
 u4 <= projections.u1 *) 

 --------
 积 setoid，按分量。合取是 Coq 的 [and]（写作 `/\`），而非库的 `∧`（Lib/Foundation.v 将其绑定为 [prod]，会把关系放回 [Type]）。

 prod_PropEquiv@{u u0 u1 u2 u3 u4} :
 ∀ {A : Type@{u}} {B : Type@{u0}} {SA : Setoid@{u u3} A}
 {SB : Setoid@{u0 u4} B},
 PropEquiv@{u u3} SA → PropEquiv@{u0 u4} SB →
 PropEquiv@{u1 u2} prod_setoid
 (* u <= u1, u0 <= u1, u3 <= u2, u4 <= u2，以及标准库界
 u <= prod_rect.u1, u0 <= prod_rect.u2, u3 <= projections.u0,
 u4 <= projections.u1 *)
*)
#[export] Instance prod_PropEquiv {A B : Type} {SA : Setoid A} {SB : Setoid B}
  (PA : PropEquiv SA) (PB : PropEquiv SB) :
  PropEquiv (@prod_setoid A B SA SB).
Proof.
  unshelve refine
    {| pequiv := fun x y => @pequiv _ _ PA (fst x) (fst y)
                            /\ @pequiv _ _ PB (snd x) (snd y) |}.
  - intros x y [H1 H2]; exact (pequiv_to _ _ H1, pequiv_to _ _ H2).
  - intros x y H; split;
      [ exact (pequiv_from _ _ (fst H)) | exact (pequiv_from _ _ (snd H)) ].
Defined.

(*
 The coproduct setoid: same injection and equivalent contents.

 sum_PropEquiv@{u u0 u1 u2 u3 u4} :
 ∀ {A : Type@{u}} {B : Type@{u0}} {SA : Setoid@{u u3} A}
 {SB : Setoid@{u0 u4} B},
 PropEquiv@{u u3} SA → PropEquiv@{u0 u4} SB →
 PropEquiv@{u1 u2} sum_setoid
 (* u <= u1, u0 <= u1, u3 <= u2, u4 <= u2, plus the stdlib bounds
 u2 <= sum_rect.u0, u3 <= False_rect.u0, u4 <= False_rect.u0 *) 

 --------
 余积 setoid：同一注入且内容等价。

 sum_PropEquiv@{u u0 u1 u2 u3 u4} :
 ∀ {A : Type@{u}} {B : Type@{u0}} {SA : Setoid@{u u3} A}
 {SB : Setoid@{u0 u4} B},
 PropEquiv@{u u3} SA → PropEquiv@{u0 u4} SB →
 PropEquiv@{u1 u2} sum_setoid
 (* u <= u1, u0 <= u1, u3 <= u2, u4 <= u2，另加标准库界
 u2 <= sum_rect.u0, u3 <= False_rect.u0, u4 <= False_rect.u0 *)
*)
#[export] Instance sum_PropEquiv {A B : Type} {SA : Setoid A} {SB : Setoid B}
  (PA : PropEquiv SA) (PB : PropEquiv SB) :
  PropEquiv (@sum_setoid A B SA SB).
Proof.
  unshelve refine
    {| pequiv := fun x y =>
         match x, y with
         | inl x, inl y => @pequiv _ _ PA x y
         | inr x, inr y => @pequiv _ _ PB x y
         | _, _ => False
         end |}.
  - intros [x|x] [y|y] H; simpl in *; try contradiction;
      [ exact (@pequiv_to _ _ PA x y H) | exact (@pequiv_to _ _ PB x y H) ].
  - intros [x|x] [y|y] H; simpl in *; try contradiction;
      [ exact (@pequiv_from _ _ PA x y H) | exact (@pequiv_from _ _ PB x y H) ].
Defined.

(*
 The option setoid.  [None ≈ None] is already the [Prop] [True], so the
 relation below agrees with `≈` on the nose at that clause.

 option_PropEquiv@{u u0} :
 ∀ {A : Type@{u}} {SA : Setoid@{u u0} A},
 PropEquiv@{u u0} SA → PropEquiv@{u u0} option_setoid
 (* u u0 |= u <= eq_ind.u0, u0 <= False_rect.u0 *) 

 --------
 option setoid。[None ≈ None] 已是 [Prop] 的 [True]，故下文关系在该子句上与 `≈` 鼻尖一致。

 option_PropEquiv@{u u0} :
 ∀ {A : Type@{u}} {SA : Setoid@{u u0} A},
 PropEquiv@{u u0} SA → PropEquiv@{u u0} option_setoid
 (* u u0 |= u <= eq_ind.u0, u0 <= False_rect.u0 *)
*)
#[export] Instance option_PropEquiv {A : Type} {SA : Setoid A}
  (PA : PropEquiv SA) : PropEquiv (@option_setoid A SA).
Proof.
  unshelve refine
    {| pequiv := fun x y =>
         match x, y with
         | Some x, Some y => @pequiv _ _ PA x y
         | None, None => True
         | _, _ => False
         end |}.
  - intros [x|] [y|] H; simpl in *; try contradiction.
    + exact (@pequiv_to _ _ PA x y H).
    + exact I.
  - intros [x|] [y|] H; simpl in *; try contradiction.
    + exact (@pequiv_from _ _ PA x y H).
    + exact I.
Defined.

(*
 The list setoid.  [list_equiv] (Lib/Datatypes.v) is a [Type]-valued
 fixpoint using `∧` = [prod]; the [Prop] mirror below uses [and], and the two
 implications are structural inductions. 

 --------
 列表 setoid。[list_equiv]（Lib/Datatypes.v）是使用 `∧` = [prod] 的 [Type] 值不动点；下文 [Prop] 镜像使用 [and]，两蕴涵为结构归纳。
*)
Fixpoint list_pequiv {A : Type} {SA : Setoid A} (PA : PropEquiv SA)
  (xs ys : list A) : Prop :=
  match xs, ys with
  | nil, nil => True
  | cons x xs, cons y ys => @pequiv _ _ PA x y /\ list_pequiv PA xs ys
  | _, _ => False
  end.

(*
   list_PropEquiv@{u u0} :
   ∀ {A : Type@{u}} {SA : Setoid@{u u0} A},
   PropEquiv@{u u0} SA → PropEquiv@{u u0} list_setoid
   (* u u0 |= u <= list_rect.u0, u <= list_rect.u1, u <= list_ind.u0,
   u0 <= False_rect.u0, u0 <= projections.u0, u0 <= projections.u1,
   u0 <= list_rect.u0 *) 

   --------
   list_PropEquiv@{u u0} :
   ∀ {A : Type@{u}} {SA : Setoid@{u u0} A},
   PropEquiv@{u u0} SA → PropEquiv@{u u0} list_setoid
   (* u u0 |= u <= list_rect.u0, u <= list_rect.u1, u <= list_ind.u0,
   u0 <= False_rect.u0, u0 <= projections.u0, u0 <= projections.u1,
   u0 <= list_rect.u0 *)
*)
#[export] Instance list_PropEquiv {A : Type} {SA : Setoid A}
  (PA : PropEquiv SA) : PropEquiv (@list_setoid A SA).
Proof.
  unshelve refine {| pequiv := list_pequiv PA |}.
  - intro xs; induction xs as [|x xs IH]; intros [|y ys] H;
      simpl in *; try contradiction.
    + exact I.
    + exact (@pequiv_to _ _ PA x y (proj1 H), IH ys (proj2 H)).
  - intro xs; induction xs as [|x xs IH]; intros [|y ys] H;
      simpl in *; try contradiction.
    + exact I.
    + exact (conj (@pequiv_from _ _ PA x y (fst H)) (IH ys (snd H))).
Defined.

(*
 [nat_setoid] (Lib/Datatypes.v) is declared as a bare [Program Instance]
 whose [equiv] field is left to instance resolution, which picks [eq].  The
 two implications below are therefore the identity, and the file's
 [Unset Transparent Obligations] does not stand in the way: the [equiv] field
 is resolved during elaboration rather than becoming an opaque obligation.

 nat_PropEquiv@{} : PropEquiv@{Set Set} nat_setoid 

 --------
 [nat_setoid]（Lib/Datatypes.v）声明为裸 [Program Instance]，其 [equiv] 字段留给实例解析（选取 [eq]）。故下文两蕴涵即恒等；文件的 [Unset Transparent Obligations] 不构成障碍：[equiv] 在细化期间解析，而非成为不透明义务。

 nat_PropEquiv@{} : PropEquiv@{Set Set} nat_setoid
*)
#[export] Instance nat_PropEquiv : PropEquiv nat_setoid.
Proof.
  unshelve refine {| pequiv := @eq nat |}.
  - intros x y h; exact h.
  - intros x y h; exact h.
Defined.

(* * ** Transports for setoids built inline / * ** 内联构建的 setoid 的传送 *)

(*
 The two shapes below are the ones the concrete algebraic categories reach
 for, and neither is one of the ten constructors above: a carrier that is a
 DEPENDENT FUNCTION SPACE compared pointwise (the product of a family of
 modules, Instance/Mod/Product.v; the standard vector space over a field,
 Instance/FdVect.v) and a carrier that is a SIGMA compared on its first
 projection (a kernel, Instance/Ab.v; a subgroup or submodule,
 Instance/Ab/DirectedColimit.v and Instance/Mod/Quotient.v; the centre
 of a group, Instance/Grp/Center.v).

 WHY BOTH TAKE THEIR TWO IMPLICATIONS AS ARGUMENTS.  Each of those sites
 writes the relation out inline inside a [Program Definition], so the setoid
 it produces is a NAMED constant whose [setoid_equiv] field is an opaque
 [Program] obligation.  A transport stated as [PropEquiv (canonical_setoid …)]
 would therefore have to unify that constant with a canonical one, and the two
 opaque obligation proofs are not convertible; the unification is refused even
 though the [equiv] fields agree on the nose.  Taking the two implications as
 explicit arguments sidesteps the record entirely: at every site above they
 are [fun _ _ h => h], since the relations ARE convertible, and the transport
 then applies to whichever setoid the site happens to have built.  This is a
 generalisation of the form these lemmas were first drafted in, which named
 the setoid.

 Measured (About under Set Printing Universes):

 dep_fun_PropEquiv@{u u0 u1 u2 u3} :
 ∀ {I : Type@{u}} {A : I → Type@{u0}} {SA : ∀ i : I, Setoid@{u0 u3} (A i)}
 (S : Setoid@{u1 u2} (∀ i : I, A i)),
 (∀ f g : ∀ i : I, A i,
 (∀ i : I, @equiv (A i) (SA i) (f i) (g i)) → @equiv _ S f g) →
 (∀ f g : ∀ i : I, A i,
 @equiv _ S f g → ∀ i : I, @equiv (A i) (SA i) (f i) (g i)) →
 (∀ i : I, PropEquiv@{u0 u3} (SA i)) → PropEquiv@{u1 u2} S
 (* u u0 u1 u2 u3 |= u <= u1, u0 <= u1 *)

 -- the target carrier universe [u1] is bounded below by the index and by the
 components and by nothing else, so a pointwise product of carrier-sized
 propositional setoids stays carrier-sized. 

 --------
 以下两种形状是具体代数范畴所触及的，且皆非上述十个构造子之一：载体为逐点比较的依赖函数空间（模族的积，Instance/Mod/Product.v；域上的标准向量空间，Instance/FdVect.v），以及在第一投影上比较的 sigma 载体（核，Instance/Ab.v；子群或子模，Instance/Ab/DirectedColimit.v 与 Instance/Mod/Quotient.v；群的中心，Instance/Grp/Center.v）。

 为何两者都以两蕴涵为参数。上述各点在 [Program Definition] 内内联写出关系，故产生的 setoid 是命名常量，其 [setoid_equiv] 字段为不透明 [Program] 义务。若传送写成 [PropEquiv (canonical_setoid …)]，须把该常量与典范者合一，而两个不透明义务证明不可转换；即便 [equiv] 字段鼻尖一致，合一仍被拒绝。把两蕴涵取为显式参数则完全绕开记录：在上述每一点它们都是 [fun _ _ h => h]（因关系可转换），传送于是适用于该点碰巧构建的任意 setoid。这是这些引理最初草稿形式的推广，彼时曾命名 setoid。

 度量（Set Printing Universes 下 About）：

 dep_fun_PropEquiv@{u u0 u1 u2 u3} :
 ∀ {I : Type@{u}} {A : I → Type@{u0}} {SA : ∀ i : I, Setoid@{u0 u3} (A i)}
 (S : Setoid@{u1 u2} (∀ i : I, A i)),
 (∀ f g : ∀ i : I, A i,
 (∀ i : I, @equiv (A i) (SA i) (f i) (g i)) → @equiv _ S f g) →
 (∀ f g : ∀ i : I, A i,
 @equiv _ S f g → ∀ i : I, @equiv (A i) (SA i) (f i) (g i)) →
 (∀ i : I, PropEquiv@{u0 u3} (SA i)) → PropEquiv@{u1 u2} S
 (* u u0 u1 u2 u3 |= u <= u1, u0 <= u1 *)

 ——目标载体宇宙 [u1] 仅被指标与分量下界，别无其他，故载体规模命题性 setoid 的逐点积仍为载体规模。
*)
Definition dep_fun_PropEquiv {I : Type} {A : I -> Type}
  {SA : forall i : I, Setoid (A i)} (S : Setoid (forall i : I, A i))
  (to : forall f g : forall i : I, A i,
          (forall i : I, @equiv (A i) (SA i) (f i) (g i)) -> @equiv _ S f g)
  (from : forall f g : forall i : I, A i,
            @equiv _ S f g -> forall i : I, @equiv (A i) (SA i) (f i) (g i))
  (H : forall i : I, PropEquiv (SA i)) : PropEquiv S.
Proof.
  unshelve refine
    {| pequiv := fun f g => forall i : I, @pequiv _ _ (H i) (f i) (g i) |}.
  - intros f g Hfg.
    apply to; intro i; exact (pequiv_to _ _ (Hfg i)).
  - intros f g Hfg i.
    exact (pequiv_from _ _ (from _ _ Hfg i)).
Defined.

(*
 The sigma case.  Only the first projection is compared, so the second
 component's type [P] is arbitrary and no [Prop] mirror is asked of it: a
 kernel element's proof that it is killed, a subgroup element's proof of
 membership, are carried along and never inspected by `≈`.  That is why the
 membership predicates of the concrete algebra may stay [Type]-valued while
 their carriers become propositional.

 Measured:

 sigma_first_PropEquiv@{u u0 u1 u2 u3} :
 ∀ {A : Type@{u}} {SA : Setoid@{u u3} A} {P : A → Type@{u0}}
 (S : Setoid@{u1 u2} (@sigT A P)),
 (∀ p q : @sigT A P, @equiv A SA (projT1 p) (projT1 q) → @equiv _ S p q) →
 (∀ p q : @sigT A P, @equiv _ S p q → @equiv A SA (projT1 p) (projT1 q)) →
 PropEquiv@{u u3} SA → PropEquiv@{u1 u2} S
 (* u u0 u1 u2 u3 |= u <= u1, u0 <= u1, and the stdlib bounds
 u <= Projections.u0, u0 <= Projections.u1 *) 

 --------
 sigma 情形。仅比较第一投影，故第二分量类型 [P] 任意，且不要求其 [Prop] 镜像：核元素“被消灭”的证明、子群元素的成员证明，随携带行而从不为 `≈` 检查。这正是具体代数的成员谓词可保持 [Type] 值而其载体变为命题性的原因。

 度量：

 sigma_first_PropEquiv@{u u0 u1 u2 u3} :
 ∀ {A : Type@{u}} {SA : Setoid@{u u3} A} {P : A → Type@{u0}}
 (S : Setoid@{u1 u2} (@sigT A P)),
 (∀ p q : @sigT A P, @equiv A SA (projT1 p) (projT1 q) → @equiv _ S p q) →
 (∀ p q : @sigT A P, @equiv _ S p q → @equiv A SA (projT1 p) (projT1 q)) →
 PropEquiv@{u u3} SA → PropEquiv@{u1 u2} S
 (* u u0 u1 u2 u3 |= u <= u1, u0 <= u1，以及标准库界
 u <= Projections.u0, u0 <= Projections.u1 *)
*)
Definition sigma_first_PropEquiv {A : Type} {SA : Setoid A} {P : A -> Type}
  (S : Setoid (@sigT A P))
  (to : forall p q : @sigT A P,
          @equiv A SA (projT1 p) (projT1 q) -> @equiv _ S p q)
  (from : forall p q : @sigT A P,
            @equiv _ S p q -> @equiv A SA (projT1 p) (projT1 q))
  (PA : PropEquiv SA) : PropEquiv S.
Proof.
  unshelve refine
    {| pequiv := fun p q => @pequiv _ _ PA (projT1 p) (projT1 q) |}.
  - intros p q Hpq.
    apply to; exact (pequiv_to _ _ Hpq).
  - intros p q Hpq.
    exact (pequiv_from _ _ (from _ _ Hpq)).
Defined.
