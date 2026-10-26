Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Comonad.Core.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** * Coalgebras over a comonad; the co-Eilenberg–Moore category / * 余范畴上的余代数；余艾伦伯格–摩尔范畴 *)

(*
nLab:      https://ncatlab.org/nlab/show/coalgebra+over+a+comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   For a comonad (W, extract, duplicate) = (W, ε, δ) on a category C — see
   Comonad/Core.v for the covariant API — a W-coalgebra on an object a is a
   costructure map γ : a ~> W a ([w_coalg]) satisfying the counit law
   ε ∘ γ ≈ id ([w_counit_law]) and the coaction law W γ ∘ γ ≈ δ ∘ γ
   ([w_coaction]).  A morphism of W-coalgebras (a, γ^a) ~> (b, γ^b) is a
   C-morphism f : a ~> b intertwining the costructure maps,
   γ^b ∘ f ≈ W f ∘ γ^a ([w_coalg_hom_commutes]).

   Since [Comonad C W] is by definition [@Monad (C^op) (W^op)]
   (Theory/Monad.v), a W-coalgebra is exactly an Eilenberg–Moore algebra
   ([TAlgebra], Monad/Algebra.v) for that opposite monad, and the category
   of W-coalgebras — the co-Eilenberg–Moore category C_W — is obtained
   here, dually to Monad/Eilenberg/Moore.v, as the opposite of the
   Eilenberg–Moore category of the opposite monad, rather than by
   re-proving the category laws:

       CoEilenbergMoore := (EilenbergMoore (W^op))^op

   Because duality is built into this library so that C^op^op = C holds by
   reflexivity, the two presentations agree definitionally: the classes
   [WCoalgebra]/[WCoalgebraHom] below are covariant re-readings of
   [TAlgebra]/[TAlgebraHom] over the opposite monad, converted in both
   directions field by field with [exact] (no proofs are re-done), and the
   hom-sets of [CoEilenbergMoore] are literally the algebra homomorphisms
   of the opposite monad ([coeilenberg_moore_hom], which holds by
   reflexivity).  The covariant category [WCoalgebras] assembled from the
   classes below is isomorphic in Cat to [CoEilenbergMoore]
   ([WCoalgebras_CoEilenbergMoore_Iso]); both functors are the identity on
   carriers and underlying morphisms, and the natural isomorphisms
   witnessing the two round trips have identity components.

--------
nLab：https://ncatlab.org/nlab/show/coalgebra+over+a+comonad
维基百科：https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

对于一个在范畴 C 上的余单子 (W, extract, duplicate) = (W, ε, δ) —— 参见 Comonad/Core.v 中的协变 API —— 对象 a 上的 W-余代数是一个共结构映射 γ : a ~> W a ([w_coalg])，满足余单位律 ε ∘ γ ≈ id ([w_counit_law]) 和余作用律 W γ ∘ γ ≈ δ ∘ γ ([w_coaction])。W-余代数 (a, γ^a) ~> (b, γ^b) 的态射是一个 C-态射 f : a ~> b，使共结构映射相互纠缠，即 γ^b ∘ f ≈ W f ∘ γ^a ([w_coalg_hom_commutes])。

由于 [Comonad C W] 按定义是 [@Monad (C^op) (W^op)]（Theory/Monad.v），W-上代数恰好是该对偶幺半群的 Eilenberg–Moore 代数（[TAlgebra], Monad/Algebra.v），而 W-上代数的范畴——co-Eilenberg–Moore 范畴 C_W——在此是通过将对偶幺半群的 Eilenberg–Moore 范畴取对偶得到的，与 Monad/Eilenberg/Moore.v 中的处理方式相反，而不是通过重新证明范畴定律得到的：

CoEilenbergMoore := (EilenbergMoore (W^op))^op

因为二重性内建于此库中，使得 C^op^op = C 可以通过自反性成立，所以这两种表示在定义上是一致的：下面的类 [WCoalgebra]/[WCoalgebraHom] 是 [TAlgebra]/[TAlgebraHom] 在对偶单子上的协变重读，通过 [exact] 在各字段之间双向转换（没有重新做证明），而 [CoEilenbergMoore] 的 Hom 集字面上就是对偶单子的代数同态（[coeilenberg_moore_hom]，通过自反性成立）。由下面这些类组装的协变范畴 [WCoalgebras] 在 Cat 中同构于 [CoEilenbergMoore] ([WCoalgebras_CoEilenbergMoore_Iso])；两个函子在载体和底层态射上都是恒等的，并且见证这两个往返的自然同构的分量也都是恒等的。
*)

(*
What a coalgebra is for

   nLab:  https://ncatlab.org/nlab/show/comonadic+functor
   nLab:  https://ncatlab.org/nlab/show/store+comonad
   Paper: O'Connor, “Functor is to Lens as Applicative is to Biplate:
          Introducing Multiplate”, arXiv:1103.2841, 2011
   Paper: Bénabou, Roubaud, “Monades et descente”, C. R. Acad. Sc. Paris,
          Sér. A 270, 1970, pp. 96-98

   A W-coalgebra is an object equipped with coherent access to its own
   contexts.  The costructure map γ : a ~> W a places each element of a
   into a W-context; [w_counit_law] states that reading the placement
   back with ε recovers the element; and [w_coaction] states that
   placing twice agrees with placing once and duplicating.  Where the
   cofree coalgebras (W x, δ) supply contexts generically, an arbitrary
   coalgebra carries its own structured way of being in context.

   Two instances make the definition concrete.  For the store comonad
   (s ⇒ −) × s (Instance/Coq/Comonad/Store.v), a coalgebra structure on
   a carrier a amounts to a pair of maps get : a → s and put : s × a → a,
   and the counit and coaction laws are together equivalent to the three
   lens laws: put (get a, a) = a; get (put (σ, a)) = σ; and
   put (τ, put (σ, a)) = put (τ, a).  Coalgebras of the store comonad
   are therefore exactly the lawful (“very well-behaved”) lenses of
   functional programming, a correspondence due to O'Connor (2010;
   arXiv:1103.2841).  For the environment comonad e × −
   (Instance/Coq/Comonad/Env.v) the classification is simpler still: a
   coalgebra on a is the same thing as a morphism a → e, and the
   category of coalgebras is isomorphic to the slice category over e.

   The cofree side of the theory dualizes the free algebras over a
   monad, with one orientation worth fixing in the mind: for a comonad
   it is the cofree functor that is the RIGHT adjoint, the forgetful
   functor from coalgebras to C being a left adjoint (Comonad/Duality.v,
   [CoEM_Adjunction], [CoEM_Cofree]), and the comonad this adjunction
   induces on C is W itself.  A functor is comonadic when it has a right
   adjoint and the comparison into the coalgebras of the induced comonad
   is an equivalence of categories; Beck's monadicity theorem has its
   exact comonadic dual, with split equalizers in the role that split
   coequalizers play for monads.  The monad side is formalized in
   Monad/Monadicity/Beck.v.

   The classical payoff of these categories is descent theory.  For a
   bifibration satisfying the Beck–Chevalley condition, the descent data
   along a morphism form the Eilenberg–Moore category of the monad
   induced by the base-change adjunction (Bénabou–Roubaud 1970); for an
   adjoint triple f_! ⊣ f^* ⊣ f_* the same data are equally coalgebras
   over the comonad f^* f_*; and Grothendieck's faithfully flat descent,
   through the extension-of-scalars adjunction, is the classical
   instance.  The same resolution machinery yields the simplicial bar
   construction on an algebra, whose contracting homotopy makes its
   acyclicity absolute — preserved by every functor — and on which
   comonad (cotriple) cohomology is founded (Barr–Beck, Springer LNM 80,
   1969).  Coalgebras over the jet comonad of a base-change adjunction
   are partial differential equations (Marvan, 1986).  None of this is
   formalized in this file; the pointers record where the notion earns
   its keep.

--------
煤代数的用途是什么

nLab: https://ncatlab.org/nlab/show/comonadic+functor
nLab: https://ncatlab.org/nlab/show/store+comonad
论文: O'Connor, 《函子之于透镜正如应用函子之于双板：引入多板》, arXiv:1103.2841, 2011
论文: Bénabou, Roubaud, 《Monad与下降》, 巴黎科学院学报, 系列 A 270, 1970, 第 96-98 页

W-余代数是一个配备了对自身上下文进行一致访问的对象。余结构映射 γ : a ~> W a 将 a 的每个元素放入 W 上下文；[w_counit_law] 说明通过 ε 读取该放置可以恢复元素；[w_coaction] 说明双重放置与单次放置并复制是一致的。当余自由余代数 (W x, δ) 通用地提供上下文时，任意余代数携带自身在上下文中的结构化方式。

两个实例使定义具体化。对于存储余单子 (s ⇒ −) × s (Instance/Coq/Comonad/Store.v)，承载对象 a 上的余代数结构相当于一对映射 get : a → s 和 put : s × a → a，并且余单位和余作用律共同等价于三个透镜定律：put (get a, a) = a；get (put (σ, a)) = σ；以及 put (τ, put (σ, a)) = put (τ, a)。因此，存储余单子的余代数恰好是函数式编程中的合法（“行为非常良好”）透镜，这一对应关系归功于 O'Connor (2010; arXiv:1103.2841)。对于环境余单子 e × − (Instance/Coq/Comonad/Env.v)，分类则更简单：a 上的余代数与映射 a → e 相同，并且余代数范畴与 over e 的切片范畴同构。

该理论的共自由方面对单子上的自由代数进行对偶，有一个方向值得牢记：对于余单子，共自由函子是右伴随，而从余代数到C的遗忘函子是左伴随（Comonad/Duality.v, [CoEM_Adjunction], [CoEM_Cofree]），这个伴随在C上诱导的余单子就是W本身。当一个函子具有右伴随并且诱导的余单子中的余代数的比较是范畴等价时，该函子是余单子的；Beck的单子性定理有其精确的余单子对偶，其中分裂等化器起到单子中分裂余等化器的作用。单子方面形式化在Monad/Monadicity/Beck.v。

这些范畴的经典回报是下降理论。对于满足 Beck–Chevalley 条件的双纤维化，一个态射下的下降数据形成由基变换伴随引出单子的 Eilenberg–Moore 范畴（Bénabou–Roubaud 1970）；对于一个伴随三元组 f_! ⊣ f^* ⊣ f_*，相同的数据同样是余伴随 f^* f_* 上的余代数；而通过标量扩展伴随，Grothendieck 的忠实平坦下降是经典实例。相同的解析机制产生了代数上的单纯条构造，其收缩同伦使其不可循环性成为绝对的——被每个函子保持——并且在其上建立了余单子（共三重）上同调（Barr–Beck，Springer LNM 80，1969）。基变换伴随的喷射余单子上的余代数是偏微分方程（Marvan, 1986）。这些内容都未在此文件中形式化；这些指引记录了该概念的价值所在。
*)

(*
The covariant coalgebra class.  Its three fields are, definitionally,
   the fields of [@TAlgebra (C^op) (W^op) H a]: the costructure map read
   covariantly, the counit law as the op-read of [t_id] (whose [ret] is
   [extract]), and the coaction law as the op-read of [t_action] (whose
   [join] is [duplicate] and whose [fmap] is [fmap[W]], with each composite
   read backwards).  See [WCoalgebra_to_TAlgebra] below.

--------
协变余代数类。它的三个字段在定义上是 [@TAlgebra (C^op) (W^op) H a] 的字段：以协变方式读取的余结构映射，作为 [t_id] 的反向读取的余单位律（其 [ret] 为 [extract]），以及作为 [t_action] 的反向读取的余作用律（其 [join] 为 [duplicate] 且其 [fmap] 为 [fmap[W]，每个复合都向后读取）。见下文的 [WCoalgebra_to_TAlgebra]。
*)

Class WCoalgebra {C : Category} (W : C ⟶ C) {H : @Comonad C W} (a : C) := {
  w_coalg : a ~> W a;

  w_counit_law : @extract C W H a ∘ w_coalg ≈ id;
  w_coaction :
    fmap[W] w_coalg ∘ w_coalg ≈ @duplicate C W H a ∘ w_coalg
}.

Notation "w_coalg[ F ]" := (@w_coalg _ _ _ _ F)
  (at level 9, format "w_coalg[ F ]") : morphism_scope.

(*
A homomorphism of W-coalgebras: an underlying arrow f : a ~> b commuting
   with the costructure maps, γ^b ∘ f ≈ W f ∘ γ^a.  Definitionally this is
   [TAlgebraHom] over the opposite monad with source and target swapped
   (the op-read reverses homs); see [WCoalgebraHom_to_TAlgebraHom].

--------
W-余代数的同态：一个基本箭头 f : a ~> b，与余结构映射交换，即 γ^b ∘ f ≈ W f ∘ γ^a。从定义上讲，这是在相反单子上交换源和目标的 [TAlgebraHom]（op-读操作会反转同态）；参见 [WCoalgebraHom_to_TAlgebraHom]。
*)

Class WCoalgebraHom {C : Category} (W : C ⟶ C) {H : @Comonad C W}
      (a b : C) (F : @WCoalgebra C W H a) (G : @WCoalgebra C W H b) := {
  w_coalg_hom : a ~> b;

  w_coalg_hom_commutes :
    w_coalg[G] ∘ w_coalg_hom ≈ fmap[W] w_coalg_hom ∘ w_coalg[F]
}.

Notation "w_coalg_hom[ f ]" := (@w_coalg_hom _ _ _ _ _ _ _ f)
  (at level 9, format "w_coalg_hom[ f ]") : morphism_scope.

Section CoEilenbergMoore.

Context {C : Category} {W : C ⟶ C} {H : @Comonad C W}.

(**
** Definitional conversions with algebras over the opposite monad

    Each conversion transports every field by [exact]: the statements are
    definitionally equal, so no equational reasoning is involved.

--------
** 对偶幺半群上的代数的定义性转换

每个转换都通过 [exact] 传输每个字段：这些语句在定义上是相等的，因此不涉及方程推理。
*)

Definition WCoalgebra_to_TAlgebra {a : C} (F : @WCoalgebra C W H a) :
  @TAlgebra (C^op) (W^op) H a :=
  @Build_TAlgebra (C^op) (W^op) H a
    (@w_coalg C W H a F)
    (@w_counit_law C W H a F)
    (@w_coaction C W H a F).

Definition TAlgebra_to_WCoalgebra {a : C} (F : @TAlgebra (C^op) (W^op) H a) :
  @WCoalgebra C W H a :=
  @Build_WCoalgebra C W H a
    (@t_alg (C^op) (W^op) H a F)
    (@t_id (C^op) (W^op) H a F)
    (@t_action (C^op) (W^op) H a F).

(**
The costructure map is untouched by the round trip (and likewise in the
    other direction): the conversions only repackage fields.

--------
结构映射在往返过程中保持不变（在另一个方向也是如此）：转换只是重新打包字段。
*)

Lemma WCoalgebra_to_TAlgebra_alg {a : C} (F : @WCoalgebra C W H a) :
  t_alg[WCoalgebra_to_TAlgebra F] ≈ w_coalg[F].
Proof. reflexivity. Qed.

Lemma TAlgebra_to_WCoalgebra_coalg {a : C} (F : @TAlgebra (C^op) (W^op) H a) :
  w_coalg[TAlgebra_to_WCoalgebra F] ≈ t_alg[F].
Proof. reflexivity. Qed.

(*
A coalgebra homomorphism (a, γ^a) ~> (b, γ^b) is an algebra homomorphism
   over the opposite monad from (b, γ^b) to (a, γ^a): the op-read reverses
   the direction of the underlying arrow, while the commuting square is the
   same C-equation.

--------
一个余代数同态 (a, γ^a) ~> (b, γ^b) 是一个代数同态，它是从 (b, γ^b) 到 (a, γ^a) 的对偶单子上的：op-read 会反转底层箭头的方向，而交换方块是相同的 C 方程。
*)

Definition WCoalgebraHom_to_TAlgebraHom {a b : C}
  {F : @WCoalgebra C W H a} {G : @WCoalgebra C W H b}
  (f : @WCoalgebraHom C W H a b F G) :
  @TAlgebraHom (C^op) (W^op) H b a
    (WCoalgebra_to_TAlgebra G) (WCoalgebra_to_TAlgebra F) :=
  @Build_TAlgebraHom (C^op) (W^op) H b a
    (WCoalgebra_to_TAlgebra G) (WCoalgebra_to_TAlgebra F)
    (@w_coalg_hom C W H a b F G f)
    (@w_coalg_hom_commutes C W H a b F G f).

Definition TAlgebraHom_to_WCoalgebraHom {a b : C}
  {F : @TAlgebra (C^op) (W^op) H a} {G : @TAlgebra (C^op) (W^op) H b}
  (f : @TAlgebraHom (C^op) (W^op) H b a G F) :
  @WCoalgebraHom C W H a b
    (TAlgebra_to_WCoalgebra F) (TAlgebra_to_WCoalgebra G) :=
  @Build_WCoalgebraHom C W H a b
    (TAlgebra_to_WCoalgebra F) (TAlgebra_to_WCoalgebra G)
    (@t_alg_hom (C^op) (W^op) H b a G F f)
    (@t_alg_hom_commutes (C^op) (W^op) H b a G F f).

(** ** The co-Eilenberg–Moore category, by duality / ** 通过对偶，协埃伦贝格–摩尔范畴 *)

Definition CoEilenbergMoore : Category :=
  (@EilenbergMoore (C^op) (W^op) H)^op.

(**
The hom-sets of the co-Eilenberg–Moore category are definitionally the
    algebra homomorphisms of the opposite monad, source and target
    swapped.

--------
共艾伦伯格–摩尔范畴的同态集合在定义上是对偶单子的代数同态，源对象和目标对象互换。
*)

Lemma coeilenberg_moore_hom (x y : CoEilenbergMoore) :
  (x ~{CoEilenbergMoore}~> y) =
  @TAlgebraHom (C^op) (W^op) H ``y ``x (projT2 y) (projT2 x).
Proof. reflexivity. Qed.

(**
** The covariant category of W-coalgebras

    Mirrors Monad/Eilenberg/Moore.v: objects are pairs of a carrier and a
    coalgebra on it, morphisms are coalgebra homomorphisms compared on
    their underlying arrows, and identities and composition are inherited
    from C.  The composition obligation pastes the two commuting squares,
    dually to the corresponding obligation there.

--------
** W-余代数的协变范畴

    对应于 Monad/Eilenberg/Moore.v：对象是一个承载对象及其上的一个余代数的对，态射是依据其底层箭头比较的余代数同态，恒等态射和复合态射从 C 继承。复合义务将两个交换图拼接起来，与那里对应的义务对偶。
*)

Program Definition WCoalgebras : Category := {|
  obj     := ∃ a : C, @WCoalgebra C W H a;
  hom     := fun x y => @WCoalgebraHom C W H ``x ``y (projT2 x) (projT2 y);
  homset  := fun _ _ => {| equiv := fun f g => w_coalg_hom[f] ≈ w_coalg_hom[g] |};
  id      := fun _ => {| w_coalg_hom := id |};
  compose := fun _ _ _ f g => {| w_coalg_hom := w_coalg_hom[f] ∘ w_coalg_hom[g] |}
|}.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite w_coalg_hom_commutes.
  rewrite <- comp_assoc.
  rewrite w_coalg_hom_commutes.
  now rewrite comp_assoc.
Qed.

(**
** The isomorphism of categories, in Cat

    Both functors keep the carrier and the underlying arrow fixed and
    convert the packaging; on hom-setoids they are the identity.  The two
    round trips are witnessed by natural isomorphisms whose components
    have identity underlying arrows.

--------
** 范畴的同构，在 Cat 中

两个函子都保持载体和底层箭头不变，并转换包装；在同态集合上它们是恒等映射。两次往返由自然同构所证明，其分量具有恒等的底层箭头。
*)

#[local] Obligation Tactic := program_simpl.

Program Definition WCoalgebras_to_CoEM : WCoalgebras ⟶ CoEilenbergMoore := {|
  fobj := fun x => (``x; WCoalgebra_to_TAlgebra (projT2 x));
  fmap := fun x y f => WCoalgebraHom_to_TAlgebraHom f
|}.
Next Obligation. proper. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

Program Definition CoEM_to_WCoalgebras : CoEilenbergMoore ⟶ WCoalgebras := {|
  fobj := fun x => (``x; TAlgebra_to_WCoalgebra (projT2 x));
  fmap := fun x y f => TAlgebraHom_to_WCoalgebraHom f
|}.
Next Obligation. proper. Qed.
Next Obligation. reflexivity. Qed.
Next Obligation. reflexivity. Qed.

(*
The two round trips fix the carrier and the costructure map on the
   nose; only the record packaging is rebuilt.  Each component of the two
   natural isomorphisms is therefore carried by an identity arrow.

--------
这两个往返将载体和成本构图固定在机头上；只有记录的打包被重建。因此，两个自然同构的每个组成部分都由一个恒等箭头承载。
*)

Program Definition coem_roundtrip (x : CoEilenbergMoore) :
  WCoalgebras_to_CoEM (CoEM_to_WCoalgebras x) ≅[CoEilenbergMoore] x := {|
  to   := {| t_alg_hom := id |};
  from := {| t_alg_hom := id |}
|}.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.

Program Definition wcoalgebras_roundtrip (x : WCoalgebras) :
  CoEM_to_WCoalgebras (WCoalgebras_to_CoEM x) ≅[WCoalgebras] x := {|
  to   := {| w_coalg_hom := id |};
  from := {| w_coalg_hom := id |}
|}.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.
Next Obligation. cat. Qed.

Lemma WCoalgebras_to_CoEM_inverse :
  WCoalgebras_to_CoEM ◯ CoEM_to_WCoalgebras ≈ Id[CoEilenbergMoore].
Proof.
  exists coem_roundtrip.
  intros x y f; cbn; cat.
Qed.

Lemma CoEM_to_WCoalgebras_inverse :
  CoEM_to_WCoalgebras ◯ WCoalgebras_to_CoEM ≈ Id[WCoalgebras].
Proof.
  exists wcoalgebras_roundtrip.
  intros x y f; cbn; cat.
Qed.

Definition WCoalgebras_CoEilenbergMoore_Iso :
  WCoalgebras ≅[Cat] CoEilenbergMoore :=
  @Build_Isomorphism Cat WCoalgebras CoEilenbergMoore
    WCoalgebras_to_CoEM CoEM_to_WCoalgebras
    WCoalgebras_to_CoEM_inverse CoEM_to_WCoalgebras_inverse.

End CoEilenbergMoore.
