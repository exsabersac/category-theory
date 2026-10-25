Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(** * Comonads: the covariant API / * 余单子：协变 API *)

(*
nLab:      https://ncatlab.org/nlab/show/comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   A comonad on a category C is an endofunctor W : C ⟶ C equipped with a
   counit ε : W ⟹ Id (here [extract]) and a comultiplication δ : W ⟹ W ○ W
   (here [duplicate]), subject to the two counit laws ε ∘ δ ≈ id and
   W ε ∘ δ ≈ id, and to coassociativity δ ∘ δ ≈ W δ ∘ δ (writing W ε and W δ
   for the fmap image of a component, and reading each composite through the
   appropriate instance of W).

   Theory/Monad.v defines [Comonad := @Monad (C^op) (W^op)]: a comonad is
   exactly a monad on the opposite category.  Because duality is built into
   this library so that C^op^op = C holds by reflexivity, each comonad law IS
   the corresponding monad law with its composites read backwards — no
   separate record is needed, and none is introduced here.  This file
   provides the covariant reading of that definition: the accessors
   [extract], [duplicate] and [extend] are definitional op-reads of [ret],
   [join] and [bind], and every law below is the corresponding monad law
   transported by [exact] (at most up to symmetry of ≈, where the op-read
   arrives in the reversed orientation).

--------
nLab:      https://ncatlab.org/nlab/show/comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   范畴 C 上的余单子是配备余单位 ε : W ⟹ Id（此处 [extract]）与余乘法
   δ : W ⟹ W ○ W（此处 [duplicate]）的自函子 W : C ⟶ C，服从两条余单位律
   ε ∘ δ ≈ id 与 W ε ∘ δ ≈ id，以及余结合律 δ ∘ δ ≈ W δ ∘ δ（写 W ε、W δ 为
   分量的 fmap 像，各复合经适当 W 实例阅读）。

   Theory/Monad.v 定义 [Comonad := @Monad (C^op) (W^op)]：余单子恰是对偶范畴上的单子。
   因本库对偶使 C^op^op = C 由 reflexivity 成立，每条余单子定律就是对应单子定律把复合
   反向阅读——无需单独 record，此处也不引入。本文件提供该定义的共变读法：访问器
   [extract]、[duplicate] 与 [extend] 是 [ret]、[join] 与 [bind] 的定义性 op-读，
   下文每条定律是经 [exact] 运送的对应单子定律（至多差 ≈ 的对称，因 op-读以反向到达）。
*)

(*
Where comonads come from, and what they are for

   nLab:  https://ncatlab.org/nlab/show/comonad
   Paper: Eilenberg, Moore, "Adjoint functors and triples", Illinois
          Journal of Mathematics 9(3), 1965
   Paper: Uustalu, Vene, "Comonadic Notions of Computation", ENTCS 203(5),
          2008

   Three views of the same structure organize everything below: the
   algebraic, the categorical, and the computational.

   Algebraically, a comonad on C is a comonoid in the monoidal category
   of endofunctors of C, with composition as tensor and Id as unit:
   [duplicate] is the comultiplication, [extract] is the counit, and the
   laws below are the comonoid axioms and nothing more.  The reading
   generalizes to any 2-category E — a comonad on an object X is a
   comonoid in the hom-category E(X, X) — and this file is the case
   E = Cat.  The terminology has accumulated in layers: Godement
   introduced the monad-side notion in 1958 as the "standard
   construction"; Eilenberg and Moore wrote "triple" in 1965, whence the
   older synonym "cotriple" for comonads; and the now-standard name
   "monad" is due to Bénabou (1967).

   Categorically, comonads are the residue that an adjunction leaves on
   the codomain of its left adjoint.  Every adjunction F ⊣ U induces a
   comonad there — the endofunctor is F ◯ U, the counit is the
   adjunction counit ε : F ◯ U ⟹ Id, and the comultiplication is the
   whiskered unit F η U — an observation that goes back to Huber (1961)
   and is realized in this library as [Adjunction_Comonad] in
   Comonad/Duality.v.  Every comonad so arises, and in two canonical
   ways: the co-Kleisli and co-Eilenberg–Moore resolutions, obtained by
   duality in Comonad/Duality.v ([CoKleisli_Adjunction],
   [CoEM_Adjunction]) over the categories built in Comonad/CoKleisli.v
   and Comonad/Coalgebra.v.

   Computationally, a comonadic value is a value in an observable
   context.  Where a monadic value T x is a computation that may perform
   effects while producing an x, a value W x is an x situated in a
   context that can be read off and re-exposed: [extract] reads the
   value at the current context, [duplicate] re-exposes the whole
   context at every point of itself, and [extend] promotes a
   context-consuming observation W x ~> y to a context-preserving
   transformation W x ~> W y by running the observation everywhere.
   Comonads therefore structure context-dependent computation in the
   same sense that Moggi-style monads structure effectful computation
   (Uustalu–Vene 2008), and the coeffect calculi of Petricek, Orchard
   and Mycroft (ICFP 2014) make the duality a type discipline, tracking
   what a program requires from its context as effect systems track
   what it does to its surroundings.

   The applications follow the three views.  From the computational
   reading come the programming uses: dataflow, where general and causal
   stream functions are the co-Kleisli arrows of stream comonads
   (Uustalu–Vene, APLAS 2005; see Comonad/CoKleisli.v); cellular
   automata, where one step of the automaton is [extend] of the local
   rule over a zipper of cells (Piponi, 2006); spreadsheet-like
   recurrences, evaluated by a comonadic fixed point in which every cell
   observes its own context within the whole (Foner, Haskell Symposium
   2015); and user interfaces, where a comonad models the space of
   states of an application, [extract] renders the current one, and a
   paired monad moves through the space (Freeman, 2016).  From the
   algebraic reading, through its coalgebras, comes the connection to
   data access: the coalgebras of the store comonad are exactly the
   lawful lenses of functional programming (O'Connor, 2011; see
   Comonad/Coalgebra.v and Instance/Coq/Comonad/Store.v).  From the
   adjunction reading come the mathematical uses: in linear logic the
   exponential modality ! is a comonad whose co-Kleisli category
   interprets intuitionistic logic (Girard 1987; Seely 1989; see
   Comonad/CoKleisli.v), and in descent theory the descent data along a
   morphism are (co)algebras over the (co)monad of a base-change
   adjunction (Bénabou–Roubaud 1970), with the simplicial bar resolution
   of a comonad founding cotriple cohomology (Barr–Beck, Springer LNM
   80, 1969; see Comonad/Coalgebra.v).  The earliest use of comonads in
   programming semantics is Brookes–Geva's computational comonads (LMS
   Lecture Note Series 177, 1992); the first proposal to program with
   them in Haskell is Kieburtz (1999).

--------
余单子从何而来，以及用途为何

   nLab:  https://ncatlab.org/nlab/show/comonad
   Paper: Eilenberg, Moore, "Adjoint functors and triples", Illinois
          Journal of Mathematics 9(3), 1965
   Paper: Uustalu, Vene, "Comonadic Notions of Computation", ENTCS 203(5),
          2008

   同一结构的三种视角组织下文一切：代数的、范畴的与计算的。

   代数上，C 上的余单子是 C 的自函子幺半范畴中的余幺半群，以复合为张量、Id 为单位：
   [duplicate] 是余乘法，[extract] 是余单位，下文定律恰是余幺半群公理。该读法推广到
   任意 2-范畴 E——对象 X 上的余单子是 hom-范畴 E(X, X) 中的余幺半群——本文件是 E = Cat
   的情形。术语层层累积：Godement 1958 在单子侧引入「标准构造」；Eilenberg 与 Moore
   1965 写「triple」，故余单子有更老同义词「cotriple」；现标准名「monad」归功于
   Bénabou (1967)。

   范畴上，余单子是伴随在其左伴随陪域上留下的残渣。每个伴随 F ⊣ U 在彼处诱导余单子——
   自函子是 F ◯ U，余单位是伴随余单位 ε : F ◯ U ⟹ Id，余乘法是 whiskered 单位 F η U——
   该观察可追溯到 Huber (1961)，本库实现为 Comonad/Duality.v 的 [Adjunction_Comonad]。
   每个余单子都如此产生，且有两种典范方式：co-Kleisli 与 co-Eilenberg–Moore 分解，
   由 Comonad/Duality.v（[CoKleisli_Adjunction]、[CoEM_Adjunction]）对偶得到，范畴建于
   Comonad/CoKleisli.v 与 Comonad/Coalgebra.v。

   计算上，余单子值是可观察上下文中的值。单子值 T x 是可能产生效应并产出 x 的计算，
   而值 W x 是处于可读取并再暴露上下文中的 x：[extract] 读当前上下文处的值，
   [duplicate] 在自身每一点再暴露整个上下文，[extend] 把消耗上下文的观察 W x ~> y
   提升为保持上下文的变换 W x ~> W y（处处运行该观察）。因此余单子在与 Moggi 风格
   单子结构化效应计算相同的意义上结构化依赖上下文的计算（Uustalu–Vene 2008）。
*)

(*
[Comonad C W] is a Definition that unfolds to the class
   [@Monad (C^op) (W^op)], but typeclass resolution keys on the head constant
   of a goal and does not look through this unfolding.  Declaring [Comonad]
   an existing class lets a comonad witness in scope be found when the
   accessors below insert their implicit [Comonad] argument, mirroring how
   [ret] and [join] resolve their implicit [Monad] argument.  Goals headed by
   [Monad] are untouched: the two heads are distinct, so neither search space
   leaks into the other.

   The declaration is kept here, in the comonad API module, rather than beside
   the [Comonad] definition in Theory/Monad.v: this file is the canonical
   entry point for the comonad API, so any code wanting class behaviour for
   [Comonad] holes and [Context] binders imports it, and imposing library-wide
   class resolution on the bare definition is avoided.

--------
[Comonad C W] 是一个定义，它展开为类 [@Monad (C^op) (W^op)]，但类型类解析是基于目标的头部常量，并不会通过这种展开进行查找。声明 [Comonad] 为现有类可以让作用域中的 comonad 证明在下面访问器插入它们的隐式 [Comonad] 参数时被找到，这类似于 [ret] 和 [join] 如何解析它们的隐式 [Monad] 参数。以 [Monad] 开头的目标不受影响：两个头部是不同的，因此它们的搜索空间不会相互泄露。

该声明保存在这里，即 comonad API 模块中，而不是放在 Theory/Monad.v 中的 [Comonad] 定义旁边：该文件是 comonad API 的规范入口点，因此任何希望为 [Comonad] 空位和 [Context] 绑定器获取类行为的代码都会导入它，从而避免在裸定义上施加全库的类解析。
*)
Existing Class Comonad.

Section ComonadAPI.

Context {C : Category} {W : C ⟶ C} {H : @Comonad C W}.

(** The counit ε : W ⟹ Id, componentwise: the op-read of [ret]. / 余单位 ε : W ⟹ Id，按分量：[ret] 的对读。 *)
Definition extract {x : C} : W x ~> x := @ret (C^op) (W^op) H x.

(**
The comultiplication δ : W ⟹ W ○ W, componentwise: the op-read of
    [join].

--------
余乘 δ : W ⟹ W ○ W，逐分量：[join] 的操作读取。
*)
Definition duplicate {x : C} : W x ~> W (W x) := @join (C^op) (W^op) H x.

(**
Co-Kleisli extension (cobind): the op-read of [bind], see
    [extend_op_bind] just below.

--------
Co-Kleisli 扩展（cobind）：[bind] 的 op-read，请参见下面的 [extend_op_bind]。
*)
Definition extend {x y : C} (f : W x ~> y) : W x ~> W y :=
  fmap[W] f ∘ duplicate.

(** [extend] agrees definitionally with the [bind] of the opposite monad. / [extend] 在定义上同意对立单子的 [bind]。 *)
Lemma extend_op_bind {x y : C} (f : W x ~> y) :
  extend f ≈ @bind (C^op) (W^op) H y x f.
Proof. reflexivity. Qed.

(**
Naturality of the counit — ε is a natural transformation W ⟹ Id.
    Op-read of [fmap_ret].

--------
伴随余单位的自然性——ε 是一个从 W 到 Id 的自然变换。
[fmap_ret] 的 Op-read。
*)
Lemma extract_natural {x y : C} (f : x ~> y) :
  f ∘ extract ≈ extract ∘ fmap[W] f.
Proof. exact (@fmap_ret (C^op) (W^op) H y x f). Qed.

(**
Naturality of the comultiplication — δ is a natural transformation
    W ⟹ W ○ W.  Op-read of [join_fmap_fmap].

--------
余乘法的自然性 — δ 是一个自然变换 W ⟹ W ○ W。 [join_fmap_fmap] 的操作读取。
*)
Lemma duplicate_natural {x y : C} (f : x ~> y) :
  fmap[W] (fmap[W] f) ∘ duplicate ≈ duplicate ∘ fmap[W] f.
Proof. exact (@join_fmap_fmap (C^op) (W^op) H y x f). Qed.

(** Counit law ε_W ∘ δ ≈ id: op-read of the right unit law [join_ret]. / 右单位律的余单位律 ε_W ∘ δ ≈ id：右单位律的操作读取 [join_ret]。 *)
Lemma extract_duplicate {x : C} : extract ∘ duplicate ≈ id[W x].
Proof. exact (@join_ret (C^op) (W^op) H x). Qed.

(** Counit law W ε ∘ δ ≈ id: op-read of the left unit law [join_fmap_ret]. / 右单位律 W ε ∘ δ ≈ id：左单位律的操作读取 [join_fmap_ret]。 *)
Lemma fmap_extract_duplicate {x : C} : fmap[W] extract ∘ duplicate ≈ id[W x].
Proof. exact (@join_fmap_ret (C^op) (W^op) H x). Qed.

(**
Coassociativity δ_W ∘ δ ≈ W δ ∘ δ: op-read of the associativity law
    [join_fmap_join], which arrives in the symmetric orientation.

--------
余结合性 δ_W ∘ δ ≈ W δ ∘ δ：结合律的操作读取 [join_fmap_join]，以对称方向到达。
*)
Lemma duplicate_duplicate {x : C} :
  duplicate ∘ @duplicate x ≈ fmap[W] duplicate ∘ @duplicate x.
Proof.
  symmetry.
  exact (@join_fmap_join (C^op) (W^op) H x).
Qed.

(**
The co-Kleisli triple laws for [extend].  Together with [extract] these
    present the comonad in extension form, dually to the ret/bind
    presentation of a monad; Comonad/CoKleisli.v uses them to relate
    co-Kleisli composition to [extend].

--------
[extend] 的共-Kleisli 三重定律。连同 [extract]，它们一起呈现了扩展形式的余单子，与单子的 ret/bind 表述相对；Comonad/CoKleisli.v 使用它们来将共-Kleisli 组合与 [extend] 关联起来。
*)

Corollary extract_extend {x y : C} (f : W x ~> y) : extract ∘ extend f ≈ f.
Proof.
  unfold extend.
  rewrite comp_assoc.
  rewrite <- extract_natural.
  rewrite <- comp_assoc.
  rewrite extract_duplicate.
  cat.
Qed.

Corollary extend_extract {x : C} : extend extract ≈ id[W x].
Proof. exact fmap_extract_duplicate. Qed.

Corollary extend_comp {x y z : C} (f : W y ~> z) (g : W x ~> y) :
  extend f ∘ extend g ≈ extend (f ∘ extend g).
Proof.
  unfold extend.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite <- duplicate_duplicate.
  rewrite (comp_assoc (fmap[W] (fmap[W] g))).
  rewrite duplicate_natural.
  now rewrite !comp_assoc.
Qed.

(**
[duplicate] is the extension of the identity, and [fmap] factors through
    [extend]: the Kleisli-style and functorial presentations agree.

--------
[duplicate] 是恒等式的扩展，而 [fmap] 通过 [extend] 起作用：Kleisli 风格的表示与函子表示是一致的。
*)

Corollary extend_id_duplicate {x : C} : extend (id[W x]) ≈ duplicate.
Proof. unfold extend; cat. Qed.

Corollary fmap_extend_extract {x y : C} (f : x ~> y) :
  extend (f ∘ extract) ≈ fmap[W] f.
Proof.
  unfold extend.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite fmap_extract_duplicate.
  cat.
Qed.

End ComonadAPI.

(**
[extend] respects ≈ in its morphism argument, so it can be rewritten
    under.  (Declared outside the section so the instance is exported with
    fully general arguments.)

--------
[extend] 在其同态参数中尊重 ≈，因此它可以在下面重写。（在该部分之外声明，因此实例以完全通用的参数导出。）
*)
#[export] Instance extend_respects
  {C : Category} {W : C ⟶ C} {H : @Comonad C W} {x y} :
  Proper (equiv ==> equiv) (@extend C W H x y).
Proof.
  proper.
  unfold extend.
  now rewrites.
Qed.

Notation "extract[ W ]" := (@extract _ W _ _)
  (at level 9, format "extract[ W ]") : category_scope.
Notation "duplicate[ W ]" := (@duplicate _ W _ _)
  (at level 9, format "duplicate[ W ]") : category_scope.
Notation "extend[ W ]" := (@extend _ W _ _ _)
  (at level 9, format "extend[ W ]") : category_scope.
