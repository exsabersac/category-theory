Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(** * 余单子：共变 API *)

(* nLab:      https://ncatlab.org/nlab/show/comonad
   Wikipedia: https://en.wikipedia.org/wiki/Monad_(category_theory)#Comonads

   范畴 C 上的余单子是配备余单位 ε : W ⟹ Id（此处 [extract]）与余乘法
   δ : W ⟹ W ○ W（此处 [duplicate]）的自函子 W : C ⟶ C，服从两条余单位律
   ε ∘ δ ≈ id 与 W ε ∘ δ ≈ id，以及余结合律 δ ∘ δ ≈ W δ ∘ δ（写 W ε、W δ 为
   分量的 fmap 像，各复合经适当 W 实例阅读）。

   Theory/Monad.v 定义 [Comonad := @Monad (C^op) (W^op)]：余单子恰是对偶范畴上的单子。
   因本库对偶使 C^op^op = C 由 reflexivity 成立，每条余单子定律就是对应单子定律把复合
   反向阅读——无需单独 record，此处也不引入。本文件提供该定义的共变读法：访问器
   [extract]、[duplicate] 与 [extend] 是 [ret]、[join] 与 [bind] 的定义性 op-读，
   下文每条定律是经 [exact] 运送的对应单子定律（至多差 ≈ 的对称，因 op-读以反向到达）。 *)

(* 余单子从何而来，以及用途为何

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
   单子结构化效应计算相同的意义上结构化依赖上下文的计算（Uustalu–Vene 2008）。 *)

(*
   本节说明单子、余单子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Existing Class Comonad.

Section ComonadAPI.

Context {C : Category} {W : C ⟶ C} {H : @Comonad C W}.

(** The counit ε : W ⟹ Id, componentwise: the op-read of [ret]. *)
Definition extract {x : C} : W x ~> x := @ret (C^op) (W^op) H x.

(** The comultiplication δ : W ⟹ W ○ W, componentwise: the op-read of
    [join]. *)
Definition duplicate {x : C} : W x ~> W (W x) := @join (C^op) (W^op) H x.

(** Co-Kleisli extension (cobind): the op-read of [bind], see
    [extend_op_bind] just below. *)
Definition extend {x y : C} (f : W x ~> y) : W x ~> W y :=
  fmap[W] f ∘ duplicate.

(** [extend] agrees definitionally with the [bind] of the opposite monad. *)
Lemma extend_op_bind {x y : C} (f : W x ~> y) :
  extend f ≈ @bind (C^op) (W^op) H y x f.
Proof. reflexivity. Qed.

(** Naturality of the counit — ε is a natural transformation W ⟹ Id.
    Op-read of [fmap_ret]. *)
Lemma extract_natural {x y : C} (f : x ~> y) :
  f ∘ extract ≈ extract ∘ fmap[W] f.
Proof. exact (@fmap_ret (C^op) (W^op) H y x f). Qed.

(** Naturality of the comultiplication — δ is a natural transformation
    W ⟹ W ○ W.  Op-read of [join_fmap_fmap]. *)
Lemma duplicate_natural {x y : C} (f : x ~> y) :
  fmap[W] (fmap[W] f) ∘ duplicate ≈ duplicate ∘ fmap[W] f.
Proof. exact (@join_fmap_fmap (C^op) (W^op) H y x f). Qed.

(** Counit law ε_W ∘ δ ≈ id: op-read of the right unit law [join_ret]. *)
Lemma extract_duplicate {x : C} : extract ∘ duplicate ≈ id[W x].
Proof. exact (@join_ret (C^op) (W^op) H x). Qed.

(** Counit law W ε ∘ δ ≈ id: op-read of the left unit law [join_fmap_ret]. *)
Lemma fmap_extract_duplicate {x : C} : fmap[W] extract ∘ duplicate ≈ id[W x].
Proof. exact (@join_fmap_ret (C^op) (W^op) H x). Qed.

(** Coassociativity δ_W ∘ δ ≈ W δ ∘ δ: op-read of the associativity law
    [join_fmap_join], which arrives in the symmetric orientation. *)
Lemma duplicate_duplicate {x : C} :
  duplicate ∘ @duplicate x ≈ fmap[W] duplicate ∘ @duplicate x.
Proof.
  symmetry.
  exact (@join_fmap_join (C^op) (W^op) H x).
Qed.

(*
   本节说明单子、余单子、Kleisli相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
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

(** [duplicate] is the extension of the identity, and [fmap] factors through
    [extend]: the Kleisli-style and functorial presentations agree. *)

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

(** [extend] respects ≈ in its morphism argument, so it can be rewritten
    under.  (Declared outside the section so the instance is exported with
    fully general arguments.) *)
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
