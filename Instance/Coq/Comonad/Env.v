Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Comonad.Core.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(* * * The environment (coreader) comonad on COQ / * * COQ 上的环境（coreader）comonad *)

(*
 nLab:      https://ncatlab.org/nlab/show/coreader+comonad
 Wikipedia: https://en.wikipedia.org/wiki/Monad_(functional_programming)

 The environment comonad — also called the coreader, product, or (after
 Haskell's Control.Comonad.Env) Env comonad — is the endofunctor e × − on
 COQ, for a fixed type e of "environments", with

 extract   (e0, v) = v               (read the value, drop the context)
 duplicate (e0, v) = (e0, (e0, v))   (expose the context to the value)

 It is dual to the writer monad m × −: where writer requires a monoid
 structure on m to merge accumulated output, the environment comonad
 requires a comonoid structure on e to copy and discard the ambient
 context, and in the cartesian category COQ every type carries one
 canonically (the diagonal and the terminal map).  Morphisms W x ~> y of
 its co-Kleisli category (Comonad/CoKleisli.v) are exactly the functions
 e * x → y that consult an ambient environment.

 Following Theory/Monad.v's [Comonad := @Monad (C^op) (W^op)], the witness
 [Env_Comonad] below is literally a [Monad] on COQ^op; the covariant
 accessors of Comonad/Core.v then read [extract], [duplicate] and [extend]
 off it definitionally (the *_spec lemmas at the end hold by
 [reflexivity]).

 COQ's morphism equivalence is pointwise Leibniz equality, so every law
 here is proved by destructuring the pair argument and [reflexivity]: no
 functional extensionality — indeed no axiom of any kind — enters this
 file, and every definition below is closed under the global context. 

 --------
 nLab:       https://ncatlab.org/nlab/show/coreader+comonad 
 维基百科:  https://en.wikipedia.org/wiki/Monad_(functional_programming) 

 环境共单子——也叫做共读器、乘积，或（在 Haskell 的 Control.Comonad.Env 之后）Env 共单子——是在 COQ 上的自函子 e × −，对于固定类型 e 的“环境”，其定义为

 extract   (e0, v) = v               （读取值，丢弃上下文）
 duplicate (e0, v) = (e0, (e0, v))   （将上下文暴露给值）它与写入器单子 m × − 是对偶的：写入器需要在 m 上有一个幺半群结构来合并累积的输出，而环境余单子需要在 e 上有一个余幺半群结构来复制和丢弃环境上下文，并且在笛卡尔范畴 COQ 中，每种类型都有一个规范的结构（对角射影和终态映射）。其 co-Kleisli 范畴（Comonad/CoKleisli.v）中的态射 W x ~> y 恰好是那些查询环境 e * x → y 的函数。

 根据 Theory/Monad.v 中的 [Comonad := @Monad (C^op) (W^op)]，下面的见证 [Env_Comonad] 从字面上是 COQ^op 上的 [Monad]；Comonad/Core.v 的协变访问器然后从中定义性地读取 [extract]、[duplicate] 和 [extend]（*_spec 引理在最后由 [reflexivity] 成立）。COQ 的态射等价是逐点 Leibniz 相等，因此这里的每一条定律都是通过析构对参数来证明的，并且没有函数外延性 —— 事实上本文件中没有引入任何公理，并且下面的每个定义都在全局上下文下封闭。
*)

(*
 Coeffects, annotation, and the slice

 nLab:  https://ncatlab.org/nlab/show/coreader+comonad
 Paper: Petricek, Orchard, Mycroft, "Coeffects: a calculus of
 context-dependent computation", ICFP 2014

 The co-Kleisli reading e * x → y is the discipline of implicit
 parameters, also called dynamic scoping: a program consults a
 read-only ambient environment without threading it by hand.
 Haskell's Control.Comonad.Env documents exactly this chain of
 readings, (a -> e -> m) ~ (a, e) -> m ~ Env e a -> m.  In the
 coeffect calculi of Petricek, Orchard and Mycroft (ICFP 2014),
 dynamic scoping is a standard instance of a coeffect — a requirement
 a computation places on its context, tracked by the type system as
 effect systems track what a computation does to its surroundings.
 The environment comonad performs exactly the computations of the
 reader monad, co-Kleisli composition threading one environment to
 both arrows (Milewski, 2017); and the relation between the two is an
 adjunction, for on a cartesian closed category e × − is left adjoint
 to e ⇒ −, the composite e ⇒ (e × −) is the state monad, and the
 comonad the same adjunction induces is Store
 (Instance/Coq/Comonad/Store.v; Comonad/Duality.v,
 [Adjunction_Comonad]).

 An environment layer is also the canonical annotation device:
 [extract] drops the annotation and [duplicate] makes it observable
 to every consumer, so a structure can be labelled without being
 disturbed.  Annotating the nodes of a cofree-comonad syntax tree
 through an environment transformer layer is the standard
 application, and Haskell's free package ships precisely that
 composition.

 The coalgebras complete the picture.  A coalgebra structure on a
 carrier a for e × − is the same thing as a single morphism a → e,
 and the category of coalgebras is isomorphic to the slice category
 over e: to hold an e-annotation coherently is exactly to be an
 object over e (see Comonad/Coalgebra.v), and the slice projection is
 thereby a comonadic functor.  The comonoid remark of the header
 above also generalizes — whenever w is a comonoid in a monoidal
 category, w ⨂ − carries an analogous comonad structure, and when w
 is instead a monoid, w × − carries the writer monad.  The
 copy/discard vocabulary for categories with a comonoid supply is
 developed in Structure/Monoidal/CopyDiscard.v. 

 --------
 共效应、注解与切片

 nLab:   https://ncatlab.org/nlab/show/coreader+comonad
 论文: Petricek, Orchard, Mycroft, 《共效应：上下文依赖计算的演算》，ICFP 2014共Kleisli 的读取 e * x → y 是隐式参数的机制，也称为动态作用域：程序在不手动传递环境的情况下，查询一个只读的环境。Haskell 的 Control.Comonad.Env 正是记录了这一系列读取过程，(a -> e -> m) ~ (a, e) -> m ~ Env e a -> m。在 Petricek、Orchard 和 Mycroft（ICFP 2014）的共效应演算中，动态作用域是共效应的一个标准实例——即计算对其上下文提出的要求，由类型系统追踪，就像效果系统追踪计算对其环境的影响一样。环境余单子执行的计算恰好是读者单子的计算，Co-Kleisli 组合将同一个环境线程传递给两个箭头（Milewski, 2017）；两者之间的关系是一个伴随关系，因为在笛卡尔闭范畴上，e × − 是 e ⇒ − 的左伴随，复合 e ⇒ (e × −) 是状态单子，而相同伴随关系诱导的余单子是 Store（Instance/Coq/Comonad/Store.v; Comonad/Duality.v, [Adjunction_Comonad]）。环境层也是规范的注释设备：
 [extract] 会丢弃注释，而 [duplicate] 会使其对每个使用者可见，因此结构可以在不被干扰的情况下被标注。通过环境转换器层对 cofree-comonad 语法树的节点进行注释是标准的应用，而 Haskell 的 free 包正是提供了这种组合。余代数完善了这个图景。载体 a 上 e × − 的余代数结构与单个态射 a → e 相同，余代数的范畴与 e 上的切片范畴同构：以一致的方式保持一个 e 注解恰好就是成为 e 上的一个对象（参见 Comonad/Coalgebra.v），因此切片投影也是一个余单子范畴函子。上文标题中的余单子注释也可以推广——每当 w 是一个单体范畴中的余单子时，w ⨂ − 具有类似的余单子结构；而当 w 是一个幺半群时，w × − 具有写器单子。对于拥有余单子供应的范畴，复制/丢弃词汇在 Structure/Monoidal/CopyDiscard.v 中进行了开发。
*)

(** The action of e × − on morphisms: apply f under the environment. / e × − 在态射上的作用：在环境下应用 f。 *)
Definition env_map {e x y : Type} (f : x → y) (p : e * x) : e * y :=
  match p with (e0, v) => (e0, f v) end.

Lemma env_map_respects {e x y : Type} (f g : x → y) :
  (∀ v, f v = g v) → ∀ p : e * x, env_map f p = env_map g p.
Proof.
  intros Hfg [e0 v]; simpl.
  now rewrite Hfg.
Qed.

Lemma env_map_id {e x : Type} (p : e * x) : env_map (λ v : x, v) p = p.
Proof. now destruct p. Qed.

Lemma env_map_comp {e x y z : Type} (f : y → z) (g : x → y) (p : e * x) :
  env_map (λ v, f (g v)) p = env_map f (env_map g p).
Proof. now destruct p. Qed.

(** The environment endofunctor e × − on COQ. / COQ 上的环境余函子 e × −。 *)
Definition EnvF (e : Type) : Coq ⟶ Coq := @Build_Functor Coq Coq
  (λ x : Type, (e * x)%type)
  (λ (x y : Type) (f : x → y), @env_map e x y f)
  (λ x y : Type, @env_map_respects e x y)
  (λ x : Type, @env_map_id e x)
  (λ (x y z : Type) (f : y → z) (g : x → y), @env_map_comp e x y z f g).

(** The counit ε: project out the value. / 余单位 ε：投射出值。 *)
Definition env_extract {e x : Type} (p : e * x) : x := snd p.

(** The comultiplication δ: copy the environment into the payload. / 余乘 δ：将环境复制到有效载荷中。 *)
Definition env_duplicate {e x : Type} (p : e * x) : e * (e * x) :=
  match p with (e0, v) => (e0, (e0, v)) end.

(** Naturality of the counit — the op-read of [fmap_ret]. / 余单位的自然性——[fmap_ret] 的对操作读取。 *)
Lemma env_extract_natural {e x y : Type} (f : x → y) (p : e * x) :
  f (env_extract p) = env_extract (env_map f p).
Proof. now destruct p. Qed.

(** Coassociativity W δ ∘ δ ≈ δ ∘ δ — the op-read of [join_fmap_join]. / 共结合性 W δ ∘ δ ≈ δ ∘ δ — [join_fmap_join] 的操作读取。 *)
Lemma env_duplicate_coassoc {e x : Type} (p : e * x) :
  env_map env_duplicate (env_duplicate p) = env_duplicate (env_duplicate p).
Proof. now destruct p. Qed.

(** Counit law W ε ∘ δ ≈ id — the op-read of [join_fmap_ret]. / 协 counit 定律 W ε ∘ δ ≈ id — [join_fmap_ret] 的对读。 *)
Lemma env_fmap_extract_duplicate {e x : Type} (p : e * x) :
  env_map env_extract (env_duplicate p) = p.
Proof. now destruct p. Qed.

(** Counit law ε ∘ δ ≈ id — the op-read of [join_ret]. / 凑单位律 ε ∘ δ ≈ id — [join_ret] 的对读。 *)
Lemma env_extract_duplicate {e x : Type} (p : e * x) :
  env_extract (env_duplicate p) = p.
Proof. now destruct p. Qed.

(** Naturality of the comultiplication — the op-read of [join_fmap_fmap]. / 余乘法的自然性 — [join_fmap_fmap] 的 op-读取。 *)
Lemma env_duplicate_natural {e x y : Type} (f : x → y) (p : e * x) :
  env_map (env_map f) (env_duplicate p) = env_duplicate (env_map f p).
Proof. now destruct p. Qed.

(*
   * The comonad witness: per Theory/Monad.v, a comonad on COQ IS a monad on
   COQ^op, so the record is assembled with [Build_Monad] at (COQ^op,
   (EnvF e)^op) — [ret] is the counit and [join] the comultiplication, and
   each monad law is the corresponding lemma above, read through the
   opposite category's reversed composition. 

   --------
   * comonad 的证明：根据 Theory/Monad.v，COQ 上的 comonad 实际上是在 COQ^op 上的 monad，因此该记录是通过 [Build_Monad] 在 (COQ^op, (EnvF e)^op) 上组装的——[ret] 是余单位，[join] 是余乘法，并且每个 monad 定律对应上面的引理，通过对偶范畴的反向组合来理解。
*)
#[export] Instance Env_Comonad (e : Type) : @Comonad Coq (EnvF e) :=
  @Build_Monad (Coq^op) ((EnvF e)^op)
    (λ x : Type, @env_extract e x)                (* ret  = ε *)
    (λ x : Type, @env_duplicate e x)              (* join = δ *)
    (λ (x y : Type) (f : y → x), @env_extract_natural e y x f)
    (λ x : Type, @env_duplicate_coassoc e x)
    (λ x : Type, @env_fmap_extract_duplicate e x)
    (λ x : Type, @env_extract_duplicate e x)
    (λ (x y : Type) (f : y → x), @env_duplicate_natural e y x f).

(*
   * The covariant accessors of Comonad/Core.v compute on this witness
   exactly as promised: [extract] is [snd], [duplicate] copies the
   environment, and [extend f] runs f with the environment kept in scope. 

   --------
   * Comonad/Core.v 的协变访问器在此见证上正如所承诺的那样进行计算：[extract] 是 [snd]，[duplicate] 复制环境，而 [extend f] 在环境保持作用域的情况下运行 f。
*)

Lemma Env_extract_spec {e x : Type} (p : e * x) :
  extract[EnvF e] p = snd p.
Proof. reflexivity. Qed.

Lemma Env_duplicate_spec {e x : Type} (e0 : e) (v : x) :
  duplicate[EnvF e] (e0, v) = (e0, (e0, v)).
Proof. reflexivity. Qed.

Lemma Env_extend_spec {e x y : Type} (f : e * x → y) (e0 : e) (v : x) :
  extend[EnvF e] f (e0, v) = (e0, f (e0, v)).
Proof. reflexivity. Qed.
