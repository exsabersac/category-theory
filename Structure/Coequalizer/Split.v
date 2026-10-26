Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Coequalizer.

Generalizable All Variables.

(* * * Split coequalizers are absolute / * * 分裂的共同等化器是绝对的 *)

(*
 nLab:      https://ncatlab.org/nlab/show/split+coequalizer
 Wikipedia: https://en.wikipedia.org/wiki/Coequaliser

 A split coequalizer of a parallel pair f, g : x ~> y is a coforking map
 e : y ~> q (law 1: e ∘ f ≈ e ∘ g) equipped with a section s : q ~> y of
 e (law 2: e ∘ s ≈ id) and a section t : y ~> x of f (law 3: f ∘ t ≈ id)
 such that the idempotent s ∘ e on y is computed by the pair through t
 (law 4: g ∘ t ≈ s ∘ e).

 The four equations force e to be a coequalizer of f and g
 ([split_coequalizer_is_coequalizer]): a coforking map h : y ~> z
 descends through e as h ∘ s, since

 (h ∘ s) ∘ e ≈ h ∘ (g ∘ t) ≈ (h ∘ f) ∘ t ≈ h,

 and law 2 pins the descent down uniquely.

 Because the definition is purely equational — no quantification over
 the ambient category — every functor carries split coequalizers to
 split coequalizers ([functor_preserves_split]), hence to coequalizers
 ([split_coequalizer_preserved]).  Colimits preserved by all functors in
 this way are called *absolute* (Paré, “On absolute colimits”, 1971;
 nLab: absolute colimit), and split coequalizers are the archetypal
 example.  They are the engine of Beck's monadicity theorem, where the
 canonical presentation of an algebra by free algebras is a split
 coequalizer after applying the forgetful functor.

 The predicate is Structure/Coequalizer/Absolute.v's
 [AbsoluteCoequalizer] (#477), Mac Lane's §VI.6 definition, where
 [split_coequalizer_absolute] reads the corollary below as
 absoluteness; the cone-level reading of absolute colimits in general
 is Structure/Limit/Absolute.v's [AbsoluteColimitCocone].

 The condition on the pair alone that t witnesses, Beck's contractible
 pair, is Structure/Coequalizer/Contractible.v's [ContractiblePair]
 (#480): a pair has a split coequalizer exactly when it is contractible
 and has a coequalizer. 

 --------
 nLab：       https://ncatlab.org/nlab/show/split+coequalizer
 Wikipedia：  https://en.wikipedia.org/wiki/Coequaliser

 平行对 f, g : x ~> y 的拆分共等化器（split coequalizer）是一个共岔映射
 e : y ~> q（定律1：e ∘ f ≈ e ∘ g），配备一个 e 的截面 s : q ~> y
 （定律2：e ∘ s ≈ id）和 f 的截面 t : y ~> x（定律3：f ∘ t ≈ id），
 使得 y 上的幂等映射 s ∘ e 可以通过 t 由该对计算得到（定律4：g ∘ t ≈ s ∘ e）。

 这四个方程强制 e 成为 f 和 g 的共等化器（[split_coequalizer_is_coequalizer]）：任一共岔映射 h : y ~> z
 都可以通过 e 下传为 h ∘ s，因为

 (h ∘ s) ∘ e ≈ h ∘ (g ∘ t) ≈ (h ∘ f) ∘ t ≈ h,

 并且定律2确保该下传是唯一确定的。因为这个定义是纯粹的方程式定义——没有对环境范畴的量化——每个函子都会将拆分的余等化器映射为拆分的余等化器（[functor_preserves_split]），因此也会映射为余等化器（[split_coequalizer_preserved]）。所有函子以这种方式保持的余极限称为*绝对*（Paré, “On absolute colimits”, 1971；nLab: absolute colimit），而拆分的余等化器是典型的例子。它们是 Beck 的幺范性定理的引擎，其中通过自由代数对一个代数进行的典型表示在应用遗忘函子后是一个拆分的余等化器。谓词是 Structure/Coequalizer/Absolute.v 中的 [AbsoluteCoequalizer]（#477），这是 Mac Lane §VI.6 的定义，其中 [split_coequalizer_absolute] 将下面的推论读作绝对性；绝对余极限在锥层面的解读通常是 Structure/Limit/Absolute.v 中的 [AbsoluteColimitCocone]。

 关于该对的条件，仅由 t 证明，Beck 的可收缩对，是 Structure/Coequalizer/Contractible.v 中的 [ContractiblePair]（#480）：一个对恰好在它是可收缩且有余极限时才有分裂余极限。
*)

(* The equational data: a cofork e over the pair, a section s splitting e, and a section t of f mediating between s ∘ e and the pair. / 方程数据：在对上有一个余分叉 e，一个分裂 e 的截面 s，以及一个在 s ∘ e 与对之间起中介作用的 f 截面 t。 *)
Record SplitCoequalizer {C : Category} {x y : C} (f g : x ~> y) := {
  scoeq_obj : C;

  scoeq_e : y ~> scoeq_obj;   (* the coequalizing map / 共等化映射 *)
  scoeq_s : scoeq_obj ~> y;   (* section of e / e 的部分 *)
  scoeq_t : y ~> x;           (* section of f / f 的部分 *)

  scoeq_law1 : scoeq_e ∘ f ≈ scoeq_e ∘ g;       (* e coforks the pair / e 叉分这对 *)
  scoeq_law2 : scoeq_e ∘ scoeq_s ≈ id;          (* s splits e / s 分裂 e *)
  scoeq_law3 : f ∘ scoeq_t ≈ id;                (* t splits f / t 分裂 f *)
  scoeq_law4 : g ∘ scoeq_t ≈ scoeq_s ∘ scoeq_e  (* g ∘ t computes s ∘ e / g ∘ t 计算 s ∘ e *)
}.

Arguments scoeq_obj  {_ _ _ _ _} _.
Arguments scoeq_e    {_ _ _ _ _} _.
Arguments scoeq_s    {_ _ _ _ _} _.
Arguments scoeq_t    {_ _ _ _ _} _.
Arguments scoeq_law1 {_ _ _ _ _} _.
Arguments scoeq_law2 {_ _ _ _ _} _.
Arguments scoeq_law3 {_ _ _ _ _} _.
Arguments scoeq_law4 {_ _ _ _ _} _.

(* * ** A split coequalizer is a coequalizer / * ** 分裂余宿是余宿 *)

(* Descent through a split coequalizer: a coforking map h descends as h ∘ s, and the splitting of e makes this the only possibility. / 通过拆分的共等化子下降：共分叉映射 h 下降为 h ∘ s，而 e 的拆分使其成为唯一的可能性。 *)
Lemma split_coeq_desc {C : Category} {x y : C} {f g : x ~> y}
  (S : SplitCoequalizer f g) {z : C} (h : y ~> z) (Hh : h ∘ f ≈ h ∘ g) :
  ∃! u : scoeq_obj S ~> z, u ∘ scoeq_e S ≈ h.
Proof.
  unshelve eapply Build_Unique.
  - exact (h ∘ scoeq_s S).
  - (* (h ∘ s) ∘ e ≈ h: trade s ∘ e for g ∘ t (law 4), g for f under h (the cofork hypothesis), then cancel t against f (law 3) / (h ∘ s) ∘ e ≈ h：将 s ∘ e 交换为 g ∘ t（定律 4），在 h 下将 g 替换为 f（共叉假设），然后用 f 抵消 t（定律 3） *)
    rewrite <- comp_assoc.
    rewrite <- (scoeq_law4 S).
    rewrite comp_assoc.
    rewrite <- Hh.
    rewrite <- comp_assoc.
    rewrite (scoeq_law3 S).
    apply id_right.
  - (* uniqueness: any v with v ∘ e ≈ h is v ∘ (e ∘ s) ≈ h ∘ s by law 2 / 唯一性：根据定律 2，任何满足 v ∘ e ≈ h 的 v 都有 v ∘ (e ∘ s) ≈ h ∘ s *)
    intros v Hv.
    rewrite <- Hv.
    rewrite <- comp_assoc.
    rewrite (scoeq_law2 S).
    apply id_right.
Qed.

(* The elementary coequalizer carried by a split coequalizer. / 由分裂余等化子承载的初等余等化子。 *)
Theorem split_coequalizer_is_coequalizer {C : Category} {x y : C}
  (f g : x ~> y) (S : SplitCoequalizer f g) :
  IsCoequalizer f g (scoeq_obj S) (scoeq_e S).
Proof.
  exact {| cofork    := scoeq_law1 S
         ; coeq_desc := fun z h Hh => split_coeq_desc S h Hh |}.
Defined.

(* * ** Absoluteness: every functor preserves split coequalizers / * ** 绝对性：每个函子保持分裂余等化器 *)

(*
 Push each datum through fmap; each law follows from the corresponding
 law in the source by functoriality.  The proof ends with [Defined] so
 that the transported data ([F (scoeq_obj S)], [fmap (scoeq_e S)], ...)
 remain visible to conversion in the corollary below.

 The universe binders of this theorem and of the corollary below are
 written out (#477) so that the target's hom level may sit ABOVE the
 source's, as [Functor] itself permits.  Left unannotated, minimization
 identified the two hom levels, and a target with strictly larger
 hom-sets was refused (“Cannot enforce xh = ch because ch < xh”); the
 same proof compiles with the bound strict, so the identification was
 an artifact of the binders, not of the argument.  It mattered once
 absoluteness quantified over every target category:
 Structure/Coequalizer/Absolute.v. 

 --------
 将每个数据通过 fmap 推送；每条定律都由源中的相应定律通过函子性推出。证明以 [Defined] 结束，以便传输的数据（[F (scoeq_obj S)]、[fmap (scoeq_e S)]、……）在下面的推论中仍然对转换可见。

 本定理和下面推论的宇宙绑定器已写出 (#477)，以便目标的同构层级可以高于源的层级，如 [Functor] 本身所允许的。如果不加注释，最小化会识别出两个同构层级相同，而具有严格更大同构集的目标将被拒绝（“Cannot enforce xh = ch because ch < xh”）；相同的证明在绑定为严格时能够编译，因此这种识别是绑定器的结果，而非论证本身造成的。当绝对性量化每个目标范畴时，这点非常重要：Structure/Coequalizer/Absolute.v。
*)
Theorem functor_preserves_split@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D)
  {x y : C} (f g : x ~> y) :
  SplitCoequalizer f g → SplitCoequalizer (fmap[F] f) (fmap[F] g).
Proof.
  intros S.
  unshelve refine
    {| scoeq_obj := F (scoeq_obj S)
     ; scoeq_e   := fmap[F] (scoeq_e S)
     ; scoeq_s   := fmap[F] (scoeq_s S)
     ; scoeq_t   := fmap[F] (scoeq_t S) |}.
  - (* law 1 *)
    rewrite <- !fmap_comp.
    now rewrite (scoeq_law1 S).
  - (* law 2 *)
    rewrite <- fmap_comp.
    rewrite (scoeq_law2 S).
    apply fmap_id.
  - (* law 3 *)
    rewrite <- fmap_comp.
    rewrite (scoeq_law3 S).
    apply fmap_id.
  - (* law 4 *)
    rewrite <- !fmap_comp.
    now rewrite (scoeq_law4 S).
Defined.

(*
 The headline: the coequalizer of a split pair is preserved, in the
 elementary [IsCoequalizer] sense, by an arbitrary functor. 

 --------
 标题：一个拆分对的共余子在初等 [IsCoequalizer] 意义下被任意函子保持。
*)
Corollary split_coequalizer_preserved@{co ch do dh +}
  {C : Category@{co ch ch}} {D : Category@{do dh dh}} (F : C ⟶ D)
  {x y : C} (f g : x ~> y) (S : SplitCoequalizer f g) :
  IsCoequalizer (fmap[F] f) (fmap[F] g)
    (F (scoeq_obj S)) (fmap[F] (scoeq_e S)).
Proof.
  exact (split_coequalizer_is_coequalizer
           (fmap[F] f) (fmap[F] g) (functor_preserves_split F f g S)).
Defined.
