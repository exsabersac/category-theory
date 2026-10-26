Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The hom-functor Hom(-,-) : C^op ∏ C ⟶ Sets.  / hom 函子 Hom(-,-) ：C^op ∏ C ⟶ 集合。*)

(*
nLab: https://ncatlab.org/nlab/show/hom-functor
   Wikipedia: https://en.wikipedia.org/wiki/Hom_functor

   For a (locally small) category C, the hom-functor sends a pair of objects
   (a, b) to the hom-set hom[C] a b, regarded as a setoid object of Sets. On a
   morphism of C^op ∏ C — that is, a pair (f, g) with f : a' ~{C}~> a (an arrow
   a ~{C^op}~> a') and g : b ~{C}~> b' — it sends an arrow q : a ~> b to the
   composite g ∘ q ∘ f : a' ~> b', i.e. pre-compose with f and post-compose
   with g. The bifunctor is therefore contravariant in its first argument and
   covariant in its second; equivalently it is the identity profunctor on C.

   Fixing one argument yields the two partial hom-functors: the covariant
   Hom(a, -) : C ⟶ Sets (acting by post-composition) and the contravariant
   Hom(-, b) : C^op ⟶ Sets (acting by pre-composition). The curried form
   Curried_Hom : C^op ⟶ [C, Sets] packages the covariant family, and as a
   full and faithful embedding it is the Yoneda embedding (Yoneda_Full and
   Yoneda_Faithful below); this is the basis of representability, developed in
   Functor/Representable.v. Since hom-sets here are setoids, Hom lands in Sets,
   the category of setoids. 

--------
nLab: https://ncatlab.org/nlab/show/hom-functor
   Wikipedia: https://en.wikipedia.org/wiki/Hom_functor

   对（局部小）范畴 C，hom 函子把对象对 (a, b) 送到 hom 集 hom[C] a b，视为 Sets 的
   setoid 对象。对 C^op ∏ C 的态射——即对 (f, g)，f : a' ~{C}~> a（箭头 a ~{C^op}~> a'）
   且 g : b ~{C}~> b'——它把箭头 q : a ~> b 送到复合 g ∘ q ∘ f : a' ~> b'，即前复合 f、
   后复合 g。故双函子在第一变元反变、第二变元共变；等价地是 C 上的恒等双函子。

   固定一变元得到两个偏 hom 函子：共变 Hom(a, -) : C ⟶ Sets（后复合作用）与反变
   Hom(-, b) : C^op ⟶ Sets（前复合作用）。curry 形式 Curried_Hom : C^op ⟶ [C, Sets]
   打包共变族，作为满忠实嵌入即 Yoneda 嵌入（下文 Yoneda_Full 与 Yoneda_Faithful）；
   这是可表性的基础，见 Functor/Representable.v。因此处 hom 集是 setoid，Hom 落在
   setoid 范畴 Sets。 
*)

(*
Bifunctors can be curried:

  C × D ⟶ E --> C ⟶ [D, E] ~~~ (C, D) → E --> C → D → E

  Where ~~~ should be read as “Morally equivalent to”.

  Note: We do not need to define Bifunctors as a separate class, since they
  can be derived from functors mapping to a category of functors. So in the
  following two definitions, [P] is effectively our bifunctor.

  The trick to [bimap] is that both the [Functor] instances we need (for
  [fmap] and [fmap1]), and the [Natural] instance, can be found in the
  category of functors we're mapping to by applying [P]. 

--------
双函子可以柯里化：

 C × D ⟶ E --> C ⟶ [D, E] ~~~ (C, D) → E --> C → D → E

 其中~~~应理解为“道德上等同于”。 

注意：我们不需要将 Bifunctor 定义为单独的类，因为它们
 可以从映射到函子类别的函子中导出。 所以在
 根据两个定义，[P] 实际上是我们的双函子。 

[bimap] 的技巧是我们需要的两个 [Functor] 实例（对于
 [fmap] 和 [fmap1]）以及 [Natural] 实例可以在
 我们通过应用 [P] 映射到的函子类别。 
*)

(*
   【Hom / Curried_Hom 定义展开】/ Definition walkthrough
   （口吻对齐 Theory/Functor.v @ c826572；受众：Coq 小白 + 范畴论小白的 Haskell 程序员）

   1) 这是什么 / What this is
      Hom : C^op ∏ C ⟶ Sets 把对象对 (a,b) 送到 Hom-集（此处为 setoid），
      把态射对 (f,g) 作用为 q ↦ g ∘ q ∘ f（前复合 f、后复合 g）。
      Hom sends (a,b) to the Hom-setoid and (f,g) to pre/post-compose.
      Haskell 对照：没有直接的标准库对应；可想成「把箭头当值」的 bifunctor，
      第一变元反变、第二变元共变。范畴版落在 Sets（setoid），相等是 ≈。
      Think: bifunctor on arrows-as-values; lands in Sets; equality is ≈.

   2) 关键字段 / Key fields of the Program Definition
      - fobj (a,b) = {| carrier := a ~> b; is_setoid := homset |}
      - fmap (f,g) = λ q. snd(f,g) ∘ q ∘ fst(f,g)
      Curried_Hom : C^op ⟶ [C, Sets] 是 curry 形式，即 Yoneda 嵌入的载体。
      Curried_Hom is the curried form (carrier of the Yoneda embedding).

   3) ≈ / Proper
      Hom 的态射是 Sets 中的函数，须尊重 ≈（Program 会生成义务）。
      Morphisms in Sets must respect ≈ (Program generates obligations).

   阅读顺序：Hom 双函子 → Curried_Hom → 后文 Yoneda_Full/Faithful。
   Reading order: Hom bifunctor → Curried_Hom → Yoneda facts below.
*)

Program Definition Hom `(C : Category) : C^op ∏ C ⟶ Sets := {|
  fobj := fun p => {| carrier   := @hom C (fst p) (snd p)
                    ; is_setoid := @homset (C) (fst p) (snd p) |};
  fmap := fun x y (f : x ~{C^op ∏ C}~> y) =>
            (*
g ↦ snd f ∘ g ∘ fst f: post-compose with the C-component
               (covariant in the second argument), pre-compose with the
               C^op-component (contravariant in the first). 

--------
g ↦ snd f ∘ g ∘ fst f：使用 C 组件进行后期合成
 （第二个参数中的协变），预先组合
 C^op-分量（第一个逆变）。 
*)
            {| morphism := fun g => snd f ∘ g ∘ fst f |}
|}.
Next Obligation. now rewrite !comp_assoc. Qed.

Program Definition Curried_Hom `(C : Category) : C^op ⟶ [C, Sets] := {|
  fobj := fun x => {|
    fobj := fun y => {| carrier := @hom C x y
                      ; is_setoid := @homset C x y |};
    fmap := fun y z (f : y ~{C}~> z) =>
              {| morphism := fun (g : x ~{C}~> y) =>
                               (f ∘ g) : x ~{C}~> z |}
  |};
  fmap := fun x y (f : x ~{C^op}~> y) => {|
    transform := fun _ => {| morphism := fun g => g ∘ op f |}
  |}
|}.
Next Obligation.
  simpl; intros.
  unfold op.
  apply comp_assoc.
Qed.

Coercion Curried_Hom : Category >-> Functor.

Notation "[Hom A , ─]" := (@Curried_Hom _ A) : functor_scope.

(*
Faithfulness of the Yoneda embedding: if f and g (arrows of C^op) induce
   the same natural transformation [Hom _,─] ⟹ [Hom _,─], then evaluating that
   transformation at the identity already forces f ≈ g. 

--------
米田嵌入的忠实度：如果 f 和 g（C^op 的箭头）归纳
 相同的自然变换 [Hom _,─] ⟹ [Hom _,─]，然后评估
 恒等式的变换已经迫使 f ≈ g。 
*)
#[export] Instance Yoneda_Faithful (C : Category) : Faithful (Curried_Hom C).
Proof.
  constructor.
  intros c c' f g same_nat_iso.
  simpl in same_nat_iso.
  specialize same_nat_iso with c id. now rewrite 2 id_left in same_nat_iso.
Qed.

(*
Fullness of the Yoneda embedding: every natural transformation between hom-
   functors arises from a morphism, recovered as its component at the identity
   (the [prefmap] field, fun c d f => f c id). 

--------
米田嵌入的完整性：家庭之间的每一次自然转变
 函子源自态射，在恒等式上恢复为它的组成部分
 （[prefmap] 字段，fun c d f => f c id）。 
*)
#[export] Instance Yoneda_Full (C : Category) : Full (Curried_Hom C).
Proof.
  unshelve econstructor; simpl in *.
  - exact (fun c d f => f c id).
  - abstract(intros x y [Ftrans Fnat ?] c f; simpl in *;
    unfold op;
    now rewrite Fnat, id_right).
Defined.

(*
The fully-faithful Yoneda bijection on hom-sets: full + faithful means
   fmap[Curried_Hom C] is, in Sets, an isomorphism between (d ~> c) = (c ~{C^op}~> d)
   and the natural transformations [Hom c,─] ⟹ [Hom d,─] (here fobj[C] is the
   coercion of C through Curried_Hom). 

--------
hom-sets 上完全忠实的米田双射：完全 + 忠实的意思
 fmap[Curried_Hom C] 在集合中是 (d ~> c) = (c ~{C^op}~> d) 之间的同构
 以及自然变换 [Hom c,─] ⟹ [Hom d,─] （这里 fobj[C] 是
 通过 Curried_Hom 对 C 进行强制转换）。 
*)
Corollary Yoneda_Embedding' (C: Category) (c d : C) :
  @IsIsomorphism Sets {| carrier := hom d c |}
                 {| carrier := hom (fobj[C] c) (fobj[C] d) |}
                 {| morphism := @fmap _ _ (Curried_Hom C) c d;
                            proper_morphism := fmap_respects _ _ |}.
Proof.
  apply bijective_is_iso.
  - abstract(assert (H := Yoneda_Faithful C); constructor;
             intros x y eq; apply H; exact eq).
  - constructor. simpl.
    intro A; exists (@prefmap _ _ _ (Yoneda_Full C) _ _ A ).
    abstract(intros x f; unfold op;
             assert (M := @fmap_sur _ _ _ (Yoneda_Full C));
             specialize M with _ _ A; simpl in M;
             unfold op in M; apply M).
Defined.

(*
The opposite hom-functor Hom_C^op(-,-) : C ∏ C^op ⟶ Sets, presented two
   ways. CoHom_Alt is Hom on C^op precomposed with the factor-swap Swap; on the
   pair (a, b) both forms give the set hom[C^op] a b = hom[C] b a, so they are
   the same bifunctor (covariant in the first argument, contravariant in the
   second). 

--------
相反的 hom 函子 Hom_C^op(-,-) : C ∏ C^op ⟶ 集合，提出了两个
 方式。 CoHom_Alt 是 C^op 上的 Hom，与因子交换 Swap 预先组合； 于
 对 (a, b) 两种形式都给出集合 hom[C^op] a b = hom[C] b a，因此它们是
 相同的双函数（第一个参数是协变的，第二个参数是逆变的）
 第二）。 
*)
Program Definition CoHom_Alt `(C : Category) : C ∏ C^op ⟶ Sets :=
  Hom C ◯ Swap.

Program Definition CoHom `(C : Category) : C ∏ C^op ⟶ Sets := {|
  fobj := fun p => {| carrier   := @hom (C^op) (fst p) (snd p)
                    ; is_setoid := @homset (C^op) (fst p) (snd p) |};
  fmap := fun x y (f : x ~{C ∏ C^op}~> y) =>
    {| morphism := fun g => snd f ∘ g ∘ fst f |}
|}.
Next Obligation. now rewrite <- ! comp_assoc. Qed.

(*
The curried contravariant hom-functor: Curried_CoHom C c = [Hom ─,c] is the
   presheaf Hom(-, c) : C^op ⟶ Sets, obtained as the covariant Curried_Hom on
   C^op. This is the contravariant Yoneda embedding C ⟶ [C^op, Sets] used to
   present presheaves. 

--------
柯里化逆变 hom 函子：Curried_CoHom C c = [Hom ─,c] 是
 presheaf Hom(-, c) : C^op ⟶ 集合，作为协变 Curried_Hom 获得
 C^op。 这是逆变米田嵌入 C ⟶ [C^op, Sets] 用于
 目前预滑轮。 
*)
Definition Curried_CoHom `(C : Category) : C ⟶ [C^op, Sets] :=
  Curried_Hom C^op.

Notation "[Hom ─ , A ]" := (@Curried_CoHom _ A) : functor_scope.
