Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.

Generalizable All Variables.

(** * Monad transformers.  / * Monad 变压器。*)

(*
nLab: https://ncatlab.org/nlab/show/monad+transformer
   Wikipedia: https://en.wikipedia.org/wiki/Monad_transformer

   A monad transformer sends a monad M on C to a new monad T M on C, together
   with a monad morphism lift : M ⟹ T M embedding the base monad into the
   transformed one. (nLab phrases this as a pointed endofunctor on the category
   of monads, whose point is exactly this lift; the Haskell [MonadTrans] class
   is the same data.)

   Being a monad morphism, lift must respect the unit and the Kleisli bind, the
   two laws recorded here as [lift_return] and [lift_bind]:

       lift ∘ ret              ≈ ret                               (1)
       lift ∘ (join ∘ fmap f)  ≈ join ∘ fmap (lift ∘ f) ∘ lift     (2)

   In the pointful Haskell phrasing these are

       lift . return    = return
       lift (m >>= f)   = lift m >>= (lift . f)

   recalling that bind f = join ∘ fmap f in the join/return presentation (see
   Theory/Monad.v). In (1) the right-hand ret is that of T M; in (2) the
   left-hand join/fmap are M's while the right-hand join/fmap are those of T M.
   Together they say lift commutes with the monadic structure, so that the
   semantics of an M-computation is preserved when it is lifted into the larger
   monad T M. Transformers are not in general commutative: T₁ (T₂ M) and
   T₂ (T₁ M) usually differ.

   CORRECTION (#468).  The class below carries [lift] as a family of arrows
   with no naturality field, and until #468 the tree had no record of monad
   morphisms against which to read "monad morphism" above.
   Monad/Morphism/Transformer.v proves the reading from the two laws:
   [lift_natural] derives the naturality, [transformer_hom] turns a
   transformer into a [MonadHom] M (T M) of Monad/Morphism.v, and
   [hom_transformer] turns one back.  The pointed endofunctor on the
   category of monads that nLab describes is not built. 

--------
nLab：https://ncatlab.org/nlab/show/monad+transformer
维基百科：https://en.wikipedia.org/wiki/Monad_transformer

一个单子变换子将类别 C 上的单子 M 发送到新的单子 T M 上的 C，同时提供一个单子态射 lift : M ⟹ T M，将基础单子嵌入到变换后的单子中。（nLab 将其描述为单子范畴上的一个有基点的自函子，其基点正是这个 lift；Haskell 的 [MonadTrans] 类是相同的数据。）

作为一个单子态射，lift 必须遵守单位和 Kleisli 绑定，这两个定律在此记录为 [lift_return] 和 [lift_bind]：

lift ∘ ret              ≈ ret                               (1)
       lift ∘ (join ∘ fmap f)  ≈ join ∘ fmap (lift ∘ f) ∘ lift     (2)

在有意义的 Haskell 表述中，这些是

lift . return    = return
       lift (m >>= f)   = lift m >>= (lift . f)

回想在 join/return 表述中 bind f = join ∘ fmap f（参见 Theory/Monad.v）。在 (1) 中，右侧的 ret 是 T M 的；在 (2) 中，左侧的 join/fmap 是 M 的，而右侧的 join/fmap 是 T M 的。它们一起说明 lift 与单子结构是交换的，因此当 M-计算被提升到更大的单子 T M 时，其语义得以保持。变换器通常不具交换性：T₁ (T₂ M) 和 T₂ (T₁ M) 通常是不同的。

更正 (#468)。下面的类携带 [lift] 作为箭头的族，没有自然性字段，而且在 #468 之前，该树没有关于“单子态射”可以参照的单子态射记录。Monad/Morphism/Transformer.v 从两个定律证明了该读取：[lift_natural] 推导出自然性，[transformer_hom] 将一个变换器转换为 Monad/Morphism.v 的 [MonadHom] M (T M)，而 [hom_transformer] 将其转换回。nLab 描述的单子范畴上的指向自函子尚未构建。 
*)

Section Transformer.

Context {C : Category}.
Context {M : C ⟶ C}.
Context `{@Monad C M}.
Context {T : (C ⟶ C) → (C ⟶ C)}.
Context `{@Monad C (T M)}.

Class MonadTransformer := {
  lift {a} : M a ~> T M a;

  lift_return {a} : lift ∘ @ret C M _ a ≈ ret;
  lift_bind {a b} (f : a ~> M b) :
    lift ∘ join ∘ fmap f ≈ join ∘ fmap (lift ∘ f) ∘ lift
}.

End Transformer.

Arguments MonadTransformer {_ _ _} T {_}.

(******************************************************************************
* Species 1: Identity transformations.
 *****************************************************************************

--------
* 物种1：同一性变换。
 *****************************************************************************
*)

(*
The identity transformer leaves the monad untouched: IdentityT M is M again,
   with the same unit and multiplication, and lift is the identity morphism.
   The two transformer laws hold trivially, so this is the unit of transformer
   stacking. 

--------
身份转换器保持 monad 不变：IdentityTM M 又是 M，
 具有相同的单位和乘法，而 lift 是恒等态射。 
这两个变压器定律基本成立，所以这是变压器的单位
 堆叠。 
*)

Program Definition IdentityT {C : Category} (M : C ⟶ C) : C ⟶ C := {|
  fobj := fobj[M];
  fmap := fun _ _ => fmap[M]
|}.
Next Obligation. apply fmap_comp. Qed.

Program Definition IdentityT_Monad {C : Category} (M : C ⟶ C) `{@Monad C M} :
  @Monad C (@IdentityT C M) := {|
  ret  := fun _ => ret[M];
  join := fun _ => join[M]
|}.
Next Obligation. destruct H; intuition. Qed.
Next Obligation. destruct H; intuition. Qed.
Next Obligation. destruct H; intuition. Qed.
Next Obligation. destruct H; intuition. Qed.
Next Obligation. destruct H; intuition. Qed.

#[export]
Program Instance IdentityT_MonadTransformer {C : Category} (M : C ⟶ C) `{@Monad C M} :
  @MonadTransformer C M _ (@IdentityT C) (IdentityT_Monad M) := {
  lift := fun _ => id
}.

(*
(******************************************************************************)
(* Free monad transformer *)
(******************************************************************************)

Inductive FreeF (F : Type → Type) (A B : Type) :=
  | PureF : A → FreeF F A B
  | JoinF : F B → FreeF F A B.

Inductive FreeT (F : Type → Type) (M : Type → Type) (A : Type) :=
  | mkFreeT : ∀ x, (x → FreeT F M A) → M (FreeF F A x) → FreeT F M A.

Import MonadLaws.

Class MonadTransformerLaws `{MonadLaws M} `{FunctorLaws F} := {
  _ : Monad (FreeT F M);
  _ : MonadLaws (FreeT F M)
}.

(******************************************************************************)
(* Algebraic monad transformer *)
(******************************************************************************)

(* Q: Are they traversable? *)

Inductive Alg (c f g : Type → Type) a :=
  | Const : c a → Alg c f g a
  | Unit  : f a → Alg c f g a
  | Prod  : f a * g a → Alg c f g a
  | Sum   : f a + g a → Alg c f g a.

(* Theorem: For all algebraic monads, we should be able to automatically
   derive prod from MonadCompose. *)

(* Program Instance Alg_Distributes (c t : Type → Type) : *)
(*   Monad_Distributes Alg c t. *)

(* Program Instance Alg_DistributesLaws (c t : Type → Type) : *)
(*   Monad_DistributesLaws Alg c t. *)

(******************************************************************************)
(* Monad transformer of a certain subclass of exponential monads *)
(******************************************************************************)

(* Q: Are they distributive? *)

(* M : Monad *)
(* C : Contravariant *)

(* M t = 1 *)
(* M t = t *)
(* M t = C t → t *)
(* M t = A t * B t *)
(* M t = A t + t (??) *)

(* Theorem: Does M have a monad instance for any contravariant functor C? *)

(* For monads M and L: T M L t = M (L t) *)

(* M (r → a) *)
(* r → M a *)

(* c → t            =>     c → L t *)
(* (t → c) → t     =>     (L t → c) → L t *)

(******************************************************************************)
(* Monad transformers of monads from adjunctions *)
(******************************************************************************)

(* F ⊣ U *)

(* U ∘ F    T L = U ∘ L ∘ F *)

(* ULFULF = id *)
(* ULLF → ULF : by join of L *)

(* MaybeT (State s) a =    StateT s Maybe a *)
(* s → s * L t   ‌    =    s → L (s * t) *)

(* Q : Is MaybeT (State s) a incorrect? *)

(* (ReaderT $ StateT $ ...) *)

(* T (t1 ∘ t2 ∘ t3 (l)) m *)

(* t1 ∘ t2 ∘ t3 ∘ tl (m ) *)
*)

(******************************************************************************
* Species 2: Constant mapping transformations.
 *****************************************************************************

--------
* 物种 2：恒定映射转换。
 *****************************************************************************
*)

(*
The constant transformer ignores its argument monad M and always yields the
   fixed monad K. K M is a monad whenever K is, but the construction fails to
   be a monad transformer: lift would have to provide a morphism M A ~> K A
   natural in A, and no such family exists for arbitrary unrelated K and M, as
   the [Fail]ing definition below witnesses. 

--------
常量变换器忽略它的参数 monad M 并且总是产生
 固定单子 K。只要 K 是，K M 就是一个单子，但构造失败
 是一个 monad 转换器： lift 必须提供态射 M A ~> K A
 自然在 A 中，并且对于任意不相关的 K 和 M 不存在这样的族，如
 [Fail]ing 的定义如下见证。 
*)

Program Definition ConstT {C : Category} (K M : C ⟶ C) : C ⟶ C := {|
  fobj := fobj[K];
  fmap := fun _ _ => fmap[K]
|}.
Next Obligation. apply fmap_comp. Qed.

Program Definition ConstT_Monad {C : Category} (K M : C ⟶ C) `{@Monad C K} :
  @Monad C (@ConstT C K M) := {|
  ret  := fun _ => ret[K];
  join := fun _ => join[K]
|}.
Next Obligation. apply H. Qed.
Next Obligation. apply H. Qed.
Next Obligation. apply H. Qed.
Next Obligation. apply H. Qed.
Next Obligation. apply H. Qed.

(*
This is not a valid monad transformer, since there cannot be a morphism
   [M A ~> K A]. 

--------
这不是一个有效的单子转换器，因为不可能存在态射
 [M A ~> K A]。 
*)
Fail Definition ConstT_MonadTransformer {C : Category} (K M : C ⟶ C)
        `{@Monad C K} `{@Monad C M} :
  @MonadTransformer C M _ (@ConstT C K) (ConstT_Monad K M) := {|
  lift := fun _ => _
|}.
