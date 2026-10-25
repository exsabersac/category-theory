Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Monad.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Naturality.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Functor.Strong.
Require Import Category.Natural.Transformation.Strong.

Generalizable All Variables.

(** Strong monads (monads whose functor carries a compatible strength)  / 强单子（函子具有兼容强度的单子）*)

(*
nLab:      https://ncatlab.org/nlab/show/strong+monad
   Wikipedia: https://en.wikipedia.org/wiki/Strong_monad

   A strong monad on a monoidal category (C, ⊗, I) is a monad (M, η, μ) whose
   underlying endofunctor M : C ⟶ C carries a (left) tensorial strength

     t = strength[M] : x ⨂ M y ~> M (x ⨂ y)          (left strength)

   — that is, M is a [StrongFunctor] (see Functor.Strong), so t already
   satisfies Kock's two coherence laws [strength_id_left] (w.r.t. the left
   unitor λ) and [strength_assoc] (w.r.t. the associator α) — and whose strength
   is *compatible with the monad structure* η and μ.  Following Kock (1972,
   "Strong functors and monoidal monads", Arch. Math. 23) and Moggi (1991,
   "Notions of computation and monads", Inf. & Comput. 93), the two
   compatibility conditions are, writing t = strength[M]:

     - η-compat ([strength_ret]):  t ∘ (id ⨂ η) ≈ η
                 at type  x ⨂ y ~> M (x ⨂ y)

     - μ-compat ([strength_join]): t ∘ (id ⨂ μ) ≈ μ ∘ M t ∘ t
                 at type  x ⨂ M (M y) ~> M (x ⨂ y)

   In words: pulling η out of the right factor agrees with applying η to the
   whole tensor, and pulling μ out of the right factor agrees with sliding the
   strength through both M-layers and then multiplying.  These are exactly the
   diagrams that make t respect the monad structure in the tensor variable,
   which is what is needed to internalize Kleisli composition and to give the
   do-notation / `>>=` of a computational monad in the sense of Moggi: a strong
   monad's effects can be parameterized by an ambient context x.

   Deep structural fact (exploited below as a validation): the two compatibility
   laws are *precisely* the [Strong_Transform] squares for the monad's structure
   maps.  Since strength[Id] = id ([Id_StrongFunctor]), η-compat is exactly the
   strength-compatibility square of η : Id ⟹ M; and since strength[M ◯ M] =
   M t ∘ t ([Compose_StrongFunctor]), μ-compat is exactly the strength-
   compatibility square of μ : M ◯ M ⟹ M.  Thus a strong monad is exactly a
   monad whose unit and multiplication are *strong* natural transformations — a
   monoid object in the category of strong endofunctors and strong natural
   transformations.  We make this explicit at the end of the Tier-2 section
   ([ret_Strong_Transform], [join_Strong_Transform]).

   "Strong" here means tensorial strength, NOT "strong (i.e. pseudo) monoidal
   functor"; the two notions are unrelated.  On a symmetric monoidal base the
   left strength induces a *right* strength by conjugating with the braiding
   (see [rstr] below, with [rstr_natural], [rstr_ret], [rstr_join]), so every
   strong monad over a symmetric base is right-strong in the monad-relevant
   sense.  Two coherence notions for combining a pair of computations appear
   below.  Abstractly, a monad that is simultaneously left- and right-strong
   (over an arbitrary bundled right strength) is *commutative* when its two
   double strengths agree ([CommutativeStrongMonad]).  Concretely, over a
   symmetric base the derived right strength [rstr] yields named double
   strengths M x ⨂ M y ~> M (x ⨂ y) ([dstr], [dstr']) and the predicate
   [commutative_sm] asserting they agree; this double strength is the laxator
   that underlies the Applicative/Day structure of a commutative monad. 

--------
nLab：https://ncatlab.org/nlab/show/strong+monad
 维基百科：https://en.wikipedia.org/wiki/Strong_monad

幺半群范畴 (C, ⊗, I) 上的强单子是一个单子 (M, η, μ)，其
 底层函子 M : C ⟶ C 带有（左）张量强度

t = Strength[M] : x ⨂ M y ~> M (x ⨂ y)（左强度）

— 也就是说，M 是 [StrongFunctor]（参见 Functor.Strong），所以 t 已经
 满足 Kock 的两个相干律 [strength_id_left]（w.r.t. 左
 单元 λ) 和 [strength_assoc] (w.r.t. 关联器 α) — 及其强度
 *与单子结构* η 和 μ 兼容。 继Coq (1972,
 “强函子和幺半群单子”，Arch。 数学。 23）和莫吉（1991，
 “计算和单子的概念”，Inf。 & 计算。 93），两个
 兼容性条件为，写作 t = Strength[M]：

- η-compat ([strength_ret]): t ∘ (id ⨂ η) ≈ η
 在类型 x ⨂ y ~> M (x ⨂ y)

- μ-compat ([strength_join])：t ∘ (id ⨂ μ) ≈ μ ∘ M t ∘ t
 在类型 x ⨂ M (M y) ~> M (x ⨂ y)

换句话说：将 η 从正确的因子中取出，与将 η 应用于
 整个张量，并将 μ 从正确的因子中拉出来与滑动
 通过两个 M 层的强度然后相乘。 这些正是
 使 t 尊重张量变量中的 monad 结构的图，
 这是内化 Kleisli 组合并给出
 Moggi 意义上的计算单子的 do-notation / `>>=`：强
 monad 的效果可以通过环境上下文 x 参数化。

深层结构事实（下面利用作为验证）：两者的兼容性
 定律*精确地*是单子结构的 [Strong_Transform] 平方
 地图。 由于强度[Id] = id ([Id_StrongFunctor])，因此 η-compat 正是
 η 的强度-相容性平方：Id ⟹ M； 由于强度[M ◯ M] =
 M t ∘ t ([Compose_StrongFunctor])，μ-compat正是强项-
 μ 的相容平方：M ◯ M ⟹ M。因此，强单子恰好是
 单位和乘法是*强*自然变换的 monad — a
 强内函子和强自然范畴中的幺半群对象
 转变。 我们在第 2 层部分的末尾明确说明了这一点
 （[ret_Strong_Transform]、[join_Strong_Transform]）。

这里的“强”是指张量强度，而不是“强（即伪）幺半群”
 函子”； 这两个概念是无关的。 在对称幺半群基上
 左强度通过与编织物结合产生“右”强度
 （参见下面的 [rstr]，以及 [rstr_natural]、[rstr_ret]、[rstr_join]），因此每个
 对称基础上的强单子在单子相关中是右强的
 感觉。 出现了用于组合一对计算的两个相干概念
 下面。 抽象地讲，一个同时具有左强和右强的单子
 （在任意捆绑右强度上）是*可交换的*，当它的两个
 双重优势一致 ([CommutativeStrongMonad])。 具体来说，超过一个
 对称基衍生的右强度 [rstr] 产生名为 double
 强度 M x ⨂ M y ~> M (x ⨂ y) ([dstr], [dstr']) 和谓词
 [commutative_sm] 声称他们同意； 这双重力量是泻药
 这是交换单子的应用/日结构的基础。 
*)

(* ================================================================== *)
(** ** The strong monad class.                                          / ** 强单子类。*)
(* ================================================================== *)

Section StrongMonad.

Context `{@Monoidal C}.
Context {M : C ⟶ C}.

(*
A strong monad bundles, over a fixed endofunctor M, both a [Monad] structure
   and a [StrongFunctor] structure on M, together with the two compatibility
   laws relating the strength to η and μ.  The functor-level coherences (λ- and
   α-laws) live in the [StrongFunctor] field; only the monad-specific coherences
   are stated here.  The two structures are coercion fields (`::`) so that
   [ret], [join], [strength], and [fmap[M]] resolve uniformly inside the laws,
   and a [StrongMonad] is usable wherever a [Monad] or [StrongFunctor] is. 

--------
一个强单子束，在一个固定的endofunctor M上，都是[Monad]结构
 以及 M 上的 [StrongFunctor] 结构，以及两者的兼容性
 强度与 η 和 μ 相关的定律。 函子级相干性（λ- 和
 α-定律）存在于 [StrongFunctor] 领域； 仅特定于单子的连贯性
 均在此说明。 这两个结构是强制字段（`::`），因此
 [ret]、[join]、[strength] 和 [fmap[M]] 在法律范围内统一解析，
 无论 [Monad] 或 [StrongFunctor] 在哪里，[StrongMonad] 都可用。 
*)

Class StrongMonad := {
  strongmonad_is_monad  :: @Monad C M;           (* the underlying monad (η, μ)  / 底层单子 (η, μ)*)
  strongmonad_is_strong :: @StrongFunctor C _ M; (* the underlying left strength t  / 基础左强度 t*)

  (*
η-compat (Kock/Moggi): the strength carries the unit pushed into the right
     factor to the unit of the whole tensor.

         x ⨂ y ---- id ⨂ η ----> x ⨂ M y
            \                        |
             \                   strength
              η                     |
               \                    v
                ------------------> M (x ⨂ y)

       t ∘ (id ⨂ η) ≈ η      at  x ⨂ y ~> M (x ⨂ y) 

--------
η-compat (Kock/Moggi)：力量携带单位推入右侧
 整个张量单位的因子。 

x ⨂ y ---- id ⨂ η ----> x ⨂ M y
 \ |
 \实力
 η |
 \v
 ------------------> M (x ⨂ y)

 t ∘ (id ⨂ η) ≈ η at x ⨂ y ~> M (x ⨂ y) 
*)
  strength_ret {x y} :
    strength ∘ (id[x] ⨂ ret[M]) ≈ (ret[M] : x ⨂ y ~> M (x ⨂ y));

  (*
μ-compat (Kock/Moggi): the strength commutes past the multiplication of the
     right factor, sliding through both M-layers.

       x ⨂ M (M y) -- id ⨂ μ --> x ⨂ M y
            |                        |
        strength                 strength
            |                        |
            v                        v
       M (x ⨂ M y)              M (x ⨂ y)
            |                        ^
        M(strength)                  | μ
            v                        |
       M (M (x ⨂ y)) --------------- /

       t ∘ (id ⨂ μ) ≈ μ ∘ M t ∘ t   at  x ⨂ M (M y) ~> M (x ⨂ y).
     The RHS associates left (∘ at level 40): (μ ∘ M t) ∘ t, which is exactly
     μ precomposed with strength[M ◯ M] = M t ∘ t (see [Compose_StrongFunctor]). 

--------
μ-compat (Kock/Moggi)：强度换算超过
 正确的因子，滑过两个 M 层。 

x ⨂ M (M y) -- id ⨂ μ --> x ⨂ M y
 | |
 强度 强度
 | |
 伏
 M (x ⨂ M y) M (x ⨂ y)
 | ^
 M（力量）| μ
 v |
 M (M (x ⨂ y)) -------------- /

 t ∘ (id ⨂ μ) ≈ μ ∘ M t ∘ t 在 x ⨂ M (M y) ~> M (x ⨂ y) 处。 
RHS 左联（∘ 位于 40 级）：(μ ∘ M t) ∘ t，这正是
 μ 预组合为 Strength[M ◯ M] = M t ∘ t（参见 [Compose_StrongFunctor]）。 
*)
  strength_join {x y} :
    strength ∘ (id[x] ⨂ join[M])
      ≈ (join[M] ∘ fmap[M] strength ∘ strength
           : x ⨂ M (M y) ~> M (x ⨂ y))
}.

End StrongMonad.

Arguments StrongMonad {C} _ M.

(* ================================================================== *)
(** ** Tier 1 instance: the identity strong monad.                     / ** 第 1 层实例：恒等强单子。*)
(* ================================================================== *)

Section IdStrongMonad.

Context `{@Monoidal C}.

(*
There is no identity monad on an abstract category in the library yet, so we
   provide one here: Id[C] with ret = id and join = id.  All five monad laws are
   instances of the identity/composition equations, discharged automatically by
   the ambient obligation tactic (cat_simpl).
   Since #469 a second identity monad, with every field given and a
   universe list that is the same on every supported version, is
   Monad/Identity.v's [IdMonad]; this local instance is kept and is not
   rewired onto it, which is outside #469's scope (Monad/Identity.v's NOT
   DELIVERED). 

--------
库中的抽象类别还没有标识单子，所以我们
 此处提供一个：Id[C]，其中 ret = id 且 join = id。 所有五个单子定律都是
 单位/组成方程的实例，自动释放
 环境义务策略（cat_simpl）。 
从 #469 开始，第二个身份单子，给出了每个字段和一个
 每个受支持版本上都相同的 Universe 列表是
 Monad/Identity.v 的 [IdMonad]； 这个本地实例被保留并且不被保留
 重新连接到它，这超出了 #469 的范围（Monad/Identity.v 不是
 已交付）。 
*)
#[local] Program Instance Id_Monad : @Monad C Id[C] := {
  ret  := fun _ => id;
  join := fun _ => id
}.

(*
Combining [Id_Monad] with [Id_StrongFunctor] (whose strength is id) gives the
   identity strong monad.  Both compatibility laws collapse to id ∘ id ≈ id
   (after id ⨂ id = id) and are discharged automatically.  [Id_Monad] is kept
   [local] so it is not leaked into library-wide [Monad] instance resolution. 

--------
将 [Id_Monad] 与 [Id_StrongFunctor]（其强度为 id）相结合可得出
 同一性强的单子。 两个兼容性法则都归结为 id ∘ id ≈ id
 （id ⨂ id = id 之后）并自动放电。 [Id_Monad] 保留
 [local] 因此它不会泄漏到库范围的 [Monad] 实例解析中。 
*)
#[export] Program Instance Id_StrongMonad : StrongMonad _ Id[C] := {
  strongmonad_is_monad  := Id_Monad;
  strongmonad_is_strong := Id_StrongFunctor
}.

End IdStrongMonad.

(* ================================================================== *)
(** ** Tier 2: validation — η and μ are strong natural transformations  / ** 第 2 层：验证 — η 和 μ 是强自然变换*)
(* ================================================================== *)

(*
The deep structural content of the definition: the two compatibility laws are
   *exactly* the [Strong_Transform] squares for the unit and the multiplication.
   We package η and μ as natural-transformation objects (Id ⟹ M and M ◯ M ⟹ M)
   and prove each is a strong natural transformation, reusing [strength_ret] and
   [strength_join].  This confirms a strong monad is a monoid η : Id ⟹ M,
   μ : M ◯ M ⟹ M in the category of strong endofunctors and strong natural
   transformations: each structure map is itself strong. 

--------
定义的深层结构内容：两个相容律是
 *准确*[Strong_Transform] 的单位和乘法平方。 
我们将 η 和 μ 封装为自然变换对象（Id ⟹ M 和 M ◯ M ⟹ M）
 并证明每个都是强大的自然变换，重用 [strength_ret] 和
 [strength_join]。 这证实了强单子是幺半群 η : Id ⟹ M，
 μ : M ◯ M ⟹ M 属于强内函子和强自然函子范畴
 转换：每个结构图本身都很强大。 
*)

Section StrongMonadValidation.

Context `{@Monoidal C}.
Context {M : C ⟶ C}.
Context `{@StrongMonad C _ M}.

(*
η packaged as a natural transformation Id ⟹ M.  Its naturality square is the
   unit naturality law [fmap_ret] of the monad; [Build_Transform'] proves the
   symmetric orientation [naturality_sym] from this one square for free. 

--------
η 封装为自然变换 Id ⟹ M。其自然性平方为
 单子的单位自然律 [fmap_ret]； [Build_Transform'] 证明
 对称方向 [naturality_sym] 从这一块免费。 
*)
Definition Monad_unit : Id[C] ⟹ M :=
  Build_Transform' (F:=Id[C]) (G:=M) (fun _ => ret[M])
    (fun _ _ _ => ltac:(simpl; symmetry; apply fmap_ret)).

(*
μ packaged as a natural transformation M ◯ M ⟹ M.  Its naturality square is
   the multiplication naturality law [join_fmap_fmap] of the monad. 

--------
μ 封装为自然变换 M ◯ M ⟹ M。其自然度平方为
 单子的乘法自然法则 [join_fmap_fmap]。 
*)
Definition Monad_mult : M ◯ M ⟹ M :=
  Build_Transform' (F:=M ◯ M) (G:=M) (fun _ => join[M])
    (fun _ _ _ => ltac:(simpl; symmetry; apply join_fmap_fmap)).

(*
η is a strong natural transformation Id ⟹ M.  Its source [Id] is strong with
   strength = id ([Id_StrongFunctor]), so the [Strong_Transform] square reads

       strength[M] ∘ (id ⨂ η_y) ≈ η_{x⨂y} ∘ strength[Id]

   and since strength[Id] = id this is precisely [strength_ret]. 

--------
η 是一个强自然变换 Id ⟹ M。其来源 [Id] 具有强
 强度 = id ([Id_StrongFunctor])，因此 [Strong_Transform] 方块为

 强度[M] ∘ (id ⨂ η_y) ≈ η_{x⨂y} ∘ 强度[Id]

 由于strength[Id] = id，这正是[strength_ret]。 
*)
#[export] Program Instance ret_Strong_Transform :
  @Strong_Transform C _ Id[C] Id_StrongFunctor M _ Monad_unit.
Next Obligation.
  simpl.
  rewrite id_right.
  apply strength_ret.
Qed.

(*
μ is a strong natural transformation M ◯ M ⟹ M.  Its source [M ◯ M] is strong
   via [Compose_StrongFunctor] with strength = M(strength) ∘ strength, so the
   [Strong_Transform] square reads

       strength[M] ∘ (id ⨂ μ_y) ≈ μ_{x⨂y} ∘ (M(strength) ∘ strength)

   and one [comp_assoc] re-brackets this to exactly [strength_join]. 

--------
μ 是强自然变换 M ◯ M ⟹ M。其来源 [M ◯ M] 强
 通过 [Compose_StrongFunctor] ，强度 = M(强度) ∘ 强度，所以
 [Strong_Transform] 方形读数

 Strength[M] ∘ (id ⨂ μ_y) ≈ μ_{x⨂y} ∘ (M(强度) ∘ 强度)

 一个 [comp_assoc] 将其重新括号为 [strength_join]。 
*)
#[export] Program Instance join_Strong_Transform :
  @Strong_Transform C _ (M ◯ M) (Compose_StrongFunctor M M _ _) M _ Monad_mult.
Next Obligation.
  simpl.
  rewrite comp_assoc.
  apply strength_join.
Qed.

End StrongMonadValidation.

(* ================================================================== *)
(** ** Tier 3: right-strong monads, the symmetric bridge,              / ** 第三层：右强单子，对称桥，*)
(**            commutativity, and the induced double strength.         / 交换性和诱导双倍强度。*)
(* ================================================================== *)

(*
nLab: https://ncatlab.org/nlab/show/strong+monad

   The mirror image of [StrongMonad]: a monad whose functor carries a *right*
   tensorial strength  rstrength : M x ⨂ y ~> M (x ⨂ y)  (so M is a
   [RightStrongFunctor]), compatible with η and μ via the right-hand factor.

     - η-compat ([rstrength_ret]):  rstrength ∘ (ret ⨂ id) ≈ ret
     - μ-compat ([rstrength_join]): rstrength ∘ (join ⨂ id)
                                      ≈ join ∘ fmap rstrength ∘ rstrength

   This dual is provided for completeness and symmetry with [StrongMonad]; no
   instance is built here.  (A derived instance over any symmetric base is
   built in Monad/Strong/Symmetric.v as [rstr_RightStrongMonad].)
   [CommutativeStrongMonad] below deliberately inlines
   a [RightStrongFunctor] plus its two compatibility laws (rather than bundling
   a [RightStrongMonad]) so that the left and right strengths share the *same*
   underlying monad, keeping [join] unambiguous in the commutativity law. 

--------
nLab：https://ncatlab.org/nlab/show/strong+monad

 [StrongMonad] 的镜像：一个函子带有 *right* 的 monad
 张量强度 rstrength : M x ⨂ y ~> M (x ⨂ y) （所以 M 是
 [RightStrongFunctor])，通过右手因子与 η 和 μ 兼容。 

- η-compat ([rstrength_ret]): rstrength ∘ (ret ⨂ id) ≈ ret
 - μ-compat ([rstrength_join])：rstrength ∘（加入 ⨂ id）
 ≈ 连接 ∘ fmap rstrength ∘ rstrength

 此对偶是为了 [StrongMonad] 的完整性和对称性而提供的； 不
 这里建立了实例。 （任何对称基上的派生实例是
 在 Monad/Strong/Symmetric.v 中内置为 [rstr_RightStrongMonad]。）
 [CommutativeStrongMonad] 下面故意内联
 [RightStrongFunctor] 加上它的两个兼容性法则（而不是捆绑
 a [RightStrongMonad]），以便左右侧优势共享*相同*
 底层 monad，使 [join] 在交换律中保持明确。 
*)

Section RightStrongMonad.

Context `{@Monoidal C}.
Context {M : C ⟶ C}.

Class RightStrongMonad := {
  rstrongmonad_is_monad   :: @Monad C M;
  rstrongmonad_is_rstrong :: @RightStrongFunctor C _ M;

  (* η-compat (right): rstrength ∘ (ret ⨂ id) ≈ ret *)
  rstrength_ret {x y} :
    rstrength ∘ (ret[M] ⨂ id[y])
      ≈ (ret[M] : x ⨂ y ~> M (x ⨂ y));

  (*
μ-compat (right): rstrength ∘ (join ⨂ id)
                         ≈ join ∘ fmap rstrength ∘ rstrength 

--------
μ-compat（右）：rstrength ∘（连接 ⨂ id）
 ≈ 连接 ∘ fmap rstrength ∘ rstrength 
*)
  rstrength_join {x y} :
    rstrength ∘ (join[M] ⨂ id[y])
      ≈ (join[M] ∘ fmap[M] rstrength ∘ rstrength
           : M (M x) ⨂ y ~> M (x ⨂ y))
}.

End RightStrongMonad.

Arguments RightStrongMonad {C} _ M.

(* ------------------------------------------------------------------ *)
(** ** Commutative strong monads (left and right strengths cohere).     / ** 可交换的强单子（左右强度一致）。*)
(* ------------------------------------------------------------------ *)

(*
nLab: https://ncatlab.org/nlab/show/commutative+monad

   A *commutative* strong monad is a monad that is simultaneously left-strong
   and right-strong, whose two strengths agree on how to combine a pair of
   computations.  Out of the left strength t and the right strength t' one
   builds two "double strengths" M x ⨂ M y ~> M (x ⨂ y):

     dstr  = μ ∘ M t  ∘ t'   (sequence the left  computation first)
     dstr' = μ ∘ M t' ∘ t    (sequence the right computation first)

   and the monad is commutative when dstr ≈ dstr' — running the two effects in
   either order yields the same result.  This double strength is precisely the
   laxator that exhibits a commutative monad as a lax monoidal monad, and it is
   what underlies the Applicative instance of a commutative monad.

   We share a single underlying [Monad] between the two strengths, so that
   [join] is unambiguous in the commutativity law: the right strength is given
   as a [RightStrongFunctor] together with its two monad-compatibility laws
   relative to that shared monad. 

--------
nLab：https://ncatlab.org/nlab/show/commutative+monad

*可交换的*强单子是同时左强的单子
 和右强，他们的两种优势在如何结合一对方面达成一致
 计算。 从左强度 t 和右强度 t' 中选出一个
 构建两个“双重强度”M x ⨂ M y ~> M (x ⨂ y)：

dstr = μ ∘ M t ∘ t' （先对左边的计算进行排序）
 dstr' = μ ∘ M t' ∘ t （首先对正确的计算进行排序）

当 dstr ≈ dstr' 时，monad 是可交换的——运行两个效果
 任一顺序都会产生相同的结果。 这双倍的力量正是
 Laxator 将交换单子展现为松散单群单子，并且它是
 交换单子的应用实例的基础是什么。

我们在这两种优势之间共享一个底层 [Monad]，因此
 [join] 在交换律中是明确的：给出了正确的强度
 作为 [RightStrongFunctor] 及其两个 monad 兼容性法则
 相对于那个共享单子。 
*)

Section CommutativeStrongMonad.

Context `{@Monoidal C}.
Context {M : C ⟶ C}.

Class CommutativeStrongMonad := {
  comm_is_strong :: @StrongMonad C _ M;

  (* the right strength over the *same* underlying monad  / 相对于“相同”底层单子的正确强度*)
  comm_is_rstrong : @RightStrongFunctor C _ M;

  comm_rstrength_ret {x y} :
    @rstrength _ _ _ comm_is_rstrong x y ∘ (ret[M] ⨂ id[y])
      ≈ (ret[M] : x ⨂ y ~> M (x ⨂ y));

  comm_rstrength_join {x y} :
    @rstrength _ _ _ comm_is_rstrong x y ∘ (join[M] ⨂ id[y])
      ≈ (join[M] ∘ fmap[M] (@rstrength _ _ _ comm_is_rstrong x y)
                ∘ @rstrength _ _ _ comm_is_rstrong (M x) y
           : M (M x) ⨂ y ~> M (x ⨂ y));

  (* the two double strengths agree  / 这两种双倍强度一致*)
  commutativity {x y} :
    join[M] ∘ fmap[M] strength ∘ @rstrength _ _ _ comm_is_rstrong x (M y)
      ≈ join[M] ∘ fmap[M] (@rstrength _ _ _ comm_is_rstrong x y) ∘ strength
}.

End CommutativeStrongMonad.

Arguments CommutativeStrongMonad {C} _ M.

(* ------------------------------------------------------------------ *)
(** ** The symmetric bridge: a strong monad over a symmetric base       / ** 对称桥：对称基础上的强单子*)
(**     carries a right strength compatible with η and μ.               / 具有与 η 和 μ 兼容的正确强度。*)
(* ------------------------------------------------------------------ *)

(*
On a symmetric monoidal base the left strength induces a right strength by
   conjugating with the braiding,

     rstr := M(β) ∘ t ∘ β  :  M x ⨂ y ~> M (x ⨂ y)

   (braid M x ⨂ y → y ⨂ M x, apply the left strength, then braid back inside
   M).  We prove that this derived right strength is natural and satisfies the
   two monad-compatibility laws — so every strong monad over a symmetric base is
   right-strong in the monad-relevant sense.

   This file delivers the derived morphism family with its naturality and
   monad-compatibility laws; the two [RightStrongFunctor] *coherence* laws
   (unit-object [rrstrength_id_right] and associator [rstrength_assoc]) are
   now derivable as well: the braid-unitor coherences (ρ ≈ λ ∘ β and its
   mirrors) are proven from the bare axioms in
   Structure/Monoidal/Braided/Proofs.v ([braid_unit_left],
   [braid_unit_right], [braid_I_I]), and Monad/Strong/Symmetric.v packages
   [rstr] as a full [RightStrongFunctor] and [RightStrongMonad]
   ([rstr_RightStrongFunctor], [rstr_RightStrongMonad]). 

--------
在对称幺半群基上，左强度通过以下方式感应右强度：
 与编织物结合，

rstr := M(β) ∘ t ∘ β : M x ⨂ y ~> M (x ⨂ y)

（编织 M x ⨂ y → y ⨂ M x，施加左侧的力量，然后编织回内侧
 米）。 我们证明这个派生的正确强度是自然的并且满足
 两个单子兼容性法则——所以对称基上的每个强单子都是
 在单子相关的意义上是右强的。

该文件提供了派生的态射族及其自然性和
 单子兼容性法则； 两个 [RightStrongFunctor] *一致性* 定律
 （单元对象 [rrstrength_id_right] 和关联器 [rstrength_assoc]）是
 现在也可导出：辫子单位相干性 (ρ ≈ λ ∘ β 及其
 镜子）是从裸露的公理证明
 结构/单峰/编织/Proofs.v（[braid_unit_left]，
 [braid_unit_right]、[braid_I_I]) 和 Monad/Strong/Symmetric.v 包
 [rstr] 作为完整的 [RightStrongFunctor] 和 [RightStrongMonad]
 （[rstr_RightStrongFunctor]、[rstr_RightStrongMonad]）。 
*)

Section SymmetricRightStrength.

Context `{@SymmetricMonoidal C}.
Context {M : C ⟶ C}.
Context `{@StrongMonad C _ M}.

(* The derived right strength rstr = M(braid) ∘ strength ∘ braid.  / 导出的右强度 rstr = M(辫子) ∘ 强度 ∘ 辫子。*)
Definition rstr {x y} : M x ⨂ y ~> M (x ⨂ y) :=
  fmap[M] braid ∘ strength ∘ braid.

(*
Joint naturality of the derived right strength:
     fmap (f ⨂ g) ∘ rstr ≈ rstr ∘ (fmap f ⨂ g). 

--------
导出的权利强度的联合自然性：
 fmap (f ⨂ g) ∘ rstr ≈ rstr ∘ (fmap f ⨂ g)。 
*)
Lemma rstr_natural {x z y w} (f : x ~> z) (g : y ~> w) :
  fmap[M] (bimap f g) ∘ rstr ≈ rstr ∘ bimap (fmap[M] f) g.
Proof.
  unfold rstr.
  pose proof (@strength_natural _ _ M _ y w g x z f) as SN.
  simpl in SN.
  normal.
  (* LHS: fmap((f⨂g)∘braid) ∘ strength ∘ braid;  (f⨂g)∘braid = braid∘(g⨂f)  / LHS: fmap((f⨂g)∘辫子) ∘ 强度 ∘ 辫子; (f⨂g)∘辫子 = 辫子∘(g⨂f)*)
  rewrite bimap_braid.
  normal.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (fmap[M] (g ⨂ f))).
  rewrite SN.
  rewrite <- !comp_assoc.
  rewrite bimap_braid.
  reflexivity.
Qed.

(* η-compat for the derived right strength: rstr ∘ (ret ⨂ id) ≈ ret.  / 导出的右强度的 η-compat：rstr ∘ (ret ⨂ id) ≈ ret。*)
Lemma rstr_ret {x y} :
  rstr ∘ (ret[M] ⨂ id[y]) ≈ (ret[M] : x ⨂ y ~> M (x ⨂ y)).
Proof.
  unfold rstr.
  rewrite <- !comp_assoc.
  rewrite <- bimap_braid.            (* braid∘(ret⨂id) = (id⨂ret)∘braid *)
  rewrite (comp_assoc strength).
  rewrite strength_ret.
  rewrite comp_assoc.
  rewrite <- fmap_ret.
  rewrite <- !comp_assoc.
  rewrite braid_invol.
  rewrite id_right.
  reflexivity.
Qed.

(*
μ-compat for the derived right strength:
     rstr ∘ (join ⨂ id) ≈ join ∘ fmap rstr ∘ rstr. 

--------
μ-compat 用于导出正确的强度：
 rstr ∘ (join ⨂ id) ≈ join ∘ fmap rstr ∘ rstr。 
*)
Lemma rstr_join {x y} :
  rstr ∘ (join[M] ⨂ id[y])
    ≈ (join[M] ∘ fmap[M] rstr ∘ rstr : M (M x) ⨂ y ~> M (x ⨂ y)).
Proof.
  unfold rstr.
  rewrite <- !comp_assoc.
  rewrite <- bimap_braid.            (* braid∘(join⨂id) = (id⨂join)∘braid *)
  rewrite (comp_assoc strength).
  rewrite strength_join.
  rewrite !comp_assoc.
  rewrite <- join_fmap_fmap.         (* fmap braid ∘ join = join ∘ fmap(fmap braid) *)
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite braid_invol.               (* braid ∘ braid = id collapses the RHS  / braid ∘ braid = id 折叠 RHS*)
  rewrite id_right.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  reflexivity.
Qed.

(*
The induced double strength M x ⨂ M y ~> M (x ⨂ y) built from the left
   strength and the derived right strength, and its mirror. 

--------
从左侧构建的诱导双强度 M x ⨂ M y ~> M (x ⨂ y)
 力量和派生的正确力量，以及它的镜子。 
*)
Definition dstr {x y} : M x ⨂ M y ~> M (x ⨂ y) :=
  join[M] ∘ fmap[M] strength ∘ rstr.

Definition dstr' {x y} : M x ⨂ M y ~> M (x ⨂ y) :=
  join[M] ∘ fmap[M] rstr ∘ strength.

(*
Commutativity over a symmetric base: the two orders of combining a pair of
   computations agree.  This is a genuine extra property of the particular
   strong monad (false for non-commutative monads), recorded here as the
   predicate to be discharged per instance.

   This is the symmetric-base specialization, phrased with the *derived* right
   strength [rstr]; it is distinct from the abstract
   [CommutativeStrongMonad.commutativity] field (stated over an arbitrary
   bundled right strength).  The bridge is provided in
   Monad/Strong/Symmetric.v: [commutative_CommutativeStrongMonad] turns a
   [commutative_sm] witness into a [CommutativeStrongMonad] over the derived
   right strength, and [CSM_commutative_sm] gives the converse whenever the
   bundled right strength agrees with [rstr]; the required braid/unitor
   coherence is [braid_unit_left] in Structure/Monoidal/Braided/Proofs.v. 

--------
对称基上的交换性：组合一对的两个顺序
 计算结果一致。 这是特定的真正的额外财产
 强单子（对于非交换单子为假），此处记录为
 每个实例要释放的谓词。 

这是对称基特化，用*派生*权利来表述
 强度 XPTECT0X； 它有别于抽象的
 [CommutativeStrongMonad.commutativity] 字段（通过任意
 捆绑正确的力量）。 该桥提供在
 Monad/Strong/Symmetric.v：[commutative_CommutativeStrongMonad] 变成
 [commutative_sm] 见证变成了 [CommutativeStrongMonad] 之上的派生
 正确的强度，[CSM_commutative_sm] 每当
 捆绑的正确强度与 [rstr] 一致； 所需的编织层/单元
 Structure/Monoidal/Braided/Proofs.v 中的一致性为 [braid_unit_left]。 
*)
Definition commutative_sm : Type := ∀ x y, @dstr x y ≈ @dstr' x y.

End SymmetricRightStrength.
