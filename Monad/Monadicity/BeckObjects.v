Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Monad.Adjunction.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Limit.Preservation.

Generalizable All Variables.

(**
* Beck objects: split forks, conservativity, created coequalizers

    nLab:      https://ncatlab.org/nlab/show/monadicity+theorem
    Wikipedia: https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem

    Fix a monad (T, η, μ) = (T, ret, join) on a category D, with
    Eilenberg–Moore category D^T (Monad/Eilenberg/Moore.v) and forgetful
    functor U^T = [EM_Forget] (Monad/Eilenberg/Moore/Adjunction.v).  This
    file assembles the three Eilenberg–Moore ingredients that drive
    Beck's monadicity theorem; the theorem itself consumes them through
    the comparison functor.

    1. [canonical_split]: every T-algebra (a, α) is presented by free
       data — the parallel pair μ_a, T α : T (T a) ⇉ T a is coequalized
       by α itself, and the coequalizer is split by the sections η_a and
       η_{T a}.  The order of the pair matters: law 3 of a split
       coequalizer asks the *first* leg to retract the section η_{T a},
       which is the monad unit law μ ∘ η_{T a} ≈ id, so μ_a comes first;
       the second leg T α composes with η_{T a} to η_a ∘ α by naturality
       of η, which is exactly law 4.  [canonical_reflexive] records that
       the same pair is also reflexive, with common section T η_a.

    2. [em_forget_reflects_isos]: U^T is conservative.  An algebra
       homomorphism whose underlying arrow is invertible is itself
       invertible: the inverse arrow is again an algebra homomorphism,
       obtained by conjugating the commuting square with the inverse on
       both sides.

    3. [em_forget_creates_split]: U^T creates coequalizers of U^T-split
       pairs.  Given f, g : (a, α) ⇉ (b, β) in D^T whose underlying pair
       has a split coequalizer e : b ~> q in D, the object q carries a
       unique T-algebra action γ making e an algebra homomorphism, and
       that homomorphism coequalizes f, g in D^T.  The action γ is the
       descent of e ∘ β through T e — legitimate because split
       coequalizers are absolute (Structure/Coequalizer/Split.v), so T
       and T ∘ T both preserve the given split fork — and its algebra
       laws follow by cancelling the split epimorphisms T e and T (T e).
       The whole package is the record [CreatedSplitCoequalizer].  The
       predicate the word "absolute" names is Structure/Coequalizer/
       Absolute.v's [AbsoluteCoequalizer] (#477); the proof here uses the
       stronger [functor_preserves_split], whose image fork is again
       split. 

--------
* Beck 对象：分叉、保守性、创建的共均衡器

nLab：https://ncatlab.org/nlab/show/monadicity+theorem
 维基百科：https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem

修复类别 D 上的 monad (T, η, μ) = (T, ret, join)，其中
 Eilenberg–Moore 类别 D^T (Monad/Eilenberg/Moore.v) 和健忘
 函子 U^T = [EM_Forget] (Monad/Eilenberg/Moore/Adjunction.v)。 这个
 文件汇集了驱动的三个艾伦伯格-摩尔成分
 贝克一元性定理； 定理本身消耗了它们
 比较函子。

1. [canonical_split]：每个T代数（a，α）都由免费呈现
 data — 并行对 μ_a, T α : T (T a) ⇉ T a 相等
 由 α 本身，并且辅均衡器由部分 η_a 和
 η_{T a}。 配对的顺序很重要：分裂法则 3
 协同均衡器要求*第一*腿缩回部分 η_{T a}，
 这是单子单位律 μ ∘ η_{T a} ≈ id，所以 μ_a 排在第一位；
 第二条腿 T α 自然地与 η_{T a} 组合为 η_a ∘ α
 η，这正是定律 4。[canonical_reflexive] 记录了
 同一对也是自反的，具有公共部分 T η_a。

2. [em_forget_reflects_isos]：U^T 是保守的。 代数
 其底层箭头可逆的同态就是它本身
 可逆：逆箭头又是一个代数同态，
 通过将通勤平方与逆矩阵共轭获得
 双方。

3. [em_forget_creates_split]：U^T 创建 U^T-split 的共均衡器
 对。 给定 f, g : (a, α) ⇉ (b, β) 在 D^T 中，其底层对
 D 中有一个分割协均衡器 e : b ~> q，对象 q 带有 a
 独特的 T 代数作用 γ 使 e 成为代数同态，并且
 同态使 D^T 中的 f、g 共等。 作用 γ 是
 e ∘ β 通过 T e 的下降 — 合法，因为分裂
 辅助均衡器是绝对的 (Structure/Coequalizer/Split.v)，所以 T
 和 T ∘ T 都保留给定的分裂叉 - 及其代数
 遵循的定律是取消分裂的同态 T e 和 T (T e)。 
整个套件的记录是[CreatedSplitCoequalizer]。 的
 谓词“绝对”名称是 Structure/Coequalizer/
 Absolute.v 的 [AbsoluteCoequalizer] (#477)； 这里的证明使用
 更强的[functor_preserves_split]，其图像再次分叉
 分裂。 
*)

Section BeckObjects.

Context {D : Category}.
Context (T : D ⟶ D).
Context `{H : @Monad D T}.

(**
** The canonical split presentation of an algebra

    For an algebra (a, α), the fork

        μ_a, T α : T (T a) ⇉ T a  --α-->  a

    is a split coequalizer: α coforks the pair (the associativity law
    [t_action], read backwards), η_a splits α (the unit law [t_id]),
    η_{T a} splits μ_a (the monad law [join_ret]), and T α ∘ η_{T a}
    computes η_a ∘ α (naturality [fmap_ret] of the unit). 

--------
** 代数的规范分裂表示

 对于代数 (a, α)，叉子

 μ_a, T α : T (T a) ⇉ T a --α--> a

 是一个分裂共均衡器：α coforks 该对（结合律
 [t_action]，向后读），η_a 分割 α（单位定律 [t_id]），
 η_{T a} 分裂 μ_a（单子定律 [join_ret]），并且 T α ∘ η_{T a}
 计算 η_a ∘ α （单位的自然性 [fmap_ret]）。 
*)

Definition canonical_split {a : D} (α : TAlgebra T a) :
  SplitCoequalizer (@join D T H a) (fmap[T] (t_alg[α])).
Proof.
  unshelve refine
    {| scoeq_obj := a
     ; scoeq_e   := t_alg[α]
     ; scoeq_s   := ret
     ; scoeq_t   := ret |}.
  - (* law 1: α ∘ μ ≈ α ∘ T α, i.e. [t_action] reversed  / 定律1：α ∘ μ ≈ α ∘ T α，即[t_action]反转*)
    symmetry.
    apply (@t_action D T H a α).
  - (* law 2: α ∘ η ≈ id, i.e. [t_id]  / 定律2：α ∘ η ≈ id，即[t_id]*)
    apply (@t_id D T H a α).
  - (* law 3: μ ∘ η_{T a} ≈ id, i.e. [join_ret]  / 定律3：μ ∘ η_{T a} ≈ id，即[join_ret]*)
    apply join_ret.
  - (* law 4: T α ∘ η_{T a} ≈ η_a ∘ α, naturality of η reversed  / 定律4：T α ∘ η_{T a} ≈ η_a ∘ α，η 的自然性反转*)
    symmetry.
    apply fmap_ret.
Defined.

(**
The same canonical pair is reflexive: T η_a is a common section,
    by the monad law [join_fmap_ret] on the μ side and functoriality
    over the unit law [t_id] on the T α side. 

--------
相同的规范对是自反的：T η_a 是公共部分，
 由 μ 侧的单子定律 [join_fmap_ret] 和函子性
 超过 T α 侧的单位律 [t_id]。 
*)

Definition canonical_reflexive {a : D} (α : TAlgebra T a) :
  ReflexivePair (@join D T H a) (fmap[T] (t_alg[α])).
Proof.
  unshelve refine {| refl_section := fmap[T] ret |}.
  - (* μ ∘ T η ≈ id *)
    apply join_fmap_ret.
  - (* T α ∘ T η ≈ T (α ∘ η) ≈ T id ≈ id *)
    rewrite <- fmap_comp.
    rewrite (@t_id D T H a α).
    apply fmap_id.
Defined.

(**
** A functor sends split epis to epis

    The image under T of a morphism with a right inverse is again a
    split epi, hence epic.  Used below to cancel T e and T (T e). 

--------
** 函子将分割的 epis 发送到 epis

 具有右逆逆的态射在 T 下的图像又是 a
 分裂 Epi，因此是史诗。 下面用于取消T e 和T (T e)。 
*)

Lemma fmap_split_epic {x y : D} (p : x ~> y) (s : y ~> x)
  (Hps : p ∘ s ≈ id) : Epic (fmap[T] p).
Proof.
  apply retractions_are_epic.
  exists (fmap[T] s).
  rewrite <- fmap_comp.
  rewrite Hps.
  apply fmap_id.
Qed.

(**
** The forgetful functor reflects isomorphisms

    Let h : (a, α) ~> (b, β) be an algebra homomorphism with underlying
    arrow h₀ and suppose h₀ has a two-sided inverse k in D.  Then k is
    itself an algebra homomorphism (b, β) ~> (a, α):

        k ∘ β ≈ k ∘ β ∘ T (h₀ ∘ k)          (h₀ ∘ k ≈ id)
              ≈ k ∘ (β ∘ T h₀) ∘ T k
              ≈ k ∘ (h₀ ∘ α) ∘ T k          (square for h, reversed)
              ≈ (k ∘ h₀) ∘ α ∘ T k
              ≈ α ∘ T k.                    (k ∘ h₀ ≈ id)

    The two inverse laws upstairs are then the ones downstairs, since
    hom-equivalence in D^T is hom-equivalence of underlying arrows.  The
    proof below runs the chain backwards, cancelling the split epi T h₀
    on the right. 

--------
** 健忘函子反映了同构

 设 h : (a, α) ~> (b, β) 是具有底层的代数同态
 箭头 h₀ 并假设 h₀ 在 D 中具有双边逆 k。则 k 为
 本身是一个代数同态 (b, β) ~> (a, α)：

 k ∘ β ≈ k ∘ β ∘ T (h₀ ∘ k) (h₀ ∘ k ≈ id)
 ≈ k ∘ (β ∘ T h₀) ∘ T k
 ≈ k ∘ (h₀ ∘ α) ∘ T k （h 的平方，反转）
 ≈ (k ∘ h₀) ∘ α ∘ T k
 ≈ α ∘ T k。 (k ∘ h₀ ≈ id)

 楼上的两个反定律就是楼下的两个反定律，因为
 D^T 中的 hom 等价是基础箭头的 hom 等价。 的
 下面的证明使链向后运行，取消了分裂 Epi T h₀
 在右边。 
*)

Lemma em_iso_inverse_commutes {x y : EilenbergMoore T}
  (h : x ~{EilenbergMoore T}~> y)
  (I : IsIsomorphism (t_alg_hom[h])) :
  @two_sided_inverse D _ _ _ I ∘ t_alg[`2 y]
    ≈ t_alg[`2 x] ∘ fmap[T] (@two_sided_inverse D _ _ _ I).
Proof.
  apply (@epic _ _ _ _
           (fmap_split_epic (t_alg_hom[h]) (@two_sided_inverse D _ _ _ I)
              (@is_right_inverse D _ _ _ I))).
  rewrite <- !comp_assoc.
  rewrite <- (@t_alg_hom_commutes _ _ _ _ _ _ _ h).
  rewrite <- fmap_comp.
  rewrite (@is_left_inverse D _ _ _ I).
  rewrite fmap_id.
  rewrite id_right.
  rewrite comp_assoc.
  rewrite (@is_left_inverse D _ _ _ I).
  apply id_left.
Qed.

(** The inverse arrow, packaged as a morphism of D^T.  / 反箭头，封装为 D^T 的态射。*)

Definition em_iso_inverse_hom {x y : EilenbergMoore T}
  (h : x ~{EilenbergMoore T}~> y)
  (I : IsIsomorphism (t_alg_hom[h])) :
  y ~{EilenbergMoore T}~> x :=
  {| t_alg_hom := @two_sided_inverse D _ _ _ I
   ; t_alg_hom_commutes := em_iso_inverse_commutes h I |}.

(**
U^T is conservative.  Note that [fmap[EM_Forget T] h] is
    definitionally [t_alg_hom[h]], so the hypothesis hands us exactly an
    inverse of the underlying arrow, and the inverse laws upstairs hold
    by the same equations downstairs. 

--------
U^T 是保守的。 请注意 [fmap[EM_Forget T] h] 是
 定义为 [t_alg_hom[h]]，因此该假设为我们提供了一个准确的
 底层箭头的逆，楼上的逆定律成立
 通过楼下相同的方程。 
*)

#[export] Instance em_forget_reflects_isos : ReflectsIsos (EM_Forget T).
Proof.
  constructor.
  intros x y h I.
  unshelve refine {| two_sided_inverse := em_iso_inverse_hom h I |}.
  - exact (@is_right_inverse D _ _ _ I).
  - exact (@is_left_inverse D _ _ _ I).
Qed.

(**
** Creation of coequalizers of split pairs

    Fix algebra homomorphisms f, g : (a, α) ⇉ (b, β) and a split
    coequalizer [SC] of their underlying pair in D, with object q,
    coequalizing map e : b₀ ~> q, and sections s and t.  We manufacture
    the unique algebra structure on q for which e is a homomorphism, and
    show the resulting homomorphism coequalizes f, g in D^T. 

--------
** 创建分割对的共均衡器

 修复代数同态 f, g : (a, α) ⇉ (b, β) 和分裂
 D 中底层对的 coequalizer [SC]，带有对象 q，
 共均衡映射 e : b₀ ~> q，以及 s 和 t 部分。 我们制造
 q 上的唯一代数结构，其中 e 是同态，并且
 表明所得到的同态与 D^T 中的 f、g 共等。 
*)

Section CreatedCoequalizers.

Context {a b : EilenbergMoore T}.
Context (f g : a ~{EilenbergMoore T}~> b).
Context (SC : SplitCoequalizer (t_alg_hom[f]) (t_alg_hom[g])).

(** Split coequalizers are absolute, so T preserves this one.  / 分离共均衡器是绝对的，所以 T 保留了这个。*)

Definition beck_image_split :
  SplitCoequalizer (fmap[T] (t_alg_hom[f])) (fmap[T] (t_alg_hom[g])) :=
  functor_preserves_split T (t_alg_hom[f]) (t_alg_hom[g]) SC.

(**
The three split epimorphisms we cancel against: e itself, T e (the
    coequalizing map of the preserved fork), and T (T e). 

--------
我们取消的三个分裂的同态：e本身，T e（
 保留叉子的共均衡图）和 T (T e)。 
*)

Lemma beck_e_epic : Epic (scoeq_e SC).
Proof.
  apply retractions_are_epic.
  exists (scoeq_s SC).
  apply (scoeq_law2 SC).
Qed.

Definition beck_fmap_e_epic : Epic (fmap[T] (scoeq_e SC)) :=
  fmap_split_epic (scoeq_e SC) (scoeq_s SC) (scoeq_law2 SC).

Definition beck_fmap_fmap_e_epic :
  Epic (fmap[T] (fmap[T] (scoeq_e SC))) :=
  fmap_split_epic (fmap[T] (scoeq_e SC)) (fmap[T] (scoeq_s SC))
    (scoeq_law2 beck_image_split).

(**
e ∘ β coforks the T-image pair: push β through the commuting
    squares of f and g, then use the cofork law of [SC] under e. 

--------
e ∘ β 共同分叉 T 图像对：通过通勤推动 β
 f 和 g 的平方，然后在 e 下使用 [SC] 的 cofork 定律。 
*)

Lemma beck_image_cofork :
  (scoeq_e SC ∘ t_alg[`2 b]) ∘ fmap[T] (t_alg_hom[f])
    ≈ (scoeq_e SC ∘ t_alg[`2 b]) ∘ fmap[T] (t_alg_hom[g]).
Proof.
  rewrite <- !comp_assoc.
  rewrite <- (@t_alg_hom_commutes _ _ _ _ _ _ _ f).
  rewrite <- (@t_alg_hom_commutes _ _ _ _ _ _ _ g).
  rewrite !comp_assoc.
  rewrite (scoeq_law1 SC).
  reflexivity.
Qed.

(**
The created action: descend e ∘ β through the preserved coequalizer
    T e.  Its defining triangle γ ∘ T e ≈ e ∘ β is [created_action_sq]. 

--------
创建的动作：通过保留的协均衡器降低 e ∘ β
 特E。 其定义三角形 γ ∘ T e ≈ e ∘ β 是 [created_action_sq]。 
*)

Definition beck_action_desc :
  ∃! u : T (scoeq_obj SC) ~{D}~> scoeq_obj SC,
    u ∘ fmap[T] (scoeq_e SC) ≈ scoeq_e SC ∘ t_alg[`2 b] :=
  split_coeq_desc beck_image_split (scoeq_e SC ∘ t_alg[`2 b])
    beck_image_cofork.

Definition created_action : T (scoeq_obj SC) ~{D}~> scoeq_obj SC :=
  unique_obj beck_action_desc.

Definition created_action_sq :
  created_action ∘ fmap[T] (scoeq_e SC) ≈ scoeq_e SC ∘ t_alg[`2 b] :=
  unique_property beck_action_desc.

(**
Unit law for γ: precompose with the epi e, slide η past e by
    naturality, contract γ ∘ T e, then use the unit law of β. 

--------
γ 的单位定律：与 epi e 预合成，将 η 滑过 e
 自然性，契约 γ ∘ T e，则使用 β 的单位律。 
*)

Lemma created_action_t_id : created_action ∘ ret ≈ id.
Proof.
  apply (@epic _ _ _ _ beck_e_epic).
  rewrite <- comp_assoc.
  rewrite fmap_ret.
  rewrite comp_assoc.
  rewrite created_action_sq.
  rewrite <- comp_assoc.
  rewrite (@t_id D T H _ (`2 b)).
  rewrite id_right.
  rewrite id_left.
  reflexivity.
Qed.

(**
Associativity law for γ: both sides agree after precomposition with
    the epi T (T e) — the left leg contracts γ ∘ T e twice, the right
    leg slides μ past T (T e) by naturality and contracts once; what
    remains is the associativity law of β under e. 

--------
γ 的结合律：预合成后双方一致
 epi T (T e) — 左腿收缩 γ ∘ T e 两次，右腿收缩
 腿自然地滑过 T (T e) 并收缩一次； 什么
 仍然是 e 下 β 的结合律。 
*)

Lemma created_action_t_action :
  created_action ∘ fmap[T] created_action ≈ created_action ∘ join.
Proof.
  apply (@epic _ _ _ _ beck_fmap_fmap_e_epic).
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.
  rewrite created_action_sq.
  rewrite fmap_comp.
  rewrite join_fmap_fmap.
  rewrite !comp_assoc.
  rewrite created_action_sq.
  rewrite <- !comp_assoc.
  rewrite (@t_action D T H _ (`2 b)).
  reflexivity.
Qed.

(**
The created algebra (q, γ), and e as an algebra homomorphism into
    it.  Its carrier is definitionally the coequalizing map e. 

--------
创建的代数 (q, γ) 和 e 作为代数同态为
 它。 它的载体定义为共均衡映射 e。 
*)

Definition created_algebra : @TAlgebra D T H (scoeq_obj SC) :=
  {| t_alg    := created_action
   ; t_id     := created_action_t_id
   ; t_action := created_action_t_action |}.

Lemma created_e_commutes :
  scoeq_e SC ∘ t_alg[`2 b] ≈ created_action ∘ fmap[T] (scoeq_e SC).
Proof.
  symmetry.
  apply created_action_sq.
Qed.

Definition created_e_hom :
  b ~{EilenbergMoore T}~> (scoeq_obj SC; created_algebra) :=
  @Build_TAlgebraHom D T H (`1 b) (scoeq_obj SC) (`2 b) created_algebra
    (scoeq_e SC) created_e_commutes.

(**
Descent upstairs.  A homomorphism h coforking f, g has a coforking
    carrier, hence descends through e downstairs; the descended arrow is
    itself a homomorphism, seen by cancelling the epi T e: both sides of
    its square restrict along T e to h₀ ∘ β. 

--------
下楼。 同态 h 同态 f, g 有同态
 载体，因此通过 e 下降到楼下； 下降箭头是
 本身是同态，通过取消 epi T e 可以看出：
 它的平方沿 T e 限制到 h₀ ∘ β。 
*)

Lemma created_desc_is_alg_hom (z : EilenbergMoore T)
  (h : b ~{EilenbergMoore T}~> z)
  (Hh : t_alg_hom[h] ∘ t_alg_hom[f] ≈ t_alg_hom[h] ∘ t_alg_hom[g]) :
  unique_obj (split_coeq_desc SC (t_alg_hom[h]) Hh) ∘ created_action
    ≈ t_alg[`2 z]
        ∘ fmap[T] (unique_obj (split_coeq_desc SC (t_alg_hom[h]) Hh)).
Proof.
  apply (@epic _ _ _ _ beck_fmap_e_epic).
  rewrite <- !comp_assoc.
  rewrite created_action_sq.
  rewrite <- fmap_comp.
  rewrite (unique_property (split_coeq_desc SC (t_alg_hom[h]) Hh)).
  rewrite comp_assoc.
  rewrite (unique_property (split_coeq_desc SC (t_alg_hom[h]) Hh)).
  apply (@t_alg_hom_commutes _ _ _ _ _ _ _ h).
Qed.

Definition created_desc_hom (z : EilenbergMoore T)
  (h : b ~{EilenbergMoore T}~> z)
  (Hh : t_alg_hom[h] ∘ t_alg_hom[f] ≈ t_alg_hom[h] ∘ t_alg_hom[g]) :
  ((scoeq_obj SC; created_algebra) : EilenbergMoore T)
    ~{EilenbergMoore T}~> z :=
  @Build_TAlgebraHom D T H (scoeq_obj SC) (`1 z) created_algebra (`2 z)
    (unique_obj (split_coeq_desc SC (t_alg_hom[h]) Hh))
    (created_desc_is_alg_hom z h Hh).

(**
The universal property upstairs: since hom-equivalence and
    composition in D^T are those of D on carriers, the triangle and the
    uniqueness clause are exactly the ones of the split coequalizer
    downstairs, transported along [created_desc_hom]. 

--------
楼上的通用属性：因为 home 等价且
 D^T 中的组成是 D 在载体、三角形和
 uniqueness 子句正是 split coequalizer 的子句
 楼下，沿着[created_desc_hom]运输。 
*)

Definition created_is_coequalizer :
  IsCoequalizer f g (scoeq_obj SC; created_algebra) created_e_hom.
Proof.
  unshelve refine {| cofork := _ ; coeq_desc := _ |}.
  - (* e coforks f, g upstairs since it does downstairs  / e coforks f, g 在楼上，因为它在楼下*)
    exact (scoeq_law1 SC).
  - intros z h Hh.
    unshelve refine {| unique_obj := created_desc_hom z h Hh |}.
    + (* the triangle is the one downstairs  / 三角形就是楼下那个*)
      exact (unique_property (split_coeq_desc SC (t_alg_hom[h]) Hh)).
    + (* uniqueness on carriers is uniqueness downstairs  / 航母上的独特性就是楼下的独特性*)
      intros v Hv.
      exact (uniqueness (split_coeq_desc SC (t_alg_hom[h]) Hh)
               (t_alg_hom[v]) Hv).
Defined.

(**
Uniqueness of the created action: any algebra structure on q making
    e a homomorphism satisfies the defining triangle of γ, so descent
    uniqueness identifies the two actions. 

--------
所创建动作的唯一性：q 上的任何代数结构
 e 同态满足 γ 的定义三角形，因此下降
 唯一性标识了这两个动作。 
*)

Lemma created_algebra_unique (alg' : @TAlgebra D T H (scoeq_obj SC)) :
  scoeq_e SC ∘ t_alg[`2 b] ≈ t_alg[alg'] ∘ fmap[T] (scoeq_e SC) →
  t_alg[alg'] ≈ t_alg[created_algebra].
Proof.
  intros Halg.
  symmetry.
  apply (uniqueness beck_action_desc).
  symmetry.
  exact Halg.
Qed.

(**
The record a consumer of creation receives: the algebra on the
    coequalizer object, the coequalizing homomorphism with its carrier
    pinned to e, the coequalizer property upstairs, and uniqueness of
    the algebra structure. 

--------
创造的消费者收到的记录：关于的代数
 共均衡器对象，与其载体的共均衡同态
 固定到 e，楼上的 coequalizer 属性，以及
 代数结构。 
*)

Record CreatedSplitCoequalizer : Type := {
  created_alg : @TAlgebra D T H (scoeq_obj SC);
  created_hom : b ~{EilenbergMoore T}~> (scoeq_obj SC; created_alg);
  created_hom_carrier : t_alg_hom[created_hom] ≈ scoeq_e SC;
  created_coequalizes :
    IsCoequalizer f g (scoeq_obj SC; created_alg) created_hom;
  created_alg_unique (alg' : @TAlgebra D T H (scoeq_obj SC)) :
    scoeq_e SC ∘ t_alg[`2 b] ≈ t_alg[alg'] ∘ fmap[T] (scoeq_e SC) →
    t_alg[alg'] ≈ t_alg[created_alg]
}.

Theorem em_forget_creates_split : CreatedSplitCoequalizer.
Proof.
  unshelve refine
    {| created_alg := created_algebra
     ; created_hom := created_e_hom |}.
  - (* the carrier of the created homomorphism is e on the nose  / 所创建的同态的载体是鼻子上的e*)
    reflexivity.
  - exact created_is_coequalizer.
  - exact created_algebra_unique.
Defined.

End CreatedCoequalizers.

End BeckObjects.
