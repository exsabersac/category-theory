Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Mod.Free.
Require Import Category.Instance.Mod.FreeMonad.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(* * * T_R X as the finitely supported functions X → R / * * T_R X 作为有限支持的函数 X → R *)

(*
 Book: Mac Lane, “Categories for the Working Mathematician”, 2nd ed.,
 Springer GTM 5, 1998, §VI.4, Exercise 2(a), printed p. 146 (PDF
 p. 155) — maclane:VI.4:ex2
 Book: Riehl, “Category Theory in Context”, Example 5.1.4(iii),
 printed p. 184 (PDF p. 204) — riehl:5.1:example4
 nLab: https://ncatlab.org/nlab/show/free+module

 Mac Lane's part (a) opens “For each set X, T_R X is the set of all
 those functions f: X → R with only a finite number of non-zero
 values”; Riehl: “Formally, a finite R-linear combination is a finitely
 supported function χ : A → R”.  Instance/Mod/FreeMonad.v reads T_R
 X on formal combinations, unconditionally, and their coefficients
 under a decider; this satellite is the third reading.

 THE ISOMORPHISM.  Under a decider for X's ≈, [FinSupp X] is the setoid
 of ≈-respecting functions X → R with a list of points outside which
 they vanish, compared pointwise: the list witnesses finiteness and is
 not compared.  [TR_FinSupp_iso : T_R X ≅ FinSupp X] in Sets sends a
 combination to its coefficient function [to_finsupp], supported on the
 points it names ([fv_gens]), and a function f to Σ f(y)·e_y over its
 support with duplicates removed ([from_finsupp]); both at [eq_refl]
 ([TR_FinSupp_iso_to], [TR_FinSupp_iso_from],
 [TR_FinSupp_iso_coef]).  Its laws are [finsupp_to_from] (pointwise ≈)
 and [finsupp_from_to] ([fv_eq]); the second is refused at [eq_refl]
 (Test/ProbeFreeModule472.v, R13), the collected sum being a different
 term.  [TR_FinSupp_iso] packages two converse facts.  UNIQUENESS: two
 combinations denoting the same element have the same collected
 coefficients ([fv_lc_unique]; the coefficient of z in Σ rᵢ·⟨xᵢ⟩ is the
 sum of the rᵢ with xᵢ ≈ z, [fv_coef_lc]), which is the respectfulness
 of [fv_coef] and the coefficient uniqueness Instance/Mod/Free.v's WHAT
 IS NOT DELIVERED records (“nothing here says two lists denoting the
 same element are related”), proved here under the decider (Free.v's
 CORRECTION (#472)); [to_finsupp] respects ≈ by it.  INJECTIVITY, its
 converse: a combination is determined by its coefficients
 ([fv_coef_injective]), from [fv_collect] (every combination is [fv_eq]
 to the sum of its coefficients over any duplicate-free list naming its
 generators, like terms collected).  The inverse map respects ≈ by
 [fv_coef_injective], so no permutation lemma for the deduplicated
 supports is needed.

 WHY A DECIDER.  The coefficient map is the linear extension of
 Free.v's indicator [fv_probe_at], and deduplicating a support list
 decides membership up to ≈; neither can be written over a bare
 setoid.  The carrier [FinSupp] itself needs none.

 A COMPUTING WITNESS.  Over ℤ on Free.v's two-element setoid [TwoGens]
 the coefficients of 2·e_true + e_false are 2 and 1, and that of
 μ (3·⟨e_true + e_false⟩ + ⟨e_true⟩) at true is 4, at [eq_refl]
 ([TR_coef_Z_true], [TR_coef_Z_false], [TR_coef_Z_join]).

 STRENGTHS.  Every [Example] holds at [eq_refl], restated in the probe.
 [fv_coef_lc] and [fv_lc_unique] are at ≈ as R's own laws are, through
 Instance/Mod/FreeMonad.v's [fv_eval_fibre_lc]; [to_finsupp] reads the
 Leibniz [fv_coef_respects_point] at ≈.  The middle-four interchange of
 [fv_lsum_plus] is Instance/CMon/Biproduct.v's [cmon_plus_interchange]
 at the free module (its [Require] adds no module to this file's
 closure).  One proof ends [Defined] (counted by token),
 [TR_FinSupp_iso], and it is load-bearing: closed alone [Qed] in a
 renamed copy of #472's six files, [TR_FinSupp_iso_to] stops.
 Twenty-three lemmas end [Qed].

 UNIVERSES, read off [About].  The section binds R : RingObject@{c c c}
 and Sets@{c so}, the identification of the ring's levels being the one
 Instance/Mod/FreeMonad.v's coefficient section records (inherited from
 Free.v's [fv_probe_at]).  The list predicates [fs_mem] and [fs_nodup]
 are typed in Type@{c} (with [poly_unit@{c}]), so that no free level is
 left in the lemmas that take them as hypotheses.  Twenty-nine names
 bind c so alone, eleven add one or two levels (nine of them two, the
 module category's object level and [fv_coef]'s fourth level, bounded
 only by c < it, which [to_finsupp] and [finsupp_from_to] bind through
 the Leibniz [fv_coef_respects_point]), and the isomorphism and
 its three readbacks add the six of T_R (Instance/Mod/FreeMonad.v's
 UNIVERSES); the ℤ witnesses bind three or seven levels of their own,
 the carrier level free above [bool] and [Z].  No [Set] but the bound
 Set < m on the module category's object level, and no equation.  On
 Coq 8.19.2 and 8.20.1 every name binds the same levels (compared by
 [About]).

 NOT DELIVERED.  [FinSupp] as a functor, with Mac Lane's
 [(T_R t)f]_y = Σ′ f_x as its action, [TR_FinSupp_iso] natural, and the
 monad structure transported to it; a decision procedure for T_R X's ≈
 (for X inhabited it would need R's decider too). 

 --------
 书籍：Mac Lane，《工作数学家的范畴》，第2版，Springer GTM 5, 1998, §VI.4, 练习2(a)，印刷页146（PDF页155）— maclane:VI.4:ex2
 书籍：Riehl，《范畴论的背景》，例5.1.4(iii)，印刷页184（PDF页204）— riehl:5.1:example4
 nLab: https://ncatlab.org/nlab/show/free+module

 Mac Lane的(a)部分开头写道：“对于每个集合X，T_R X是所有函数 f: X → R 的集合，这些函数只有有限个非零值”；Riehl写道：“形式上，一个有限的R线性组合是一个有限支撑函数 χ : A → R”。Instance/Mod/FreeMonad.v在形式组合上读取T_R X，无条件，并在判定器下读取其系数；这个附属部分是第三种读取方式。同构。在 X 的 ≈ 的判定器下，[FinSupp X] 是一个集合等价类，包含 ≈-保持的函数 X → R，并附有一个在其外部消失的点列表，以逐点比较：该列表证明有限性，但本身不参与比较。[TR_FinSupp_iso : T_R X ≅ FinSupp X] 在集合中将一个组合映射到它的系数函数 [to_finsupp]，支持在其指名的点上（[fv_gens]），并将一个函数 f 映射为其支持点上去重后的 Σ f(y)·e_y（[from_finsupp]）；二者都在 [eq_refl] 上（[TR_FinSupp_iso_to], [TR_FinSupp_iso_from], [TR_FinSupp_iso_coef]）。它的规律为 [finsupp_to_from]（逐点 ≈）和 [finsupp_from_to]（[fv_eq]）；第二条在 [eq_refl]（Test/ProbeFreeModule472.v, R13）被拒绝，因为收集的和是一个不同的项。[TR_FinSupp_iso] 打包了两个相反的事实。唯一性：两个表示相同元素的组合具有相同的收集系数（[fv_lc_unique]；在 Σ rᵢ·⟨xᵢ⟩ 中 z 的系数是所有 xᵢ ≈ z 的 rᵢ 之和，[fv_coef_lc]），这体现了对 [fv_coef] 和系数唯一性 Instance/Mod/Free.v 中未提供内容的尊重（“这里没有说明表示相同元素的两个列表是相关的”），在判定器下证明（Free.v 的 CORRECTION（#472））；[to_finsupp] 因此尊重 ≈。单射性，其逆命题：一个组合由其系数决定（[fv_coef_injective]），来自 [fv_collect]（每个组合都是 [fv_eq] 对于命名其生成元的任何无重复列表上系数之和，如同类项汇总）。逆映射通过 [fv_coef_injective] 尊重 ≈，所以不需要去重后的支撑的排列引理。

 为什么需要判定器。系数映射是 Free.v 的指示器 [fv_probe_at] 的线性扩展，而去重支撑列表可以判断成员是否属于 ≈ 范畴；两者都不能在裸集合上表示。载体 [FinSupp] 本身不需要。

 计算证据。在 Free.v 的两元素集合 ℤ 上的集合 [TwoGens] 中，2·e_true + e_false 的系数是 2 和 1，而 μ (3·⟨e_true + e_false⟩ + ⟨e_true⟩) 在 true 的系数是 4，在 [eq_refl] 上是 ( [TR_coef_Z_true] , [TR_coef_Z_false] , [TR_coef_Z_join] )。优势。每个 [Example] 在 [eq_refl] 时成立，在探针中重新陈述。[fv_coef_lc] 和 [fv_lc_unique] 大约与 R 自身的定律相同，通过 Instance/Mod/FreeMonad.v 的 [fv_eval_fibre_lc]；[to_finsupp] 在 ≈ 时读取 Leibniz [fv_coef_respects_point]。[fv_lsum_plus] 的中间四重交换是 Instance/CMon/Biproduct.v 的 [cmon_plus_interchange] 在自由模上的实现（其 [Require] 不为此文件的闭包添加任何模）。一个证明以 [Defined] 结束（按标记计算），[TR_FinSupp_iso]，并且它是承重的：单独关闭 [Qed] 在 #472 重命名的六个文件副本中，[TR_FinSupp_iso_to] 停止。二十三个引理以 [Qed] 结束。宇宙，读取 [About]。该部分绑定 R：RingObject@{c c c} 和 Sets@{c so}，环的级别的标识是 Instance/Mod/FreeMonad.v 的系数部分记录（继承自 Free.v 的 [fv_probe_at]）。列表谓词 [fs_mem] 和 [fs_nodup] 的类型为 Type@{c}（带 [poly_unit@{c}]），因此在将它们作为假设的引理中不会留下自由级别。二十九个名字
 绑定c如此孤立，十一个增加一到两个级别（其中九个为两个级别，即模块类别的对象级别和[fv_coef]的第四级别，仅受c < it的限制，而[to_finsupp]和[finsupp_from_to]通过莱布尼茨[fv_coef_respects_point]绑定），同构及其三个回读增加了T_R（Instance/Mod/FreeMonad.v的UNIVERSES）的六个级别；ℤ见证者绑定了三个或七个自己的级别，承载级别在[bool]和[Z]之上自由。不存在[Set]，只有模块类别对象级别上Set < m的绑定，并且没有方程。在Coq 8.19.2和8.20.1中，每个名字绑定的级别相同（通过[About]对比）。未送达。[FinSupp] 作为函子，其作用为 Mac Lane 的 [(T_R t)f] _y = Σ′ f_x，[TR_FinSupp_iso] 自然，并且单子结构已被传输到它上面；T_R X 的 ≈ 的决策过程（对于有元素的 X，它还需要 R 的判定器）。
*)

Section FinSupp.

Universes c so.
Context (R : RingObject@{c c c}).

Local Notation scalar := (carrier (rig_setoid (ring_rig R))).
Local Notation rzero := (rig_zero (ring_rig R)).
Local Notation rone := (rig_one (ring_rig R)).
Local Notation radd := (rig_add (ring_rig R)).
Local Notation rmul := (rig_mul (ring_rig R)).

Context (X : Sets@{c so}).
Context (Xdec : ∀ x y : carrier X, (x ≈ y) + ((x ≈ y) → False)).

(* ------------------------------------------------------------------------ *)
(** ** Lists of points up to ≈ / ** 列表中的点最多 ≈ *)

Fixpoint fs_mem@{+} (y : carrier X) (l : list (carrier X)) : Type@{c} :=
  match l with
  | nil => False
  | cons x l' => ((y ≈ x) + fs_mem y l')%type
  end.

Fixpoint fs_nodup@{+} (l : list (carrier X)) : Type@{c} :=
  match l with
  | nil => poly_unit@{c}
  | cons x l' => ((fs_mem x l' → False) * fs_nodup l')%type
  end.

Fixpoint fs_mem_dec@{+} (y : carrier X) (l : list (carrier X)) :
  fs_mem y l + (fs_mem y l → False) :=
  match l as l0 return fs_mem y l0 + (fs_mem y l0 → False) with
  | nil => inr (fun f => f)
  | cons x l' =>
      match Xdec y x with
      | inl e => inl (inl e)
      | inr n =>
          match fs_mem_dec y l' with
          | inl m => inl (inr m)
          | inr nm =>
              inr (fun h => match h with inl e => n e | inr m => nm m end)
          end
      end
  end.

Lemma fs_mem_respects@{+} (y y' : carrier X) (l : list (carrier X)) :
  y ≈ y' → fs_mem y l → fs_mem y' l.
Proof.
  intro E. induction l as [|x l IH]; simpl; [ intro f; exact f | ].
  intros [e|m]; [ left; exact (transitivity (symmetry E) e) | ].
  right; exact (IH m).
Qed.

Lemma fs_mem_app_l@{+} (y : carrier X) (l l' : list (carrier X)) :
  fs_mem y l → fs_mem y (app l l').
Proof.
  induction l as [|x l IH]; simpl; [ intro f; destruct f | ].
  intros [e|m]; [ left; exact e | right; exact (IH m) ].
Qed.

Lemma fs_mem_app_r@{+} (y : carrier X) (l l' : list (carrier X)) :
  fs_mem y l' → fs_mem y (app l l').
Proof.
  induction l as [|x l IH]; simpl; [ exact (fun m => m) | ].
  intro m; right; exact (IH m).
Qed.

(* Duplicates up to ≈ removed, keeping the last copy. / 大约重复项已删除，保留最后一份。 *)
Fixpoint fs_dedup@{+} (l : list (carrier X)) : list (carrier X) :=
  match l with
  | nil => nil
  | cons x l' =>
      match fs_mem_dec x l' with
      | inl _ => fs_dedup l'
      | inr _ => cons x (fs_dedup l')
      end
  end.

Lemma fs_dedup_mem_back@{+} (y : carrier X) (l : list (carrier X)) :
  fs_mem y (fs_dedup l) → fs_mem y l.
Proof.
  induction l as [|x l IH]; simpl; [ exact (fun f => f) | ].
  destruct (fs_mem_dec x l) as [m|n]; simpl.
  - intro h; right; exact (IH h).
  - intros [e|h]; [ left; exact e | right; exact (IH h) ].
Qed.

Lemma fs_dedup_mem@{+} (y : carrier X) (l : list (carrier X)) :
  fs_mem y l → fs_mem y (fs_dedup l).
Proof.
  induction l as [|x l IH]; simpl; [ exact (fun f => f) | ].
  destruct (fs_mem_dec x l) as [m|n]; simpl.
  - intros [e|h]; [ exact (IH (fs_mem_respects x y l (symmetry e) m)) | ].
    exact (IH h).
  - intros [e|h]; [ left; exact e | right; exact (IH h) ].
Qed.

Lemma fs_dedup_nodup@{+} (l : list (carrier X)) : fs_nodup (fs_dedup l).
Proof.
  induction l as [|x l IH]; simpl; [ exact ttt | ].
  destruct (fs_mem_dec x l) as [m|n]; simpl; [ exact IH | ].
  split; [ | exact IH ].
  intro h. exact (n (fs_dedup_mem_back x l h)).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The generators a combination names, and its coefficients there / * ** 生成器是名称的组合，以及它的系数在那里 *)

Fixpoint fv_gens@{+} (t : @FVTerm R X) : list (carrier X) :=
  match t with
  | fv_gen x => cons x nil
  | fv_zero => nil
  | fv_plus s u => app (fv_gens s) (fv_gens u)
  | fv_neg s => fv_gens s
  | fv_smul _ s => fv_gens s
  end.

(*
 A combination's coefficient vanishes at every point it does not
 name. 

 --------
 一个组合的系数在它没有命名的每个点上消失。
*)
Lemma fv_coef_gens_support@{+} (z : carrier X) (t : @FVTerm R X) :
  (fs_mem z (fv_gens t) → False) → fv_coef R Xdec z t ≈ rzero.
Proof.
  induction t as [ x | | s IHs u IHu | s IHs | r s IHs ]; intro n.
  - change (match Xdec z x with inl _ => rone | inr _ => rzero end ≈ rzero).
    destruct (Xdec z x) as [e|_]; [ destruct (n (inl e)) | reflexivity ].
  - reflexivity.
  - refine (transitivity (rig_add_respects (ring_rig R) _ _
              (IHs (fun m => n (fs_mem_app_l z _ _ m))) _ _
              (IHu (fun m => n (fs_mem_app_r z _ _ m)))) _).
    apply (rig_add_zero_l (ring_rig R)).
  - refine (transitivity (ring_neg_respects R _ _ (IHs n)) _).
    exact (ab_neg_zero (ring_ab R)).
  - refine (transitivity (rig_mul_respects (ring_rig R) _ _ (reflexivity r)
                            _ _ (IHs n)) _).
    apply (rig_mul_zero_r (ring_rig R)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Weighted sums of generators / ** 发电机的加权和 *)

(* Σ_{y ∈ D} c_y·e_y. *)
Fixpoint fv_lsum@{+} (cf : carrier X → scalar) (D : list (carrier X))
  : @FVTerm R X :=
  match D with
  | nil => fv_zero
  | cons y D' => fv_plus (fv_smul (cf y) (fv_gen y)) (fv_lsum cf D')
  end.

Lemma fv_lsum_ext@{+} (cf cg : carrier X → scalar) (H : ∀ y, cf y ≈ cg y)
  (D : list (carrier X)) : fv_eq (fv_lsum cf D) (fv_lsum cg D).
Proof.
  induction D as [|y D IH]; simpl; [ apply fv_refl | ].
  exact (fe_plus (fe_smul (H y) (fv_refl _)) IH).
Qed.

Local Notation FM := (FreeModObject X).

Lemma fv_lsum_zero@{+} (D : list (carrier X)) :
  fv_eq (fv_lsum (fun _ => rzero) D) fv_zero.
Proof.
  induction D as [|y D IH]; simpl; [ apply fv_refl | ].
  refine (fe_trans (fe_plus (rm_smul_zero_l FM (fv_gen y)) IH) _).
  exact (fe_zero_l _).
Qed.

(* The middle-four interchange (p + q) + (r + s) ≈ (p + r) + (q + s) is Instance/CMon/Biproduct.v's [cmon_plus_interchange], at the free module. / 中四交换律 (p + q) + (r + s) ≈ (p + r) + (q + s) 是 Instance/CMon/Biproduct.v 中自由模的 [cmon_plus_interchange]。 *)
Lemma fv_lsum_plus@{+} (cf cg : carrier X → scalar) (D : list (carrier X)) :
  fv_eq (fv_lsum (fun y => radd (cf y) (cg y)) D)
        (fv_plus (fv_lsum cf D) (fv_lsum cg D)).
Proof.
  induction D as [|y D IH]; simpl; [ exact (fe_sym (fe_zero_l _)) | ].
  refine (fe_trans (fe_plus (fe_smul_distr_r _ _ _) IH) _).
  exact (cmon_plus_interchange FM _ _ _ _).
Qed.

Lemma fv_lsum_neg@{+} (cf : carrier X → scalar) (D : list (carrier X)) :
  fv_eq (fv_lsum (fun y => ring_neg R (cf y)) D) (fv_neg (fv_lsum cf D)).
Proof.
  induction D as [|y D IH]; simpl; [ exact (fe_sym (ab_neg_zero FM)) | ].
  refine (fe_trans (fe_plus (rm_smul_neg_l FM _ _) IH) _).
  exact (fe_sym (ab_neg_plus FM _ _)).
Qed.

Lemma fv_lsum_smul@{+} (r : scalar) (cf : carrier X → scalar)
  (D : list (carrier X)) :
  fv_eq (fv_lsum (fun y => rmul r (cf y)) D) (fv_smul r (fv_lsum cf D)).
Proof.
  induction D as [|y D IH]; simpl; [ exact (fe_sym (rm_smul_zero_r FM r)) | ].
  refine (fe_trans (fe_plus (fe_smul_assoc _ _ _) IH) _).
  exact (fe_sym (fe_smul_distr_l _ _ _)).
Qed.

Lemma fv_lsum_ext_in@{+} (cf cg : carrier X → scalar) (D : list (carrier X))
  (H : ∀ y, fs_mem y D → cf y ≈ cg y) : fv_eq (fv_lsum cf D) (fv_lsum cg D).
Proof.
  induction D as [|y D IH]; simpl; [ apply fv_refl | ].
  refine (fe_plus (fe_smul (H y (inl (reflexivity y))) (fv_refl _)) _).
  exact (IH (fun y0 m => H y0 (inr m))).
Qed.

(* Σ_{y ∈ D} (e_x)_y·e_y ≈ e_x, for D duplicate-free and naming x. / Σ_{y ∈ D} (e_x)_y·e_y ≈ e_x，对于无重复且命名为 x 的 D。 *)
Lemma fv_lsum_indicator@{+} (x : carrier X) (D : list (carrier X)) :
  fs_nodup D → fs_mem x D →
  fv_eq (fv_lsum (fun y => fv_coef R Xdec y (fv_gen x)) D) (fv_gen x).
Proof.
  induction D as [|y D IH]; [ intros _ f; destruct f | ].
  intros [ny nd] m.
  change (fv_eq (fv_plus (fv_smul (match Xdec y x with
                                   | inl _ => rone | inr _ => rzero end)
                                  (fv_gen y))
                         (fv_lsum (fun y0 => fv_coef R Xdec y0 (fv_gen x)) D))
                (fv_gen x)).
  destruct (Xdec y x) as [e|n].
  - refine (fe_trans (fe_plus (fe_trans (fe_smul_one _) (fe_gen e))
              (fe_trans (fv_lsum_ext_in _ (fun _ => rzero) D _)
                        (fv_lsum_zero D))) _).
    + intros y0 m0.
      change (match Xdec y0 x with inl _ => rone | inr _ => rzero end
              ≈ rzero).
      destruct (Xdec y0 x) as [e0|_]; [ | reflexivity ].
      destruct (ny (fs_mem_respects y0 y D (transitivity e0 (symmetry e)) m0)).
    + exact (fe_trans (fe_comm _ _) (fe_zero_l _)).
  - destruct m as [e|m]; [ destruct (n (symmetry e)) | ].
    refine (fe_trans (fe_plus (rm_smul_zero_l FM _) (IH nd m)) _).
    exact (fe_zero_l _).
Qed.

(* The coefficients of a weighted sum: zero off the list ... / 加权和的系数：列表之外为零... *)
Lemma fv_coef_lsum_out@{+} (cf : carrier X → scalar) (D : list (carrier X))
  (z : carrier X) :
  (fs_mem z D → False) → fv_coef R Xdec z (fv_lsum cf D) ≈ rzero.
Proof.
  induction D as [|y D IH]; intro n; [ reflexivity | ].
  change (radd (rmul (cf y) (match Xdec z y with
                             | inl _ => rone | inr _ => rzero end))
               (fv_coef R Xdec z (fv_lsum cf D)) ≈ rzero).
  destruct (Xdec z y) as [e|_]; [ destruct (n (inl e)) | ].
  refine (transitivity (rig_add_respects (ring_rig R) _ _
                          (rig_mul_zero_r (ring_rig R) _)
                          _ _ (IH (fun m => n (inr m)))) _).
  apply (rig_add_zero_l (ring_rig R)).
Qed.

(* ... and the weight on it, for a duplicate-free list. / ... 以及其上的权重，用于无重复列表。 *)
Lemma fv_coef_lsum_in@{+} (cf : carrier X → scalar)
  (cr : ∀ y y', y ≈ y' → cf y ≈ cf y') (D : list (carrier X))
  (z : carrier X) :
  fs_nodup D → fs_mem z D → fv_coef R Xdec z (fv_lsum cf D) ≈ cf z.
Proof.
  induction D as [|y D IH]; [ intros _ f; destruct f | ].
  intros [ny nd] m.
  change (radd (rmul (cf y) (match Xdec z y with
                             | inl _ => rone | inr _ => rzero end))
               (fv_coef R Xdec z (fv_lsum cf D)) ≈ cf z).
  destruct (Xdec z y) as [e|n].
  - refine (transitivity
              (rig_add_respects (ring_rig R) _ _
                 (rig_mul_one_r (ring_rig R) _) _ _
                 (fv_coef_lsum_out cf D z
                    (fun mz => ny (fs_mem_respects z y D e mz)))) _).
    refine (transitivity (rig_add_zero_r (ring_rig R) _) _).
    exact (cr y z (symmetry e)).
  - destruct m as [e|m]; [ destruct (n e) | ].
    refine (transitivity (rig_add_respects (ring_rig R) _ _
                            (rig_mul_zero_r (ring_rig R) _)
                            _ _ (IH nd m)) _).
    apply (rig_add_zero_l (ring_rig R)).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** Collecting like terms, and coefficient uniqueness / * ** 合并同类项，以及系数的唯一性 *)

(*
 The coefficient of z in Σ rᵢ·⟨xᵢ⟩ is the sum of the rᵢ with xᵢ ≈ z:
 the fibre sum at the identity, by the induction [fv_coef_map_lc]
 uses ([fv_eval_fibre_lc]). 

 --------
 在 Σ rᵢ·⟨xᵢ⟩ 中 z 的系数是所有 xᵢ ≈ z 的 rᵢ 之和：
 通过归纳法在单位元处的纤维和 [fv_coef_map_lc] 
 使用了 ( [fv_eval_fibre_lc] )。
*)
Lemma fv_coef_lc@{+} (z : carrier X) (l : list (fv_pair R X)) :
  fv_coef R Xdec z (fv_lc l) ≈ fv_fibre_sum R Xdec (@id Sets@{c so} X) z l.
Proof. exact (fv_eval_fibre_lc R Xdec (@id Sets@{c so} X) l z). Qed.

(*
 Uniqueness: two combinations denoting the same element have the same
 collected coefficients, so the list is unique up to rearrangement and
 collection of like terms.  It is the respectfulness of [fv_coef];
 [fv_coef_injective] below is its converse. 

 --------
 唯一性：表示相同元素的两个组合具有相同的累积系数，因此列表在重新排列和合并同类项之后是唯一的。下面 [fv_coef] ; [fv_coef_injective] 的尊重性是它的逆。
*)
Theorem fv_lc_unique@{+} (l l' : list (fv_pair R X)) :
  fv_eq (fv_lc l) (fv_lc l') →
  ∀ z, fv_fibre_sum R Xdec (@id Sets@{c so} X) z l
         ≈ fv_fibre_sum R Xdec (@id Sets@{c so} X) z l'.
Proof.
  intros H z.
  refine (transitivity (symmetry (fv_coef_lc z l)) _).
  refine (transitivity (proper_morphism (fv_coef R Xdec z) _ _ H) _).
  exact (fv_coef_lc z l').
Qed.

(*
 Every combination is the sum of its coefficients over any duplicate-free
 list naming its generators. 

 --------
 每个组合都是其系数在任何不重复列出其生成元的列表上的总和。
*)
Lemma fv_collect@{+} (t : @FVTerm R X) (D : list (carrier X)) :
  fs_nodup D → (∀ x, fs_mem x (fv_gens t) → fs_mem x D) →
  fv_eq t (fv_lsum (fun y => fv_coef R Xdec y t) D).
Proof.
  intro nd.
  induction t as [ x | | s IHs u IHu | s IHs | r s IHs ]; intro cov.
  - exact (fe_sym (fv_lsum_indicator x D nd (cov x (inl (reflexivity x))))).
  - exact (fe_sym (fv_lsum_zero D)).
  - refine (fe_trans
              (fe_plus (IHs (fun x m => cov x (fs_mem_app_l x _ _ m)))
                       (IHu (fun x m => cov x (fs_mem_app_r x _ _ m)))) _).
    exact (fe_sym (fv_lsum_plus _ _ D)).
  - refine (fe_trans (fe_neg (IHs cov)) _).
    exact (fe_sym (fv_lsum_neg _ D)).
  - refine (fe_trans (fe_smul (reflexivity r) (IHs cov)) _).
    exact (fe_sym (fv_lsum_smul r _ D)).
Qed.

(* A combination is determined by its coefficients: the converse of [fv_lc_unique], from [fv_collect]. / 一个组合由其系数决定：从 [fv_collect] 得到的 [fv_lc_unique] 的逆。 *)
Theorem fv_coef_injective@{+} (s t : @FVTerm R X) :
  (∀ z, fv_coef R Xdec z s ≈ fv_coef R Xdec z t) → fv_eq s t.
Proof.
  intro H.
  set (D := fs_dedup (app (fv_gens s) (fv_gens t))).
  refine (fe_trans (fv_collect s D (fs_dedup_nodup _)
                      (fun x m => fs_dedup_mem x _ (fs_mem_app_l x _ _ m))) _).
  refine (fe_trans (fv_lsum_ext _ _ H D) _).
  exact (fe_sym (fv_collect t D (fs_dedup_nodup _)
                   (fun x m => fs_dedup_mem x _ (fs_mem_app_r x _ _ m)))).
Qed.

(* ------------------------------------------------------------------------ *)
(* * ** The finitely supported functions, and T_R X ≅ them in Sets / * ** 有有限支撑的函数，以及在集合中 T_R X ≅ 它们 *)

(* A ≈-respecting f : X → R with a list outside which it vanishes. / 一个≈-尊重的函数 f : X → R，它在外部的一个列表中消失。 *)
Record FinSupp : Type := {
  fs_fun : carrier X → scalar;
  fs_resp : ∀ y y', y ≈ y' → fs_fun y ≈ fs_fun y';
  fs_supp : list (carrier X);
  fs_vanish : ∀ y, (fs_mem y fs_supp → False) → fs_fun y ≈ rzero
}.

(* Compared pointwise: the support list is a witness, not data. / 逐点比较：支持列表是证据，而不是数据。 *)
Definition fs_eq@{+} (f g : FinSupp) : Type := ∀ y, fs_fun f y ≈ fs_fun g y.

Lemma fs_eq_Equivalence@{+} : Equivalence fs_eq.
Proof.
  constructor.
  - intros f y. reflexivity.
  - intros f g H y. symmetry. exact (H y).
  - intros f g h H1 H2 y. exact (transitivity (H1 y) (H2 y)).
Qed.

Definition FinSupp_Setoid@{+} : Setoid FinSupp :=
  {| equiv := fs_eq; setoid_equiv := fs_eq_Equivalence |}.

Definition FinSuppObj@{+} : Sets@{c so} :=
  {| carrier := FinSupp; is_setoid := FinSupp_Setoid |}.

(*
 A combination as its coefficient function, supported on the generators
 it names; [fv_coef_respects_point] is Leibniz, read here at ≈. 

 --------
 作为其系数函数的组合，支持它所命名的生成元；[fv_coef_respects_point] 是莱布尼茨，这里读作 ≈。
*)
Definition to_finsupp@{+} (t : @FVTerm R X) : FinSupp :=
  {| fs_fun := fun y => fv_coef R Xdec y t;
     fs_resp := fun y y' e =>
       match fv_coef_respects_point R Xdec y y' e t in _ = v
             return fv_coef R Xdec y t ≈ v with
       | eq_refl => reflexivity _
       end;
     fs_supp := fv_gens t;
     fs_vanish := fun y n => fv_coef_gens_support y t n |}.

(*
 A finitely supported function as the combination Σ f(y)·e_y over its
 support, duplicates removed. 

 --------
 一个有限支撑函数作为其支撑上的组合 Σ f(y)·e_y，重复项已去除。
*)
Definition from_finsupp@{+} (f : FinSupp) : @FVTerm R X :=
  fv_lsum (fs_fun f) (fs_dedup (fs_supp f)).

Lemma finsupp_to_from@{+} (f : FinSupp) (z : carrier X) :
  fv_coef R Xdec z (from_finsupp f) ≈ fs_fun f z.
Proof.
  unfold from_finsupp.
  destruct (fs_mem_dec z (fs_dedup (fs_supp f))) as [m|n].
  - exact (fv_coef_lsum_in (fs_fun f) (fs_resp f) _ z (fs_dedup_nodup _) m).
  - refine (transitivity (fv_coef_lsum_out (fs_fun f) _ z n) _).
    symmetry. exact (fs_vanish f z (fun m => n (fs_dedup_mem z _ m))).
Qed.

Lemma finsupp_from_to@{+} (t : @FVTerm R X) :
  fv_eq (from_finsupp (to_finsupp t)) t.
Proof.
  exact (fe_sym (fv_collect t (fs_dedup (fv_gens t)) (fs_dedup_nodup _)
                   (fun x m => fs_dedup_mem x _ m))).
Qed.

(* Mac Lane's T_R X, “the set of all those functions f : X → R with only a finite number of non-zero values”. / Mac Lane 的 T_R X，“所有那些从 X 到 R 的函数 f 的集合，其中只有有限个非零值。” *)
Definition TR_FinSupp_iso@{+} :
  @Isomorphism Sets@{c so} (fobj[FreeModF R] X) FinSuppObj.
Proof using R X Xdec.
  unshelve refine
    (@Build_Isomorphism Sets@{c so} (fobj[FreeModF R] X) FinSuppObj
       {| morphism := to_finsupp |} {| morphism := from_finsupp |} _ _).
  - intros s t H z. exact (proper_morphism (fv_coef R Xdec z) s t H).
  - intros f g H. apply fv_coef_injective. intro z.
    refine (transitivity (finsupp_to_from f z) _).
    refine (transitivity (H z) _).
    symmetry. exact (finsupp_to_from g z).
  - intros f z. exact (finsupp_to_from f z).
  - intros t. exact (finsupp_from_to t).
Defined.

(*
 The isomorphism sends a combination to its coefficient function, and
 a function to Σ f(y)·e_y over its support, duplicates removed. 

 --------
 同构将一个组合映射到它的系数函数，并将一个函数映射到其支撑上的 Σ f(y)·e_y，重复项被移除。
*)
Example TR_FinSupp_iso_to@{+} (t : @FVTerm R X) :
  to TR_FinSupp_iso t = to_finsupp t := eq_refl.

Example TR_FinSupp_iso_from@{+} (f : FinSupp) :
  from TR_FinSupp_iso f = fv_lsum (fs_fun f) (fs_dedup (fs_supp f))
  := eq_refl.

Example TR_FinSupp_iso_coef@{+} (t : @FVTerm R X) (y : carrier X) :
  fs_fun (to TR_FinSupp_iso t) y = fv_coef R Xdec y t := eq_refl.

End FinSupp.

(* ------------------------------------------------------------------------ *)
(*
   * ** A computing witness: T_ℤ on two generators

   Instance/Mod/Free.v's two-element generating setoid [TwoGens], its
   decider [two_gens_dec] and the integers [Int_Ring], where the action
   computes.  Mac Lane's formulas are then arithmetic, at [eq_refl]. 

   --------
   * ** 一个计算见证：T_ℤ 关于两个生成元

   Instance/Mod/Free.v 的两个元素生成集合 [TwoGens]，其决定器 [two_gens_dec] 和整数 [Int_Ring]，其中进行运算。然后，Mac Lane 的公式在 [eq_refl] 处是算术的。
*)

(* [FVTerm]'s index arguments are implicit and a literal has nothing to propagate them from; these NOTATIONS, not definitions, fix them. The second three build combinations of combinations. / [FVTerm] 的索引参数是隐式的，而字面量没有任何东西可以从中传播它们；这些符号，而不是定义，修正了它们。后面三个构建的是组合的组合。 *)
Local Notation zgen := (@fv_gen Int_Ring TwoGens).
Local Notation zsmul := (@fv_smul Int_Ring TwoGens).
Local Notation zplus := (@fv_plus Int_Ring TwoGens).
Local Notation zgen2 :=
  (@fv_gen Int_Ring (RMod_Forget Int_Ring (FreeModObject TwoGens))).
Local Notation zsmul2 :=
  (@fv_smul Int_Ring (RMod_Forget Int_Ring (FreeModObject TwoGens))).
Local Notation zplus2 :=
  (@fv_plus Int_Ring (RMod_Forget Int_Ring (FreeModObject TwoGens))).

(* The coefficients of 2·e_true + e_false are 2 and 1 ... / 2·e_true + e_false 的系数是 2 和 1 ... *)
Example TR_coef_Z_true :
  fv_coef Int_Ring two_gens_dec true
    (zplus (zsmul 2%Z (zgen true)) (zgen false)) = 2%Z := eq_refl.

Example TR_coef_Z_false :
  fv_coef Int_Ring two_gens_dec false
    (zplus (zsmul 2%Z (zgen true)) (zgen false)) = 1%Z := eq_refl.

(*
 ... and μ of 3·⟨e_true + e_false⟩ + ⟨e_true⟩ has coefficient
 3·1 + 1 = 4 at true. 

 --------
 ... 并且 3·⟨e_true + e_false⟩ + ⟨e_true⟩ 的 μ 在 true 上的系数是 3·1 + 1 = 4。
*)
Example TR_coef_Z_join :
  fv_coef Int_Ring two_gens_dec true
    (@join _ _ (FreeModMonad Int_Ring) TwoGens
       (zplus2 (zsmul2 3%Z (zgen2 (zplus (zgen true) (zgen false))))
               (zgen2 (zgen true)))) = 4%Z := eq_refl.
