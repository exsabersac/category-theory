Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Adjunction.Map.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Morphism.Algebra.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Monad.Monadicity.Beck.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Monad.Comparison.Resolution.

Generalizable All Variables.

(**
* Probe for issue #482: the strength boundaries of
      Monad/Comparison/Resolution.v and the controls of
      Instance/Fun/Action/Monad/Comparison.v

--------
* 针对问题 #482 的探查：Monad/Comparison/Resolution.v 的强度边界以及 Instance/Fun/Action/Monad/Comparison.v 的控制
*)

(*
The import list is the first target's, in its order, followed by that
   target.  The last section adds, after every command above it, the
   import list of the second target,
   Instance/Fun/Action/Monad/Comparison.v, and that module; so nothing
   above it is elaborated under the second target's imports.

   REFUTATIONS.  Five lines open with the refutation keyword: the
   instrument, NAME-ABSENCE, a [Check] of a name that does not exist,
   which shows that the keyword is live; and four CONVERSION boundaries,
   R1, R2a, R2 and R3, each a statement that is well typed and refused
   at [eq_refl].  Each refutation, stripped of its keyword in a copy of
   this whole file, stops inside the stripped command, the instrument
   with "The reference p482_absent_name was not found in the current
   environment" and the other four with "cannot unify" (five of five,
   measured).  Each control, prefixed in such a copy, stops with "The
   command has not" and the rest of that message (twenty-three of
   twenty-three).

   R1  The strict left triangle of [EM_Comparison] on objects:
       K (F x) = F^T x at [eq_refl].  The two algebras agree on carrier
       (C1) and on structure map (C2), both at [eq_refl]; the [TAlgebra]
       records differ in their law fields.  This is why the comparison of
       a resolution is read at ≈ (the target's header, THE READING).
   R2  The Lemma's comparison at the Eilenberg–Moore resolution,
       [EM_Comparison_via_Lemma], against [EM_Comparison], on objects at
       [eq_refl].  They agree on carriers (C3) and are isomorphic
       ([EM_Comparison_via_Lemma_agrees]); R2a: their structure maps are
       refused at [eq_refl].  The Lemma's uniqueness is up to
       isomorphism, not on the nose.  R2a and R2 measure conversion:
       the Leibniz equality of the two is neither proved nor refuted.
   R3  The coherence [cmp_monad] of [EM_Comparison_Comparison] at
       [eq_refl]: its left side is id ∘ id at [eq_refl] (C5), the right
       side id, in a variable category.

   CONTROLS.  C1-C5 above; C4, the right triangle of the Lemma's
   comparison at the Eilenberg–Moore resolution on objects, at
   [eq_refl]; and C6-C17, the twelve [Example]s of the first target
   restated, so that a rename or a lost transparency breaks this file.
   In the last section, the second target's positive controls: at the
   adjunction of LZ-sets, [EM_Comparison] satisfies the two hypotheses
   that [bare_awodey_refuted] quantifies over (C18, C19) and is a
   comparison over the identity identification (C20), to which
   [EM_Comparison_unique] applies (C21), so that neither
   [bare_awodey_refuted] nor [K_no_coherent_comparison] is vacuous; and
   C22, C23, that target's two [Example]s restated.

--------
导入列表是第一个目标的，按照它的顺序，随后是该目标。最后一部分在其上面的每条命令之后添加第二个目标的导入列表，Instance/Fun/Action/Monad/Comparison.v，以及该模块；因此它上面的内容不会在第二个目标的导入下展开。

反驳。五行以反驳关键词开头：该工具，NAME-ABSENCE，一个不存在名称的[Check]，显示该关键词是有效的；以及四个CONVERSION边界，R1、R2a、R2和R3，每个都是类型良好的声明，在[eq_refl]处被拒绝。每个反驳在该文件的副本中删除其关键词后，都在被删除的命令中停止，其中工具显示“在当前环境中未找到引用p482_absent_name”，其余四个显示“无法统一”（五个中的五个，已测量）。每个控制在这样的副本中添加前缀后停止于“该命令尚未”及该消息的其余部分（二十三个中的二十三个）。

R1  [EM_Comparison] 在对象上的严格左三角形：
       K (F x) = F^T x 在 [eq_refl]。 这两个代数在承载体 (C1) 和结构映射 (C2) 上都一致，都在 [eq_refl]；[TAlgebra] 的记录在其律字段上有所不同。 这就是为什么对解析的比较会在 ≈ 上读取（目标的标题，THE READING）。
   R2  引理在 Eilenberg–Moore 解析 [EM_Comparison_via_Lemma] 上与 [EM_Comparison] 的比较，在对象 [eq_refl] 上。 它们在承载体 (C3) 上一致，并且同构 ([EM_Comparison_via_Lemma_agrees])；R2a：它们的结构映射在 [eq_refl] 上被拒绝。 引理的唯一性是同构意义上的，而不是字面上的。 R2a 和 R2 测量转换：两者的 Leibniz 等式既未被证明，也未被反驳。
   R3  [EM_Comparison_Comparison] 在 [eq_refl] 上的相干性 [cmp_monad]：其左侧在 [eq_refl] 是 id ∘ id (C5)，右侧是 id，在一个变量范畴中。

控制。以上的 C1-C5；C4，在 Eilenberg–Moore 对象分解上的引理比较的直角三角形，在 [eq_refl]；以及 C6-C17，第一个目标重新陈述的十二个 [Example]，因此重命名或丢失透明性会破坏此文件。在最后一节中，第二个目标的正控制：在 LZ 集合的伴随下，[EM_Comparison] 满足 [bare_awodey_refuted] 在 (C18, C19) 上量化的两个假设，并且是身份识别 (C20) 上的比较，[EM_Comparison_unique] 应用于此 (C21)，因此 [bare_awodey_refuted] 和 [K_no_coherent_comparison] 都不是空的；以及 C22、C23，该目标的两个 [Example] 重新陈述。
*)

(* ------------------------------------------------------------------------ *)
(** ** The instrument / ** 乐器 *)

(* The instrument / 乐器 *)
Fail Check p482_absent_name.

Section EMProbe.

Context {X A : Category} {F : X ⟶ A} {G : A ⟶ X} (Adj : F ⊣ G).

Local Notation T := (Adjunction_Induced_Monad Adj).

Example C1 (x : X) :
  `1 (fobj[EM_Comparison Adj ◯ F] x) = `1 (fobj[@EM_Free X (G ◯ F) T] x)
  := eq_refl.

Example C2 (x : X) :
  t_alg[`2 (fobj[EM_Comparison Adj ◯ F] x)]
    = t_alg[`2 (fobj[@EM_Free X (G ◯ F) T] x)] := eq_refl.

Fail Example R1 (x : X) :
  fobj[EM_Comparison Adj ◯ F] x = fobj[@EM_Free X (G ◯ F) T] x := eq_refl.

Example C3 (a : A) :
  `1 (fobj[EM_Comparison_via_Lemma Adj] a) = `1 (fobj[EM_Comparison Adj] a)
  := eq_refl.

Fail Example R2a (a : A) :
  t_alg[`2 (fobj[EM_Comparison_via_Lemma Adj] a)]
    = t_alg[`2 (fobj[EM_Comparison Adj] a)] := eq_refl.

Fail Example R2 (a : A) :
  fobj[EM_Comparison_via_Lemma Adj] a = fobj[EM_Comparison Adj] a := eq_refl.

Example C4 (a : A) :
  fobj[EM_Forget (G ◯ F) ◯ EM_Comparison_via_Lemma Adj] a = fobj[G] a
  := eq_refl.

Fail Example R3 (x : X) :
  fmap[EM_Forget (G ◯ F)] (to (`1 (EM_Comparison_Free Adj) x))
    ∘ from (`1 (EM_Comparison_Forget Adj) (F x))
    = transform[mh_transform (to (EM_Comparison_theta Adj))] x := eq_refl.

Example C5 (x : X) :
  fmap[EM_Forget (G ◯ F)] (to (`1 (EM_Comparison_Free Adj) x))
    ∘ from (`1 (EM_Comparison_Forget Adj) (F x))
    = id ∘ id := eq_refl.

(* Restatements. / 重述。 *)

Example C6 (x : X) :
  transform[mh_transform (to (EM_Comparison_theta Adj))] x = id := eq_refl.

Example C7 (a : A) :
  `1 (EM_Comparison_Forget Adj) a = iso_id := eq_refl.

Example C8 (x : X) :
  `1 (EM_Comparison_Free Adj) x = EM_Comparison_Free_iso Adj x := eq_refl.

End EMProbe.

Section MonadProbe.

Context {X : Category} (T : X ⟶ X) `{H : @Monad X T}.

Example C9 (x : X) :
  transform[mh_transform (to (@EM_Monad_iso X T H))] x = id := eq_refl.

Example C10 (x : X) :
  transform[mh_transform (from (@EM_Monad_iso X T H))] x = id := eq_refl.

End MonadProbe.

Section LemmaProbe.

(* The object and hom levels of [Monads X], kept apart as in the target. / [Monads X] 的对象和同源水平，像在目标中一样分开。 *)
Universes m1 m2.

Context {X : Category}.
Context {A : Category} {F : X ⟶ A} {G : A ⟶ X} (Adj : F ⊣ G).
Context {A' : Category} {F' : X ⟶ A'} {G' : A' ⟶ X} (Adj' : F' ⊣ G').
Context (θ : @Isomorphism (Monads@{_ _ m1 m2} X)
               (G' ◯ F'; Adjunction_Induced_Monad Adj')
               (G ◯ F; Adjunction_Induced_Monad Adj)).
Context (CR : CreatesUSplitCoequalizers G).
Context (P : Comparison Adj Adj' θ).

Example C11 :
  wsq_K (wmap_squares Adj' Adj (Comparison_map Adj Adj' θ P))
    = cmp_functor Adj Adj' θ P := eq_refl.

Example C12 :
  wsq_L (wmap_squares Adj' Adj (Comparison_map Adj Adj' θ P)) = Id[X]
  := eq_refl.

Example C13 (a : A') : `1 (fobj[Comparison_alg Adj Adj' θ] a) = G' a
  := eq_refl.

Example C14 (a : A') :
  t_alg[`2 (fobj[Comparison_alg Adj Adj' θ] a)]
    = fmap[G'] (@counit _ _ _ _ Adj' a)
        ∘ transform[mh_transform (from θ)] (G' a) := eq_refl.

Example C15 (a : A') :
  fobj[Comparison_functor Adj Adj' θ CR] a
    = beck_G_obj Adj CR (fobj[Comparison_alg Adj Adj' θ] a) := eq_refl.

Example C16 (a : A') :
  to (`1 (Comparison_right Adj Adj' θ CR) a)
    = beck_to Adj CR (fobj[Comparison_alg Adj Adj' θ] a) := eq_refl.

Example C17 (a : A') :
  from (`1 (Comparison_right Adj Adj' θ CR) a)
    = fmap[G] (beck_e Adj CR (fobj[Comparison_alg Adj Adj' θ] a))
        ∘ @unit _ _ _ _ Adj (G' a) := eq_refl.

End LemmaProbe.

(* ------------------------------------------------------------------------ *)
(** ** The positive controls of Instance/Fun/Action/Monad/Comparison.v / ** Instance/Fun/Action/Monad/Comparison.v 的阳性对照 *)

(*
Required here, after every other command above, so that the sections
   above are elaborated under the first target's import list alone: the
   import list of Instance/Fun/Action/Monad/Comparison.v, in its order,
   and that module.

--------
在这里，在上面每个其他命令之后都是必需的，以便上面的各部分只在第一个目标的导入列表下进行详细说明：即 Instance/Fun/Action/Monad/Comparison.v 的导入列表，按其顺序，以及该模块。
*)
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.Action.
Require Import Category.Instance.Fun.Action.Monad.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Kleisli.
Require Import Category.Monad.Kleisli.Adjunction.
Require Import Category.Monad.Comparison.Resolution.
Require Import Category.Instance.Fun.Action.Monad.Comparison.

(*
C18: at the adjunction of LZ-sets, [EM_Comparison] satisfies the first
   hypothesis that [bare_awodey_refuted] quantifies over.

--------
C18：在 LZ 集的连接处，[EM_Comparison] 满足 [bare_awodey_refuted] 量化的第一个假设。
*)
Example C18 :
  EM_Forget (ActF LZ) ◯ EM_Comparison (MSet_adj LZ) ≈ MSet_Forget LZ :=
  EM_Comparison_Forget (MSet_adj LZ).

(* C19: and the second. / C19：还有第二个。 *)
Example C19 :
  EM_Comparison (MSet_adj LZ) ◯ MSet_Free LZ ≈ EM_Free (ActF LZ) :=
  EM_Comparison_Free (MSet_adj LZ).

(* C20: a comparison over the identity identification exists there. / C20：在那里存在关于身份识别的比较。 *)
Definition C20 :
  Comparison (@EM_Adjunction Sets (ActF LZ) (ActMonad LZ)) (MSet_adj LZ)
    (EM_Comparison_theta (MSet_adj LZ)) :=
  EM_Comparison_Comparison (MSet_adj LZ).

(* C21: and the Lemma's uniqueness applies to it. / C21：引理的唯一性适用于它。 *)
Definition C21 : cmp_functor _ _ _ C20 ≈ EM_Comparison (MSet_adj LZ) :=
  EM_Comparison_unique (MSet_adj LZ) C20.

(* C22: [K_forget_components] restated. / C22：[K_forget_components] 重申。 *)
Example C22 (A : MSetoidAction LZ) : `1 K_forget A = iso_id := eq_refl.

(* C23: [theta_sigma_component] restated. / C23：[theta_sigma_component] 重申。 *)
Example C23 (X : SetoidObject) :
  transform[mh_transform (to theta_sigma)] X = lz_swap_first X := eq_refl.
