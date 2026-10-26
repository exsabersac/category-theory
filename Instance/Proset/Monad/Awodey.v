Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Monad.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(* * * Awodey's adjunction from a closure operator / * * Awodey 的闭包算子的伴随 *)

(*
 nLab: https://ncatlab.org/nlab/show/closure+operator
 Book: Awodey, “Category Theory” (1st ed., CMU pre-print, Sept 2005),
 SS 10.2, printed p. 271, the unnumbered construction after
 Example 10.4
 Book: Fong and Spivak, “Seven Sketches in Compositionality”, arXiv v3,
 SS 1.4.4, Example 1.122, printed p. 34

 Awodey, p. 271: “In the poset case, we can easily recover an
 adjunction from the monad.  First, let K = im(T)(P) (the fixed points
 of T), and let i : K → P be the inclusion.  Then let t be the
 factorization of T through K ...  Observe that since TTp = Tp, for any
 element k ∈ K we then have, for some p ∈ P, the equation
 itik = ititp = itp = ik, whence tik = k since i is monic.  We therefore
 have: p ≤ ik implies tp ≤ tik = k; tp ≤ k implies p ≤ itp ≤ ik.  So
 indeed t ⊣ i.”  Seven Sketches' Example 1.122 builds the same
 adjunction on a preorder, with fix_j = {p | j(p) ≅ p}.

 WHAT IS BUILT.  For a closure operator [c] on a PREORDER
 (Instance/Proset/Monad.v's [ClosureOperator]), K is [ClosedElt c], the
 elements x with cl x ≤ x, ordered as in P ([closed_le],
 [closed_PreOrder]).  [closed_t] sends x to cl x, whose membership proof
 is the field [cl_mult] itself, and [closed_i] is the first projection.
 Awodey's two displayed implications are the unit [cl_ext] and the
 counit (the membership proof) fed to Instance/Proset/Galois.v's
 [galois_of_unit_counit], which gives the Galois connection
 [closed_galois]; [closed_adj] is its [GaloisAdjunction], t ⊣ i between
 the thin categories.

 WHICH K.  Awodey writes K = im(T) and calls it the fixed points.  Over
 a preorder the image, the fixed points and the closed elements agree
 only up to ≅: every cl p is closed ([cl_mult]), and every closed k is
 isomorphic to cl k ([closed_tik_iso]).  The file takes the closed
 elements, which is Seven Sketches' fix_j (j p ≅ p holds exactly when
 j p ≤ p, extensivity giving the other half), because membership is
 then a single inequality with a canonical witness, where the image
 would carry an existential.

 “tik = k SINCE i IS MONIC”.  Awodey's i is monic as a map of posets,
 that is, injective, and cancelling it turns i t i k = i k into
 t i k = k.  Over a preorder neither step survives: i t i k is cl k,
 which is only isomorphic to k, and i = proj1_sig identifies two
 elements of K only when their membership proofs are identified, which
 is proof irrelevance.  What holds is: the first component of t (i k)
 is cl k by [eq_refl] ([closed_tik_fst]); t (i k) ≅ k in the order of
 K ([closed_tik_iso]); and under an explicit [Antisymmetric] hypothesis
 the first components are equal
 ([closed_tik_eq]).  The equation t (i k) = k itself is refused by
 conversion: the first components are cl k and k, and the second are
 proofs of a [Prop], which are identified only under proof
 irrelevance, not assumed here.  Awodey's argument is for a poset,
 where his K and the closed elements coincide as sets; this file
 records what survives over a preorder.

 THE INDUCED MONAD IS T.  On objects and on arrows T = i ∘ t by
 [eq_refl] ([closed_factorisation_obj], [closed_factorisation_fmap]).
 The monad induced by t ⊣ i (Monad/Comparison.v's
 [Adjunction_Induced_Monad]), read back through
 Instance/Proset/Monad.v's [closure_of_monad], has a monotone map EQUAL
 to c's, as a whole [MonotoneFun], by [eq_refl] ([closed_induced_is_c]):
 the order-level form of Construction/Reflective/Idempotent/Induced.v.
 As functors, i ◯ t ≈ [closure_functor c] with identity components
 ([closed_induced_functor]).  Awodey does not say in words that the
 adjunction induces T; the construction makes it so, and these are the
 readbacks.  The route through Idempotent.v, with K the M-local
 subcategory, is Instance/Proset/Monad.v's [proset_fixed_adj].

 STRENGTHS, measured.  [eq_refl]: [closed_factorisation_obj],
 [closed_factorisation_fmap], [closed_induced_is_c] (the whole monotone
 map), [closed_tik_fst].  At ≈ or ≅ only, each with its [=] refused by
 conversion in a stripped copy: the functor equation
 i ◯ t = [closure_functor c], whose [fobj] and [fmap] agree by
 [eq_refl] (the two Examples above), so that the refusal sits in the
 law fields.  Flipped first, in a copy of the 55-file dependency closure:
 with [Compose]'s two proved obligations and [Functor_of_monotone]'s
 three made [Defined], and Instance/Proset.v and Galois.v compiled with
 transparent obligations, it is still refused.  The composite's
 [fmap_respects] and [fmap_comp] then reduce to terms stuck on the
 stdlib's opaque [CMorphisms.trans_co_eq_inv_arrow_morphism_obligation_1],
 left by the setoid rewriting in [Compose]'s proofs, and its [fmap_id]
 on [Compose]'s automatically solved obligation, whose transparency
 breaks a proof script of Structure/Limit/Preservation.v.  So ≈ is the
 strongest available short of re-proving [Compose].  Also refused: the
 WHOLE closure-operator record read back from the induced monad, whose
 two proof fields reduce to c's own [cl_ext] and [cl_mult] each
 composed with a reflexivity by the transitivity of P (the composites
 made by [galois_of_unit_counit]); P is a variable, so no flip can
 identify them with c's.  And t (i k) = k, above.

 UNIVERSES, read off [About].  [ClosedElt@{u}] lives in [Type@{u}].
 Every constant that projects out of the subset type carries the cap
 [u <= Subset_projections.u0] of the stdlib's [proj1_sig], first used by
 [closed_le].  [closed_adj@{u h s a}] has [h < s], introduced by
 Instance/Sets.v's [Sets] ([o < so]) where the hom-setoid isomorphism of
 [Adjunction] lives, and [a] is a level of [GaloisAdjunction] free in
 its block.  [closed_induced_is_c] pins the adjunction to
 [closed_adj@{u h s a}]: unpinned, the adjunction took fresh levels and
 the declared [h] occurred nowhere in the statement (measured by a check
 of every instance level against the printed type).  The composites add
 Theory/Functor.v's [Compose] bound ([u3 < u2]) and the ≈ its
 [Functor_Setoid] bound; each is unified into one strict level per
 constant.  [closed_adj] and [closed_induced_is_c] also carry the
 stdlib caps [h <= compose.u0, compose.u1, compose.u2, ID.u0], first
 carried by [Sets] ([Sets@{o so}] has them at its level o) through
 [Adjunction].  No level occurs only in a body, and no constant carries
 [Set].  Both copies of [Thin] are loaded here (Structure/Thin.v through
 Instance/Proset/Monad.v, and Instance/Proset/Galois.v directly); this
 file names neither.

 NOT DELIVERED.  No comparison between [ClosedElt c] and the M-local
 subcategory of the other route beyond both being reflective with the
 same T; no identification of K with the image of T as a set; no
 whole-record identification of the induced closure operator with c,
 which is refused as above; and no interior-operator dual of this
 order-theoretic construction (the coreflection onto the open elements
 is Instance/Proset/Monad/Interior.v's [proset_open_coreflective],
 through Structure/Thin/Monad.v). 

 --------
 nLab: https://ncatlab.org/nlab/show/closure+operator
 书籍: Awodey, 《范畴论》(第一版, CMU 预印本, 2005年9月),
 第10.2节, 印刷页 271, 示例10.4之后未编号的构造
 书籍: Fong 和 Spivak, 《组合性七个草图》, arXiv 第3版,
 第1.4.4节, 示例1.122, 印刷页 34Awodey，第271页：“在偏序集的情况下，我们可以很容易地从单子中恢复一个伴随。首先，设 K = im(T)(P)（T 的不动点），并让 i : K → P 为包含映射。然后让 t 是通过 K 对 T 的分解……注意，由于 TTp = Tp，对于任意元素 k ∈ K，我们有，对于某个 p ∈ P，方程 itik = ititp = itp = ik，因此 tik = k，因为 i 是单射。因此我们有：p ≤ ik 蕴含 tp ≤ tik = k；tp ≤ k 蕴含 p ≤ itp ≤ ik。因此实际上 t ⊣ i。” Seven Sketches 的示例 1.122 在一个预序上构建了相同的伴随，fix_j = {p | j(p) ≅ p}.构建的内容。对于前序 (Instance/Proset/Monad.v 的 [ClosureOperator]) 上的闭包算子 [c]，K 是 [ClosedElt c]，即满足 cl x ≤ x 的元素 x，按 P([closed_le], [closed_PreOrder]) 中的顺序排列。[closed_t] 将 x 映射为 cl x，其成员资格证明是字段 [cl_mult] 本身，而 [closed_i] 是第一个投影。Awodey 展示的两个蕴涵是单元 [cl_ext] 和作为 Instance/Proset/Galois.v 的输入的余单位（成员资格证明） [galois_of_unit_counit]，后者给出了 Galois 连接 [closed_galois]；[closed_adj] 是其 [GaloisAdjunction]，即薄范畴之间的 t ⊣ i。WHICH K。Awodey 写道 K = im(T) 并称其为不动点。在一个预序中，像、不动点和封闭元只在 ≅ 下相同：每个 cl p 都是封闭的（[cl_mult]），每个封闭的 k 与 cl k 同构（[closed_tik_iso]）。该文件采用封闭元，即 Seven Sketches 的 fix_j（当 j p ≤ p 时 j p ≅ p 正好成立，扩展性给出另一半），因为此时成员关系只是带有一个典型证明对象的单个不等式，而像会涉及存在量词。“tik = k 因为 i 是单射”。Awodey 的 i 作为偏序集的映射是单射的，即注入的，并且取消它将 i t i k = i k 转化为 t i k = k。在前序集上，这两个步骤都不成立：i t i k 是 cl k，而 cl k 仅与 k 同构，并且 i = proj1_sig 仅在 K 的两个元素的成员资格证明被识别时才识别它们，这就是证明无关性。成立的是：t (i k) 的第一分量是 cl k（参见 [eq_refl]（[closed_tik_fst]））；t (i k) 在 K 的顺序中与 k 同构（参见 [closed_tik_iso]）；并且在显式的 [Antisymmetric] 假设下，第一分量是相等的（参见 [closed_tik_eq]）。方程 t (i k) = k 本身被转换拒绝：第一分量是 cl k 与 k，第二分量是 [Prop] 的证明，这些证明仅在证明无关性下才被识别，而此处未假设。Awodey 的论证针对的是一个偏序集，其中他的 K 与闭合集合作为集合是重合的；这个文件记录了在预序中的情况。

 诱导的单子是 T。在对象和箭头上，T = i ∘ t，根据 [eq_refl]（[closed_factorisation_obj]，[closed_factorisation_fmap]）。
 由 t ⊣ i（Monad/Comparison.v 的 [Adjunction_Induced_Monad]）诱导的单子，通过 Instance/Proset/Monad.v 的 [closure_of_monad] 读回，具有与 c 的单调映射 EQUAL，作为整体 [MonotoneFun]，根据 [eq_refl]（[closed_induced_is_c]）：这是 Construction/Reflective/Idempotent/Induced.v 的序层形式。
 作为函子，i ◯ t ≈ [closure_functor c] 且具有恒等分量（[closed_induced_functor]）。Awodey 没有用文字说明伴随关系诱导了 T；这个构造使得如此，并且这些是读回结果。通过 Idempotent.v，K 为 M-局部子范畴的路径是 Instance/Proset/Monad.v 的 [proset_fixed_adj]。优势，已测量。[eq_refl]：[closed_factorisation_obj]，[closed_factorisation_fmap]，[closed_induced_is_c]（整个单调映射），[closed_tik_fst]。仅在≈或≅时，每个都有其被剥离副本中拒绝转换的[=]：函子方程i ◯ t = [closure_functor c]，其[fobj]和[fmap]通过[eq_refl]（上面两个例子）一致，因此拒绝存在于定律字段中。首先翻转，在一个55文件依赖闭包的副本中：带有[Compose]的两个已证明义务和[Functor_of_monotone]的三个生成[Defined]，以及Instance/Proset.v和Galois.v使用透明义务编译，它仍然被拒绝。该复合体的 [fmap_respects] 和 [fmap_comp] 然后简化为卡在 stdlib 的不透明 [CMorphisms.trans_co_eq_inv_arrow_morphism_obligation_1] 上的项，由 [Compose] 的证明中的集等价重写留下，以及 [Compose] 的自动解决义务上的 [fmap_id]，其透明性破坏了 Structure/Limit/Preservation.v 的证明脚本。因此 ≈ 是在不重新证明 [Compose] 的情况下可用的最强形式。也被拒绝的是：从诱导单子读回的整个闭包算子记录，其两个证明字段分别简化为 c 自己的 [cl_ext] 和 [cl_mult]，每个都通过 P 的传递性与自反性组合（这些复合项由 [galois_of_unit_counit] 生成）；P 是一个变量，因此没有翻转可以将它们与 c 的标识。上面的 t (i k) = k。宇宙，读取 [About]。[ClosedElt@{u}] 生活在 [Type@{u}]。每个从子集类型投射出的常量都携带 stdlib 的 [proj1_sig] 的帽 [u <= Subset_projections.u0]，首次由 [closed_le] 使用。[closed_adj@{u h s a}] 拥有 [h < s]，由 Instance/Sets.v 的 [Sets]（[o < so]）引入，其中 [Adjunction] 的同值集同构存在，并且 [a] 是 [GaloisAdjunction] 在其块中自由的一个层次。[closed_induced_is_c] 将伴随固定到 [closed_adj@{u h s a}]：未固定时，伴随获取了新的层次，并且声明的 [h] 在语句中未出现（通过检查每个实例层次与打印类型对比进行测量）。复合项添加了 Theory/Functor.v 的 [Compose] 绑定（[u3 < u2]）及其 [Functor_Setoid] 绑定的 ≈；每个常量都统一为一个严格层次。[closed_adj] 和 [closed_induced_is_c] 也包含了 stdlib 的 [h <= compose.u0, compose.u1, compose.u2, ID.u0]，这最初由 [Sets] 携带（[Sets@{o so}] 在其层级 o 上拥有它们）通过 [Adjunction]。没有任何层级仅出现在一个主体中，并且没有常量携带 [Set]。[Thin] 的两个副本都在这里加载（从 Structure/Thin.v 到 Instance/Proset/Monad.v，以及直接从 Instance/Proset/Galois.v）；此文件都未命名它们。未交付。没有将 [ClosedElt c] 与另一条路径的 M-本地子类进行比较，除了它们都是具有相同 T 的反射；没有将 K 与 T 的像作为集合进行识别；没有将诱导闭包算子与 c 的整个记录进行识别，如上文所拒绝；也没有该序理论构造的内算子对偶（对开元素的余反射是 Instance/Proset/Monad/Interior.v 的 [proset_open_coreflective]，通过 Structure/Thin/Monad.v）。
*)

(* * ** The closed elements, with the inherited order / * ** 闭合元素，具有继承的顺序 *)

(* K: the elements with cl x ≤ x, i.e. Seven Sketches' fix_j. / K: 元素满足 cl x ≤ x，即 Seven Sketches 的 fix_j。 *)
Definition ClosedElt@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (c : ClosureOperator@{u} P) : Type@{u} :=
  { x : A | R (cl_fun c x) x }.

Definition closed_le@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (c : ClosureOperator@{u} P) : relation (ClosedElt c) :=
  fun a b => R (proj1_sig a) (proj1_sig b).

Definition closed_PreOrder@{u} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) : PreOrder (closed_le c) :=
  {| PreOrder_Reflexive  := fun a => @PreOrder_Reflexive A R P (proj1_sig a)
   ; PreOrder_Transitive := fun a b d (H1 : closed_le c a b)
                                (H2 : closed_le c b d) =>
       @PreOrder_Transitive A R P _ _ _ H1 H2 |}.

(** ** Awodey's t and i / ** Awodey 的 t 和 i *)

(* t : P → K, the factorisation of cl through K. / t : P → K，通过 K 的 cl 的分解。 *)
Definition closed_t@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (c : ClosureOperator@{u} P) (x : A) : ClosedElt c :=
  exist _ (cl_fun c x) (cl_mult c x).

(* i : K → P, the inclusion. / i : K → P，包含映射。 *)
Definition closed_i@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (c : ClosureOperator@{u} P) (k : ClosedElt c) : A :=
  proj1_sig k.

(* Awodey's two implications, as the unit and counit inequalities. / 阿沃迪的两个含义，作为单位和余单位不等式。 *)
Definition closed_galois@{u} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  GaloisConnection R (closed_le c) :=
  galois_of_unit_counit P (closed_PreOrder c) (closed_t c) (closed_i c)
    (fun a a' h => mono_pres (cl_fun c) a a' h)
    (fun b b' h => h)
    (fun a => cl_ext c a)
    (fun b => proj2_sig b).

(* t ⊣ i. *)
Definition closed_adj@{u h s a | h < s +} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (c : ClosureOperator@{u} P) :=
  GaloisAdjunction@{u u s a h} P (closed_PreOrder c) (closed_galois c).

(* * ** T = i ∘ t, and the induced monad is T / * ** T = i ∘ t，且诱导的幺半群是 T *)

(* T = i ∘ t on objects, on the nose. / T = i ∘ t 在对象上，完全如此。 *)
Example closed_factorisation_obj@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) (x : A) :
  fobj[GaloisFunctor_r@{u u h} P (closed_PreOrder c) (closed_galois c)
       ◯ GaloisFunctor_l@{u u h} P (closed_PreOrder c) (closed_galois c)] x
    = cl_fun c x := eq_refl.

(* ...and on arrows, so that i ◯ t = [closure_functor c] is refused in the law fields alone. / ...以及在箭头上，因此我 ◯ t = [closure_functor c] 只在法律领域被拒绝。 *)
Example closed_factorisation_fmap@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) (x y : A) (f : R x y) :
  fmap[GaloisFunctor_r@{u u h} P (closed_PreOrder c) (closed_galois c)
       ◯ GaloisFunctor_l@{u u h} P (closed_PreOrder c) (closed_galois c)] f
    = fmap[closure_functor@{u h} c] f := eq_refl.

(*
 The induced monad, read back as a closure operator, has c's monotone
 map on the nose. 

 --------
 诱导的幺半群，被回读为闭包算子，正好具有 c 的单调映射。
*)
Example closed_induced_is_c@{u h s a | h < s +} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (c : ClosureOperator@{u} P) :
  cl_fun (closure_of_monad _
            (MM := Adjunction_Induced_Monad (closed_adj@{u h s a} c)))
    = cl_fun c := eq_refl.

(* i ◯ t is the closure functor, with identity components. / i ◯ t 是闭包函子，具有恒等分量。 *)
Lemma closed_induced_functor@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  GaloisFunctor_r@{u u h} P (closed_PreOrder c) (closed_galois c)
    ◯ GaloisFunctor_l@{u u h} P (closed_PreOrder c) (closed_galois c)
    ≈ closure_functor@{u h} c.
Proof. exists (fun x => iso_id). intros; exact I. Qed.

(* * ** “tik = k”: up to ≅, and on first projections under antisymmetry / * ** “tik = k”：至 ≅，以及在反对称性下的第一投影上 *)

(* t (i k) has first component cl k... / t (i k) 的第一个分量是 cl k... *)
Example closed_tik_fst@{u} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) (k : ClosedElt c) :
  proj1_sig (closed_t c (closed_i c k)) = cl_fun c (proj1_sig k)
  := eq_refl.

(* ...and is isomorphic to k in K... / ...并且在 K 中与 k 同构... *)
Definition closed_tik_iso@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) (k : ClosedElt c) :
  closed_t c (closed_i c k) ≅[Proset@{u h} (closed_PreOrder c)] k :=
  @Build_Isomorphism (Proset@{u h} (closed_PreOrder c))
    (closed_t c (closed_i c k)) k (proj2_sig k) (cl_ext c (proj1_sig k)) I I.

(* ...and equal to k on first components under antisymmetry. / ...并且在反对称性下在第一分量上等于 k。 *)
Lemma closed_tik_eq@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (AS : @Antisymmetric A eq eq_equiv R) (c : ClosureOperator@{u} P)
  (k : ClosedElt c) :
  proj1_sig (closed_t c (closed_i c k)) = proj1_sig k.
Proof. exact (AS _ _ (proj2_sig k) (cl_ext c (proj1_sig k))). Qed.
