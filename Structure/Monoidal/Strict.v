Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(*
   * * Strict monoidal categories

   nLab: https://ncatlab.org/nlab/show/strict+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category#Strict_monoidal_category

   A strict monoidal category is a monoidal category in which the
   associator and unitors are identity natural transformations —
   equivalently, where the tensor is strictly associative and strictly
   unital on objects, not merely up to coherent isomorphism.

   In this library's setoid-based setting, "strict" requires BOTH:

   (a) object-level Leibniz equalities
   [(X ⨂ Y) ⨂ Z = X ⨂ (Y ⨂ Z)],
   [I ⨂ X = X = X ⨂ I];
   (b) the structural isomorphisms [tensor_assoc], [unit_left],
   [unit_right] coincide (modulo those equalities) with [id].

   Object-level equality (Leibniz [=]) is required because [obj] in
   [Category] is a [Type], not a setoid; the monoidal coherence
   isomorphisms relate distinct objects (e.g. [(X ⨂ Y) ⨂ Z] and
   [X ⨂ (Y ⨂ Z)]).  In a strict monoidal category, those objects
   coincide on the nose.

   The structural isomorphisms then transport along those equalities
   to give [id].  We use the explicit [match … in _ = T return …]
   form (Coq's primitive dependent elimination on equality), rather
   than the [rew]/[eq_rect] notation, which the library's [_CoqProject]
   does not pull in.  See the "Formulation note" at the end of the file
   for the rationale; both the [strict_*_to] fields and the derived
   [strict_*_from] corollaries use the [match] form consistently.

   Strict monoidal categories are precisely monoid objects in the
   cartesian monoidal category [Cat].  PROPs are strict symmetric
   monoidal categories whose objects are the natural numbers under
   [+]; this class is the foundation for the upcoming PROP
   machinery. 

   --------
   * * 严格单类范畴

   nLab:  https://ncatlab.org/nlab/show/strict+monoidal+category 
   维基百科:  https://en.wikipedia.org/wiki/Monoidal_category#Strict_monoidal_category 

   严格单类范畴是一个单类范畴，其中关联子和单位子是恒等自然变换——
   等价地说，在对象上张量是严格结合的和严格单位的，而不仅仅是通过相干同构成立。

   在该库基于集合类（setoid-based）的设定中，“严格”要求如下两者：

   (a) 对象层面的莱布尼茨等式
   [(X ⨂ Y) ⨂ Z = X ⨂ (Y ⨂ Z)] ,
   [I ⨂ X = X = X ⨂ I] ;
   (b) 结构同构 [tensor_assoc] , [unit_left] ,
   [unit_right] 在这些等式意义下与 [id] 一致。对象级别的相等性（Leibniz [=]）是必要的，因为在 [Category] 中的 [obj] 是一个 [Type]，而不是集合范畴；幺半群的相容同构关联不同的对象（例如 [(X ⨂ Y) ⨂ Z] 和 [X ⨂ (Y ⨂ Z)]）。在严格的幺半群范畴中，这些对象完全一致。

   然后，结构同构沿着这些相等性传输以生成 [id]。我们使用显式的 [match … in _ = T return …] 形式（Coq 对相等性的原生依赖消去），而不是 [rew] / [eq_rect] 符号，因为库中的 [_CoqProject] 并未引入这些符号。有关理由，请参见文件结尾的“表述说明”；[strict_*_to] 字段和派生的 [strict_*_from] 推论都一致地使用 [match] 形式。严格单范畴恰好是笛卡尔单范畴 [Cat] 中的幺半群对象。PROP 是严格对称单范畴，其对象是在 [+] 下的自然数；这一类是即将介绍的 PROP 机制的基础。
*)

Section StrictMonoidal.

Context {C : Category}.

Class StrictMonoidal : Type := {
  strict_is_monoidal : @Monoidal C;

  (** Object-level strictness. / 对象级严格性。 *)
  strict_assoc_obj :
    forall (X Y Z : C),
      ((X ⨂[strict_is_monoidal] Y)%object ⨂[strict_is_monoidal] Z)%object
      = (X ⨂[strict_is_monoidal] (Y ⨂[strict_is_monoidal] Z)%object)%object;

  strict_unit_left_obj :
    forall (X : C),
      (I ⨂[strict_is_monoidal] X)%object = X;

  strict_unit_right_obj :
    forall (X : C),
      (X ⨂[strict_is_monoidal] I)%object = X;

  (*
   * The structural isomorphisms ARE the identity, transported.

   We use the [match] form (rather than [eq_rect]) to keep
   destruct-of-equality reductions clean. 

   --------
   * 结构同构就是传递后的恒等映射。

   我们使用 [match] 形式（而不是 [eq_rect]），以保持等式析构化的约简干净。
*)
  strict_assoc_to :
    forall (X Y Z : C),
      to (@tensor_assoc C strict_is_monoidal X Y Z)
      ≈ match strict_assoc_obj X Y Z in _ = T
          return ((X ⨂[strict_is_monoidal] Y)%object
                   ⨂[strict_is_monoidal] Z)%object ~> T
        with eq_refl => id end;

  strict_unit_left_to :
    forall (X : C),
      to (@unit_left C strict_is_monoidal X)
      ≈ match strict_unit_left_obj X in _ = T
          return (I ⨂[strict_is_monoidal] X)%object ~> T
        with eq_refl => id end;

  strict_unit_right_to :
    forall (X : C),
      to (@unit_right C strict_is_monoidal X)
      ≈ match strict_unit_right_obj X in _ = T
          return (X ⨂[strict_is_monoidal] I)%object ~> T
        with eq_refl => id end
}.
#[export] Existing Instance strict_is_monoidal.

Coercion strict_is_monoidal : StrictMonoidal >-> Monoidal.

(*
   * ** Corollaries

   In a strict monoidal category the [from] direction of each
   structural iso is also the transported identity. 

   --------
   * ** 推论

   在严格的单元范畴中，每个结构同构的 [from] 方向也是被传递的恒等映射。
*)

Context `{S : StrictMonoidal}.

(*
 A sanity-check corollary: in any strict monoidal category, the
 composite [α ∘ α⁻¹] at any triple is [id] (which is just
 [iso_to_from] specialised — we restate it here as a flat lemma
 using the strict-shape so downstream code can use it without
 going through [tensor_assoc]'s iso projections).  The closed-form
 [from] direction of each structural iso (the transported identity
 along the symmetric equality) is given by the [strict_*_from]
 corollaries below. 

 --------
 理智检查推论：在任何严格的幺半范畴中，任意三元组处的复合  [α ∘ α⁻¹]  是  [id] （这只是 [iso_to_from] 的特化——我们在此将其重新表述为一个扁平引理，使用严格形状，以便下游代码可以在不经过 [tensor_assoc] 的同构投影的情况下使用它）。每个结构同构的闭合形式方向（沿对称等式传递的恒等映射）由下面的 [strict_*_from] 推论给出。
*)
Lemma strict_assoc_iso (X Y Z : C) :
  to (@tensor_assoc C strict_is_monoidal X Y Z)
    ∘ from (@tensor_assoc C strict_is_monoidal X Y Z)
  ≈ id.
Proof. apply iso_to_from. Qed.

(*
   * ** Closed-form [from] corollaries

   The [from] direction of each structural isomorphism is, like its
   [to] direction, the transported identity — but transported along the
   SYMMETRIC equality (so that the domain and codomain of the resulting
   morphism are swapped).

   The phrasing uses a single match-and-return-on-the-domain (rather
   than a doubly-dependent [a ~> b]).  Concretely, given
   [e : a = b], the morphism [b ~> a] is given by
   [match e in _ = T return T ~> a with eq_refl => id end]:
   at [eq_refl], [T = b] reduces to [a] by elimination, and the branch
   [id : a ~> a] inhabits the resulting type. 

   --------
   * ** 闭式 [from] 推论

   每个结构同构的 [from] 方向，就像其 [to] 方向一样，是被传递的恒等映射——但是沿着对称等式传递（因此生成的态射的定义域和余域被交换）。

   这种表述使用了单一的在定义域上的匹配并返回（而不是双依赖的 [a ~> b]）。具体来说，给定 [e : a = b]，态射 [b ~> a] 由 [match e in _ = T return T ~> a with eq_refl => id end] 给出：
   在 [eq_refl]，[T = b] 通过消解简化为 [a]，分支 [id : a ~> a] 属于生成的类型。
*)

(*
   * A general lemma: given an iso [phi : a ≅ b] and an equality [e : a = b]
   such that [to phi] equals the transported identity along [e], the
   [from phi] equals the transported identity along [e] in the other
   direction.

   This is purely group-theoretic — once you know [to phi] is "id along
   e", uniqueness of inverses in [Isomorphism] forces [from phi] to be
   "id along the symmetric e". 

   --------
   * 一个通用引理：给定一个同构  [phi : a ≅ b]  和一个等式  [e : a = b] ，
   使得  [to phi]  等于沿着  [e]  传递的恒等映射，
   则  [from phi]  等于沿着  [e]  在另一个方向上传递的恒等映射。

   这完全是群论的 —— 一旦你知道  [to phi]  是“沿着 e 的恒等映射”，
   [Isomorphism]  中逆元的唯一性就会迫使  [from phi]  是“沿着对称 e 的恒等映射”。
*)
Lemma transported_iso_from
  {C' : Category} {a b : C'} (e : a = b) (phi : a ≅[C'] b)
  (Hto : to phi ≈ match e in _ = T return a ~> T with eq_refl => id end) :
  from phi ≈ match e in _ = T return T ~> a with eq_refl => id end.
Proof.
  pose proof (iso_to_from phi) as Htf.
  rewrite Hto in Htf.
  destruct e.
  simpl in Htf |- *.
  rewrite id_left in Htf.
  exact Htf.
Qed.

Lemma strict_assoc_from (X Y Z : C) :
  from (@tensor_assoc C strict_is_monoidal X Y Z)
  ≈ match strict_assoc_obj X Y Z in _ = T
      return T ~> ((X ⨂[strict_is_monoidal] Y)%object
                    ⨂[strict_is_monoidal] Z)%object
    with eq_refl => id end.
Proof.
  apply (transported_iso_from
           (strict_assoc_obj X Y Z)
           (@tensor_assoc C _ X Y Z)).
  apply strict_assoc_to.
Qed.

Lemma strict_unit_left_from (X : C) :
  from (@unit_left C strict_is_monoidal X)
  ≈ match strict_unit_left_obj X in _ = T
      return T ~> (I ⨂[strict_is_monoidal] X)%object
    with eq_refl => id end.
Proof.
  apply (transported_iso_from
           (strict_unit_left_obj X)
           (@unit_left C _ X)).
  apply strict_unit_left_to.
Qed.

Lemma strict_unit_right_from (X : C) :
  from (@unit_right C strict_is_monoidal X)
  ≈ match strict_unit_right_obj X in _ = T
      return T ~> (X ⨂[strict_is_monoidal] I)%object
    with eq_refl => id end.
Proof.
  apply (transported_iso_from
           (strict_unit_right_obj X)
           (@unit_right C _ X)).
  apply strict_unit_right_to.
Qed.

End StrictMonoidal.

(*
   * ** Formulation note

   The library does not import the [rew] notation (Coq's [eq_rect]
   sugar in [stdpp] / [Init.Logic]) by default — its [_CoqProject]
   does not pull it in.  The explicit [match … in _ = T return …]
   form parses cleanly inside record fields, and combined with
   [destruct]-of-equality the dependent transport reduces by
   [eq_refl] elimination just as cleanly as the [rew] form does in
   libraries that import the notation.  Both [strict_*_to] and the
   derived [strict_*_from] corollaries use the [match] formulation
   consistently. 

   --------
   * ** 公式说明

   库默认不导入 [rew] 符号（Coq 在 [stdpp] / [Init.Logic] 中的 [eq_rect] 语法糖）——它的 [_CoqProject] 不会自动引入。显式的 [match … in _ = T return …] 形式在记录字段中解析得很干净，并且结合 [destruct] -of-equality，依赖传输通过 [eq_refl] 消去就像在导入该符号的库中 [rew] 形式一样干净。[strict_*_to] 和派生的 [strict_*_from] 推论都一致地使用 [match] 公式。
*)

(*
   * ** Future use

   PROPs (deferred to V2b) are by definition strict symmetric monoidal
   categories on the natural numbers; this class is their foundation.
   Hypergraph PROPs — the main application area for the downstream
   rewriting work — combine this with the V1 [Hypergraph] class. 

   --------
   * ** 未来用途

   PROPs（推迟到 V2b）按定义是自然数上的严格对称单oidal范畴；这一类是它们的基础。超图 PROPs —— 下游重写工作的主要应用领域 —— 将其与 V1  [Hypergraph]  类结合起来。
*)
