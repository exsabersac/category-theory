(* ========================================================================= *)
(* Regression suite for issue #138. / 针对问题 #138 的回归测试套件。                                          *)
(*                                                                           *)
(* This file locks in the resolution of issue #138.  It checks that: / 此文件锁定了问题 #138 的解决方案。它会检查：        *)
(*                                                                           *)
(*   - [StrictCat] is the STRICT category of categories: its homset / - [StrictCat] 是类别中的严格类别：它的同态集          *)
(*     equivalence is [Functor_StrictEq_Setoid] (strict equality of / 等价是 [Functor_StrictEq_Setoid]（严格相等于          *)
(*     functors), not the weak nat-iso equivalence [Functor_Setoid] used by / 函子)，而不是 [Functor_Setoid] 使用的弱自然同构等价  *)
(*     the weak category [Cat]. / 弱类别 [Cat]。                                              *)
(*                                                                           *)
(*   - The underlying-graph [Forgetful] functor and the [Free] ⊣ [Forgetful] / - 底层图 [Forgetful] 函子和 [Free] ⊣ [Forgetful] *)
(*     adjunction live OVER [StrictCat], not over the weak [Cat].  They / 附加在 [StrictCat] 上实时，而不是在弱 [Cat] 上。他们       *)
(*     cannot be defined over [Cat] because they do not respect natural / 不能在 [Cat] 上定义，因为它们不遵守自然      *)
(*     isomorphism: a category's underlying quiver is not invariant under / 同构：一个范畴的底层有向图在……下不保持不变     *)
(*     the weak equivalence that [Cat]'s [Functor_Setoid] identifies. / [Cat] 的 [Functor_Setoid] 所识别的弱等价。        *)
(*                                                                           *)
(*   - The comparison functor [StrictCat_to_Cat] witnesses that strict / - 比较函子 [StrictCat_to_Cat] 证明了严格        *)
(*     equality of functors implies natural isomorphism (strict-eq ⟹ / 函子相等意味着自然同构（严格相等 ⟹         *)
(*     natural-iso), exhibiting [StrictCat] as a refinement of [Cat]. / natural-iso)，显示[StrictCat]作为[Cat]的改进。        *)
(* ========================================================================= *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Construction.Free.Quiver.
Generalizable All Variables.

(* ===== BLOCK A138 — forgetful behaviour ===== *)

(*
The underlying-graph (Forgetful) functor is the motivating example of issue
   #138.  It is defined over [StrictCat], NOT the weak [Cat], precisely because
   it does NOT respect natural isomorphism: two categories can be equivalent
   (naturally isomorphic functors witnessing an equivalence) while their
   underlying quivers are genuinely different, so a functor sending a category
   to its underlying quiver cannot be well-defined up to the weak equivalence
   that [Cat]'s [Functor_Setoid] identifies.  It is well-defined up to the
   STRICT equality of [StrictCat]'s [Functor_StrictEq_Setoid].

--------
底层图（忘却）函子是问题 #138 的动机示例。它定义在 [StrictCat] 上，而不是在弱 [Cat] 上，恰恰因为它不遵守自然同构：两个范畴可以是等价的（自然同构函子证明了这种等价性），而它们的底层棋图却截然不同，因此将一个范畴映射到其底层棋图的函子无法在 [Cat] 的 [Functor_Setoid] 确定的弱等价下良好定义。它在 [StrictCat] 的 [Functor_StrictEq_Setoid] 的严格相等下是良好定义的。
*)

(* Forgetful is well-typed with the claimed signature. / Forgetful 的类型与声称的签名一致。 *)
Check (Forgetful : StrictCat ⟶ QuiverCategory).

(* Computational behaviour: underlying nodes are the category's objects. / 计算行为：底层节点是该类别的对象。 *)
Example A138_nodes (C : Category) : @nodes (Forgetful C) = obj[C] := eq_refl.

(* Underlying edges are the hom-sets. / 底层边是同集合。 *)
Example A138_edges (C : Category) (x y : C) :
  @edges (Forgetful C) x y = (x ~> y) := eq_refl.

(* The edge-map of the functor's fmap is the functor's fmap. / 函子 fmap 的边缘图是函子 fmap。 *)
Example A138_fedgemap (C D : Category) (F : C ⟶ D) (x y : C) (f : x ~> y) :
  @fedgemap _ _ (fmap[Forgetful] F) x y f = fmap[F] f := eq_refl.

(* The underlying constructions on objects and morphisms are well-typed. / 对象和态射上的基础构造类型正确。 *)
Check (QuiverOfCat : Category -> Quiver).
Check (@QuiverHomomorphismOfFunctor
        : ∀ (C D : Category), (C ⟶ D) ->
            QuiverHomomorphism (QuiverOfCat C) (QuiverOfCat D)).

(* The composite Forgetful ◯ FreeCatFunctor is an endofunctor on QuiverCategory. / 复合的 Forgetful ◯ FreeCatFunctor 是 QuiverCategory 上的一个自函子。 *)
Check (Forgetful ◯ FreeCatFunctor : QuiverCategory ⟶ QuiverCategory).

(*
A negative check.  [Forgetful] is fixed as [StrictCat ⟶ Quiv], so ascribing
   it the type [Cat ⟶ Quiv] is a genuine type error — the domain category differs
   ("has type StrictCat ⟶ QuiverCategory while it is expected to have type
   Cat ⟶ QuiverCategory").  These [Fail] commands lock in that [Forgetful] is NOT
   a functor over the weak [Cat].  Note this only checks the type mismatch; it
   does not itself exercise the deeper reason no such functor can be *built* over
   [Cat] (its [fmap_respects] would have to turn a natural isomorphism [F x ≅ G x]
   into a strict equality [F x = G x] of quiver nodes — see [Instance.Cat]).

--------
一次负检查。[Forgetful] 被固定为 [StrictCat ⟶ Quiv]，因此将其归类为 [Cat ⟶ Quiv] 类型是真正的类型错误——域类别不同（“类型为 StrictCat ⟶ QuiverCategory，而预期类型为 Cat ⟶ QuiverCategory”）。这些 [Fail] 命令锁定了 [Forgetful] 不会在弱 [Cat] 上成为函子。请注意，这只检查类型不匹配；它本身并不涉及为什么无法在 [Cat] 上*构建*这样的函子的更深层原因（其 [fmap_respects] 必须将自然同构 [F x ≅ G x] 转换为箭矢节点的严格相等 [F x = G x]——参见 [Instance.Cat]）。
*)
Fail Check (Forgetful : Cat ⟶ QuiverCategory).
Fail Definition A138_forgetful_over_Cat : Cat ⟶ QuiverCategory := Forgetful.

(* ===== BLOCK B138 — free ⊣ forgetful adjunction ===== *)

Check (FreeCatFunctor : QuiverCategory ⟶ StrictCat).

Check (FreeForgetfulAdjunction : FreeCatFunctor ⊣ Forgetful).

(*
A concrete worked quiver: one node, one loop.
   NB: bare [unit] in edge position resolves to the adjunction-unit notation, so
   we must qualify the Coq type as [Datatypes.unit].

--------
一个具体的有效箭袋：一个节点，一个环。
注意：位于边缘位置的裸 [unit] 会解析为结合单位符号，因此我们必须将 Coq 类型限定为 [Datatypes.unit]。
*)
Definition B138_loop : Quiver :=
  Build_Quiver_Standard_Eq Datatypes.unit (fun _ _ => Datatypes.unit).

Check (FreeOnQuiver B138_loop : Category).
Check (FreeCatFunctor B138_loop : Category).

(*
The nodes of the free category on the loop quiver are exactly the quiver's
   nodes (here [unit]).

--------
环形导图上自由范畴的结点正好是导图的结点（这里是 [unit]）。
*)
Example B138_free_loop_nodes :
  obj[FreeOnQuiver B138_loop] = Datatypes.unit := eq_refl.

(* The composite endofunctor on StrictCat / StrictCat 上的复合端函子 *)
Check (FreeCatFunctor ◯ Forgetful : StrictCat ⟶ StrictCat).

(* ===== BLOCK C138 — StrictCat strict laws ===== *)

(*
The defining property of issue #138's fix: StrictCat's hom-equivalence IS the
   strict equality [Functor_StrictEq_Setoid] (not the weak nat-iso
   [Functor_Setoid] of [Cat]).  This pins it directly, so reverting StrictCat to
   the weak setoid fails HERE, in the test body — not merely transitively
   through some downstream consumer.

--------
问题 #138 修复的定义特性：StrictCat 的同构等价就是严格相等 [Functor_StrictEq_Setoid]（而不是 [Cat] 的弱自然同构 [Functor_Setoid]）。这直接固定了它，因此将 StrictCat 回退到弱集合等价在这里的测试主体中会失败——而不仅仅是通过某些下游使用者的传递性失败。
*)
Example C138_homset_is_strict (A B : Category) :
  @homset StrictCat A B = @Functor_StrictEq_Setoid A B := eq_refl.

(*
The strict identity law, exercised through StrictCat's OWN category structure
   (its [id], [compose], [homset] and [id_left]), rather than only via the
   free-standing [fun_strict_equiv_*] lemmas.

--------
严格的同一性法则，通过 StrictCat 的自身分类结构（其 [id]、[compose]、[homset] 和 [id_left]）来执行，而不仅仅是通过独立的 [fun_strict_equiv_*] 词条。
*)
Example C138_strictcat_id_left (A B : Category) (F : A ⟶ B) :
  @equiv _ (@homset StrictCat A B)
         (@compose StrictCat _ _ _ (@id StrictCat B) F) F :=
  @id_left StrictCat A B F.

(*
The three strict category laws, stated with the EXPLICIT strict setoid
   and discharged by the existing lemmas.

--------
三个严格的范畴定律，以明确的严格集合基元表示，并通过现有的引理得到证明。
*)
Example C138_id_left {A B} (F : A ⟶ B) :
  @equiv _ Functor_StrictEq_Setoid (Id ◯ F) F := fun_strict_equiv_id_left F.

Example C138_id_right {A B} (F : A ⟶ B) :
  @equiv _ Functor_StrictEq_Setoid (F ◯ Id) F := fun_strict_equiv_id_right F.

Example C138_comp_assoc {A B C D} (F : C ⟶ D) (G : B ⟶ C) (H : A ⟶ B) :
  @equiv _ Functor_StrictEq_Setoid (F ◯ (G ◯ H)) ((F ◯ G) ◯ H) :=
  fun_strict_equiv_comp_assoc F G H.

(* Strict equality is genuinely an equivalence usable on concrete witnesses. / 严格相等确实是可用于具体实例的等价关系。 *)

(* Reflexivity of a functor under the strict setoid. / 在严格宿集下函子 的自反性。 *)
Example C138_strict_refl {A B} (F : A ⟶ B) :
  @equiv _ Functor_StrictEq_Setoid F F.
Proof.
  reflexivity.
Qed.

(* Id ◯ (Id ◯ F) relates to F under strict equality, using transitivity. / Id ◯ (Id ◯ F) 在严格等式下与 F 相关，使用传递性。 *)
Example C138_nested_id {A B} (F : A ⟶ B) :
  @equiv _ Functor_StrictEq_Setoid (Id ◯ (Id ◯ F)) F.
Proof.
  transitivity (Id ◯ F).
  - exact (fun_strict_equiv_id_left (Id ◯ F)).
  - exact (fun_strict_equiv_id_left F).
Qed.

(* Strict equality refines weak (nat-iso) equality. / 严格相等是对弱（自然同构）相等的细化。 *)
Example C138_strict_refines_weak {A B} (F : A ⟶ B) :
  @equiv _ Functor_Setoid (Id ◯ F) F :=
  strict_equiv_implies_fun_equiv (Id ◯ F) F (fun_strict_equiv_id_left F).

(* ===== BLOCK D138 — comparison functor ===== *)

Check (StrictCat_to_Cat : StrictCat ⟶ Cat).

Example D138_obj (C : Category) : StrictCat_to_Cat C = C := eq_refl.

Example D138_map {C D} (F : C ⟶ D) : fmap[StrictCat_to_Cat] F = F := eq_refl.

(*
The per-object isomorphism the comparison uses is [iso_of_eq] of the object
   equality, which at a reflexivity proof is the identity iso (its [to] and
   [from] are [id]).  These two examples pin [iso_of_eq]'s behaviour directly.
   That [strict_equiv_implies_fun_equiv] builds its natural-iso family as
   [fun x => iso_of_eq (eq_on_obj x)] is true by construction (see ToCat.v); it
   is not separately machine-checked here because that lemma is opaque ([Qed]),
   so its body does not reduce for an [eq_refl] comparison.

--------
该比较使用的每个对象同构是对象等式的 [iso_of_eq]，在自反性证明中，它是恒等同构（其 [to] 和 [from] 为 [id]）。这两个例子直接固定了 [iso_of_eq] 的行为。[strict_equiv_implies_fun_equiv] 构建其自然同构族为 [fun x => iso_of_eq (eq_on_obj x)] 是构造上成立的（参见 ToCat.v）；它在此没有单独进行机器检查，因为该引理是封装的（[Qed]），因此其主体对于 [eq_refl] 比较不发生化简。
*)
Example D138_iso_of_eq_refl_to (C : Category) (x : C) :
  to (iso_of_eq (@eq_refl _ x)) = @id C x := eq_refl.

Example D138_iso_of_eq_refl_from (C : Category) (x : C) :
  from (iso_of_eq (@eq_refl _ x)) = @id C x := eq_refl.

Example D138_strict_to_weak {C D} (F G : C ⟶ D)
  (H : @equiv _ Functor_StrictEq_Setoid F G) : @equiv _ Functor_Setoid F G
  := strict_equiv_implies_fun_equiv F G H.

(*
Concrete instance: re-derive a strict equality witness locally (id_left),
   then push it through the comparison functor to obtain a weak (nat-iso)
   equality in Cat.

--------
具体实例：在本地重新导出一个严格等式见证（id_left），然后将其通过比较函子传递以在 Cat 中得到一个弱的（自然同构）等式。
*)

Definition D138_idleft_strict {C D} (F : C ⟶ D)
  : @equiv _ Functor_StrictEq_Setoid (Id ◯ F) F
  := fun_strict_equiv_id_left F.

Definition D138_idleft_weak {C D} (F : C ⟶ D)
  : @equiv _ Functor_Setoid (Id ◯ F) F
  := strict_equiv_implies_fun_equiv (Id ◯ F) F (D138_idleft_strict F).
