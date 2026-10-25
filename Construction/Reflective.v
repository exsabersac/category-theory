Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(*
 nLab: https://ncatlab.org/nlab/show/reflective+subcategory
 Wikipedia: https://en.wikipedia.org/wiki/Reflective_subcategory

 A reflective subcategory of C is a full subcategory S ⊆ C whose inclusion
 functor [Incl C S : Sub C S ⟶ C] has a left adjoint, the reflector
 [reflector : C ⟶ Sub C S], with [reflector ⊣ Incl C S].  The record
 [Reflective] below bundles exactly these three data: fullness of the
 subcategory ([reflective_full]), the reflector, and the adjunction.

 Dually, a coreflective subcategory is one whose inclusion has a right
 adjoint (the coreflector).  We obtain it by reflectivity in the opposite
 category: [Coreflective S := Reflective (op_subcategory S)], where
 [op_subcategory S] is the subcategory of C^op selecting the same objects
 and the C^op-reverses of the morphisms of S.

 The characteristic property of a *full* reflective subcategory is that the
 counit ε : reflector ∘ Incl ⟹ Id of the adjunction is a natural
 isomorphism: at every object [x] of the subcategory the component
 ε_x : reflector (Incl x) ~> x is invertible.  Its inverse is the unit
 η_{Incl x} : Incl x ~> Incl (reflector (Incl x)) of the adjunction, read
 back into [Sub C S] using fullness — fullness supplies the [shom] witness
 making η into a morphism of the subcategory ([reflective_counit_iso]).  One
 triangle identity ([fmap_counit_unit]) discharges ε_x ∘ η ≈ id, and the
 other ([counit_fmap_unit]) together with naturality of the counit
 ([counit_naturality]) discharges η ∘ ε_x ≈ id. 

 --------
 nLab：https://ncatlab.org/nlab/show/reflective+subcategory 
 维基百科：https://en.wikipedia.org/wiki/Reflective_subcategory 

 C 的一个反射子范畴是一个满子范畴 S ⊆ C，其包含函子 [Incl C S : Sub C S ⟶ C] 具有左伴随，即反射子 [reflector : C ⟶ Sub C S]，并且 [reflector ⊣ Incl C S]。下面的记录 [Reflective] 精确地捆绑了这三条数据：子范畴的充满性（[reflective_full]）、反射子，以及伴随性。

 对偶地，余反射子范畴是其包含函子具有右伴随（余反射子）的子范畴。我们可以通过对偶范畴中的反射性来获得它：[Coreflective S := Reflective (op_subcategory S)]，其中 [op_subcategory S] 是 C^op 的子范畴，选择相同的对象和 S 的态射在 C^op 中的反向映射。*完全*反射子范畴的特征性质是伴随的余单位 ε : 反射子 ∘ 包含 ⟹ Id 是自然同构：在子范畴的每个对象 [x] 上，其分量 ε_x : 反射子(包含 x) ~> x 是可逆的。它的逆是伴随的单位 η_{包含 x} : 包含 x ~> 包含(反射子(包含 x))，通过满性读回到 [Sub C S] —— 满性提供了 [shom] 的见证，使 η 成为子范畴 ([reflective_counit_iso]) 的态射。一个三角恒等式 ([fmap_counit_unit]) 使 ε_x ∘ η ≈ id 成立，另一个 ([counit_fmap_unit]) 以及余单位的自然性 ([counit_naturality]) 使 η ∘ ε_x ≈ id 成立。
*)

(*
 The counit of an adjunction is natural at an arbitrary morphism.  The
 corollaries in Theory/Adjunction.v prove this square only when the domain
 is an F-image ([counit_comp]); the general form below (a copy of the
 argument used for the corollaries there) is what the counit-iso proof
 consumes, since its morphism runs out of an arbitrary object of the
 subcategory. 

 --------
 伴随的余单位在任意态射下是自然的。Theory/Adjunction.v 中的推论仅在定义域是 F-像（[counit_comp]）时证明了这个交换图；下面的一般形式（复制了那里推论使用的论证）是余单位同构证明所用的，因为它的态射来源于子范畴的任意对象。
*)

Lemma counit_naturality
      {Cadj Dadj : Category} {F : Dadj ⟶ Cadj} {U : Cadj ⟶ Dadj}
      (A : F ⊣ U) {x y : Cadj} (f : x ~> y) :
  @counit Cadj Dadj F U A y ∘ fmap[F] (fmap[U] f)
    ≈ f ∘ @counit Cadj Dadj F U A x.
Proof.
  unfold counit.
  rewrite <- from_adj_nat_l.
  rewrite <- from_adj_nat_r.
  now rewrite id_left, id_right.
Qed.

(*
 The reflector, the fullness witness, and the reflection adjunction. 

 --------
 反射器、圆满见证者和反射附加物。
*)

Record Reflective {C : Category} (S : Subcategory C) := {
  reflective_full : Construction.Subcategory.Full C S;
  reflector : C ⟶ Sub C S;
  reflective_adj : reflector ⊣ Incl C S
}.

Arguments reflective_full {C S} r.
Arguments reflector {C S} r.
Arguments reflective_adj {C S} r.

(*
 The opposite subcategory: the same selected objects, with a C^op-morphism
 x ~> y (that is, a C-morphism y ~> x) selected exactly when the underlying
 C-morphism is selected by S. 

 --------
 相反子类别：相同的被选对象，其中仅当基础 C-态射被 S 选中时，才选择 C^op-态射 x ~> y（即 C-态射 y ~> x）。
*)

Definition op_subcategory {C : Category} (S : Subcategory C) :
  Subcategory (C^op) :=
  @Build_Subcategory (C^op)
    (sobj C S)
    (fun x y ox oy f => shom C S oy ox f)
    (fun x y z ox oy oz f g Hf Hg => scomp C S oz oy ox Hg Hf)
    (fun x ox => sid C S ox).

(*
 A coreflective subcategory of C is a reflective subcategory of C^op on the
 opposite subcategory: the inclusion then has a right adjoint in C. 

 --------
 C 的一个共反射子范畴是 C^op 上反射子范畴的对偶子范畴：包含然后在 C 中具有右伴随。
*)

Definition Coreflective {C : Category} (S : Subcategory C) : Type :=
  @Reflective (C^op) (op_subcategory S).

(*
 For a full reflective subcategory the counit is a componentwise
 isomorphism: reflector (Incl x) ≅ x in Sub C S, with the counit as the
 forward map and the (subcategory-lifted) unit as its inverse. 

 --------
 对于一个完全反射子范畴，余单位是按分量的同构：在 Sub C S 中，反射函子 (Incl x) ≅ x，其中余单位作为正向映射，而（升到子范畴的）单位作为它的逆映射。
*)

Lemma reflective_counit_iso {C : Category} {S : Subcategory C}
      (R : Reflective S) (x : Sub C S) :
  reflector R (Incl C S x) ≅[Sub C S] x.
Proof.
  unshelve refine
    {| to   := @counit (Sub C S) C (reflector R) (Incl C S)
                 (reflective_adj R) x
     ; from := _
     ; iso_to_from := _
     ; iso_from_to := _ |}.
  - (* inverse: the unit, lifted into the subcategory by fullness / 逆：单位，通过完备性被提升到子范畴中 *)
    exists (@Category.Theory.Adjunction.unit
              (Sub C S) C (reflector R) (Incl C S) (reflective_adj R)
              (Incl C S x)).
    apply (reflective_full R).
  - (* ε_x ∘ η ≈ id, one triangle identity / ε_x ∘ η ≈ id，一个三角恒等式 *)
    apply (@fmap_counit_unit
             (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) x).
  - (* η ∘ ε_x ≈ id, by counit naturality and the other triangle identity / η ∘ ε_x ≈ id，由余单位自然性和另一个三角恒等式得出 *)
    rewrite <- (counit_naturality (reflective_adj R)).
    apply (@counit_fmap_unit
             (Sub C S) C (reflector R) (Incl C S) (reflective_adj R)
             (Incl C S x)).
Qed.
