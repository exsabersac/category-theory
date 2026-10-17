Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Bridging.
Require Import Category.Construction.Cospan.Hypergraph.
Require Import Category.Construction.Cospan.Symmetric.
Require Import Category.Construction.Cospan.HypergraphInstance.
Require Import Category.Construction.DecoratedCospan.
Require Import Category.Construction.DecoratedCospan.Category.
Require Import Category.Construction.DecoratedCospan.Symmetric.
Require Import Category.Construction.DecoratedCospan.Monoidal.
Require Import Category.Construction.DecoratedCospan.Braided.

Generalizable All Variables.

(*
    Reference: Brendan Fong, "Decorated Cospans", arXiv:1502.00872,

   本文件给出构造。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section DecoratedCospanHypergraph.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context `{MC : @Monoidal C}.
Context {D : Category}.
Context `{MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).
Context `{DCC : @DecCospan_Coherent C HP H_Coc MC D MD F LM
                                     id_decoration cospan_merge}.
Context `{DCBC : @DecCospan_Bifunctor_Coherent C HP H_Coc MC D MD F LM
                                                id_decoration cospan_merge}.
Context `{DCMC : @DecCospan_Monoidal_Coherent C HP H_Coc H_Ini MC D MD F LM
                                               id_decoration cospan_merge}.
Context `{DCBrC : @DecCospan_Braided_Coherent C HP H_Coc MC D MD F LM
                                                id_decoration cospan_merge}.
Context `{DCSC : @DecCospan_Symmetric_Coherent C HP H_Coc MC D MD F LM
                                                 id_decoration cospan_merge}.

Notation DC := (DecoratedCospanCat HP LM id_decoration cospan_merge).
Notation DCMon := (DecoratedCospan_Monoidal HP LM id_decoration cospan_merge).
Notation DCSMC :=
  (DecoratedCospan_SymmetricMonoidal HP LM id_decoration cospan_merge).

(*
   本节说明 Hypergraph 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Class DecCospan_Hypergraph_Coherent : Type := {
  dec_cospan_scfa : forall (X : DC),
    @SpecialCommutativeFrobenius DC DCSMC X;

  (** Tensor coherence: the SCFA on [X ⨂ Y] agrees with the canonical
      assembled one. *)
  dec_scfa_tensor_mu : forall (X Y : DC),
    @scfa_mu DC DCSMC _ (dec_cospan_scfa (X ⨂ Y)%object)
      ≈ @canonical_tensor_mu DC DCSMC X Y
          (dec_cospan_scfa X) (dec_cospan_scfa Y);

  dec_scfa_tensor_eta : forall (X Y : DC),
    @scfa_eta DC DCSMC _ (dec_cospan_scfa (X ⨂ Y)%object)
      ≈ @canonical_tensor_eta DC DCSMC X Y
          (dec_cospan_scfa X) (dec_cospan_scfa Y);

  dec_scfa_tensor_delta : forall (X Y : DC),
    @scfa_delta DC DCSMC _ (dec_cospan_scfa (X ⨂ Y)%object)
      ≈ @canonical_tensor_delta DC DCSMC X Y
          (dec_cospan_scfa X) (dec_cospan_scfa Y);

  dec_scfa_tensor_epsilon : forall (X Y : DC),
    @scfa_epsilon DC DCSMC _ (dec_cospan_scfa (X ⨂ Y)%object)
      ≈ @canonical_tensor_epsilon DC DCSMC X Y
          (dec_cospan_scfa X) (dec_cospan_scfa Y);

  (** Unit coherence: the SCFA on [I_DC] is the trivial one. *)
  dec_scfa_unit_mu :
    @scfa_mu DC DCSMC _ (dec_cospan_scfa (@I DC DCMon))
      ≈ to (@unit_left DC DCMon (@I DC DCMon));

  dec_scfa_unit_eta :
    @scfa_eta DC DCSMC _ (dec_cospan_scfa (@I DC DCMon))
      ≈ id[(@I DC DCMon)];

  dec_scfa_unit_delta :
    @scfa_delta DC DCSMC _ (dec_cospan_scfa (@I DC DCMon))
      ≈ from (@unit_left DC DCMon (@I DC DCMon));

  dec_scfa_unit_epsilon :
    @scfa_epsilon DC DCSMC _ (dec_cospan_scfa (@I DC DCMon))
      ≈ id[(@I DC DCMon)]
}.

Context `{DCHGC : DecCospan_Hypergraph_Coherent}.

Set Default Proof Using "All".

(** ** [DecoratedCospan_Hypergraph] : the Hypergraph instance *)

Program Definition DecoratedCospan_Hypergraph : @Hypergraph DC DCSMC := {|
  scfa                := dec_cospan_scfa ;
  scfa_tensor_mu      := dec_scfa_tensor_mu ;
  scfa_tensor_eta     := dec_scfa_tensor_eta ;
  scfa_tensor_delta   := dec_scfa_tensor_delta ;
  scfa_tensor_epsilon := dec_scfa_tensor_epsilon ;
  scfa_unit_mu        := dec_scfa_unit_mu ;
  scfa_unit_eta       := dec_scfa_unit_eta ;
  scfa_unit_delta     := dec_scfa_unit_delta ;
  scfa_unit_epsilon   := dec_scfa_unit_epsilon
|}.

End DecoratedCospanHypergraph.

(*
   本节说明 Hypergraph 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
