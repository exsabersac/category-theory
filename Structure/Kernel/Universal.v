Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Kernel.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

(** * Kernels as universal elements *)

(*
   Wikipedia: https://en.wikipedia.org/wiki/Kernel_(category_theory)
   Paper: Kan, "Adjoint functors", Trans. Amer. Math. Soc. 87, 1958

   本文件给出泛构造相关。

   （英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(*
   本节说明hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* * ** Zero 态射 without zero 对象 （已译） *)

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Class ZeroMorphisms (C : Category) := {
  zmor {x y : C} : x ~> y;
  zmor_absorb_l {x y z : C} (g : y ~> z) : g ∘ @zmor x y ≈ @zmor x z;
  zmor_absorb_r {x y z : C} (g : x ~> y) : @zmor y z ∘ g ≈ @zmor x z
}.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
#[export] Instance ZeroMorphisms_of_ZeroObject {C : Category}
  (Z : @ZeroObject C) : ZeroMorphisms C :=
  @Build_ZeroMorphisms C
    (fun x y => @zero_mor C Z x y)
    (fun x y z g => @zero_mor_left C Z x y z g)
    (fun x y z g => @zero_mor_right C Z x y z g).

(** ** The kill-f presheaf *)

Section KernelUniversal.

Context {C : Category}.
Context {ZM : ZeroMorphisms C}.
Context {x y : C}.
Context (f : x ~> y).

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition Kills (d : C) : Type := { h : d ~> x & f ∘ h ≈ zmor }.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition Kills_Setoid (d : C) : Setoid (Kills d) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.

(* Contravariant by precomposition: if f kills h then it kills h ∘ u, by
   associativity and absorption. *)
Program Definition KillPresheaf : C^op ⟶ Sets := {|
  fobj := fun d => {| carrier := Kills d ; is_setoid := Kills_Setoid d |};
  fmap := fun d d' (u : d ~{C^op}~> d') =>
            {| morphism := fun p : Kills d => (`1 p ∘ u; _) |}
|}.
Next Obligation.
  rewrite comp_assoc, (`2 p).
  apply zmor_absorb_r.
Qed.

(*
   本节说明函子相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

(* The action, conversion: 这是 what makes universal-element
 clause below literally descent clause [kernel_desc]. （已译） *)
Lemma kill_fmap (d d' : C) (u : d' ~{C}~> d) (p : Kills d) :
  `1 (fmap[KillPresheaf] u p) = `1 p ∘ u.
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma kill_fork {d : C} {h : d ~> x} (Hh : f ∘ h ≈ zmor) :
  f ∘ h ≈ zmor ∘ h.
Proof. rewrite Hh; symmetry; apply zmor_absorb_r. Qed.

Lemma fork_kill {d : C} {h : d ~> x} (Hh : f ∘ h ≈ zmor ∘ h) :
  f ∘ h ≈ zmor.
Proof. rewrite Hh; apply zmor_absorb_r. Qed.

(* [Structure/Kernel.v]'s [IsKernel] restated over [ZeroMorphisms]. When
 structure comes zero 对象 two THE SAME TYPE; see
 [IsKernel_is_IsKernelOf] below. （已译） *)
Definition IsKernelOf {k : C} (i : k ~> x) : Type := IsEqualizer f zmor k i.

(** ** The two passages *)

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition kernel_aue {k : C} {i : k ~> x} (K : IsKernelOf i)
  : AUniversalElement KillPresheaf k :=
  @Build_AUniversalElement (C^op) KillPresheaf k
    (existT _ i (fork_kill (fork_eq K)))
    (fun d p => eq_desc K (`1 p) (kill_fork (`2 p))).

Definition aue_kernel {k : C} (U : AUniversalElement KillPresheaf k)
  : IsKernelOf (`1 (@aue_elem (C^op) KillPresheaf k U)) :=
  {| fork_eq := kill_fork (`2 (@aue_elem (C^op) KillPresheaf k U))
   ; eq_desc := fun z h Hh =>
       @aue_universal (C^op) KillPresheaf k U z (existT _ h (fork_kill Hh)) |}.

(* The underlying 态射 survives both passages nose. （已译） *)
Corollary kernel_aue_morphism {k : C} {i : k ~> x} (K : IsKernelOf i) :
  `1 (@aue_elem (C^op) KillPresheaf k (kernel_aue K)) = i.
Proof. reflexivity. Qed.

Corollary aue_kernel_morphism {k : C} (U : AUniversalElement KillPresheaf k) :
  `1 (@aue_elem (C^op) KillPresheaf k
        (kernel_aue (aue_kernel U)))
    = `1 (@aue_elem (C^op) KillPresheaf k U).
Proof. reflexivity. Qed.

(* 相关说明。 （已译） *)
Corollary kernel_aue_mediator {k : C} {i : k ~> x} (K : IsKernelOf i)
  (d : C) (h : d ~> x) (Hh : f ∘ h ≈ zmor) :
  unique_obj (@aue_universal (C^op) KillPresheaf k (kernel_aue K) d (h; Hh))
    = unique_obj (eq_desc K h (kill_fork Hh)).
Proof. reflexivity. Qed.

(* * ** The 等价, universe-free: two round trips （已译） *)

(*
   本节说明同构、核/余核、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Lemma kernel_round_mediator {k : C} {i : k ~> x} (K : IsKernelOf i)
  {z : C} (h : z ~> x) (Hh : f ∘ h ≈ zmor ∘ h) :
  unique_obj (eq_desc (aue_kernel (kernel_aue K)) h Hh)
    ≈ unique_obj (eq_desc K h Hh).
Proof.
  apply (uniqueness (eq_desc (aue_kernel (kernel_aue K)) h Hh)).
  exact (unique_property (eq_desc K h Hh)).
Qed.

Lemma aue_kernel_round_mediator {k : C} (U : AUniversalElement KillPresheaf k)
  (d : C) (p : Kills d) :
  unique_obj (@aue_universal (C^op) KillPresheaf k
                (kernel_aue (aue_kernel U)) d p)
    ≈ unique_obj (@aue_universal (C^op) KillPresheaf k U d p).
Proof.
  apply (uniqueness (@aue_universal (C^op) KillPresheaf k
                       (kernel_aue (aue_kernel U)) d p)).
  exact (unique_property (@aue_universal (C^op) KillPresheaf k U d p)).
Qed.

(* * ** The 等价, 同构 setoids （已译） *)

Definition KernelData (k : C) : Type := { i : k ~> x & IsKernelOf i }.

Program Definition KernelData_Setoid (k : C) : Setoid (KernelData k) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.

Definition KernelSetoid (k : C) : SetoidObject :=
  {| carrier := KernelData k ; is_setoid := KernelData_Setoid k |}.

Definition AUEKernelSetoid (k : C) : SetoidObject :=
  {| carrier := AUniversalElement KillPresheaf k
   ; is_setoid := @AUniversalElementEquiv (C^op) KillPresheaf k |}.

(*
   本节说明同构、核/余核、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Program Definition kernel_universal_element_iso (k : C)
  : @Isomorphism Sets (KernelSetoid k) (AUEKernelSetoid k) := {|
  to   := {| morphism := fun p : KernelData k => kernel_aue (`2 p) |};
  from := {| morphism := fun U : AUniversalElement KillPresheaf k =>
               (`1 (@aue_elem (C^op) KillPresheaf k U); aue_kernel U) |}
|}.

(** ** Representability *)

(*
   本节说明函子、Yoneda、hom相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition kernel_UniversalElement {k : C} {i : k ~> x} (K : IsKernelOf i)
  : UniversalElement KillPresheaf :=
  UniversalElement_of_AUniversalElement (kernel_aue K).

Definition kernel_Representable {k : C} {i : k ~> x} (K : IsKernelOf i)
  : Representable KillPresheaf :=
  Representable_of_UniversalElement (kernel_UniversalElement K).

Corollary kernel_repr_obj {k : C} {i : k ~> x} (K : IsKernelOf i) :
  @repr_obj (C^op) KillPresheaf (kernel_Representable K) = k.
Proof. reflexivity. Qed.

(* The natural 同构 itself: Hom(─, k) ≅ Kill_f [C^op, Sets].
 [@Curried_Hom (C^op) k] IS [Hom ─,k], presheaf Hom(─, k)
 (Functor/Hom.v defines [Curried_CoHom C] as [Curried_Hom C^op]).（已译） *)
Definition kernel_representation {k : C} {i : k ~> x} (K : IsKernelOf i)
  : @Curried_Hom (C^op) k ≅[[C^op, Sets]] KillPresheaf :=
  ue_representation KillPresheaf k (kernel_aue K).

(* Its component at d carries u : d ~> k i ∘ u, nose -- the
 comparison map kernel's 普遍性质. （已译） *)
Corollary kernel_representation_at {k : C} {i : k ~> x} (K : IsKernelOf i)
  (d : C) (u : d ~{C}~> k) :
  `1 (transform (to (kernel_representation K)) d u) = i ∘ u.
Proof. reflexivity. Qed.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Definition kernel_of_representable (R : Representable KillPresheaf)
  : { k : C & { i : k ~> x & IsKernelOf i } } :=
  ( @repr_obj (C^op) KillPresheaf R
  ; ( `1 (@aue_elem (C^op) KillPresheaf (@repr_obj (C^op) KillPresheaf R)
            (AUniversalElement_of_repr KillPresheaf
               (@repr_obj (C^op) KillPresheaf R)
               (@represented (C^op) KillPresheaf R)))
    ; aue_kernel (AUniversalElement_of_repr KillPresheaf
                    (@repr_obj (C^op) KillPresheaf R)
                    (@represented (C^op) KillPresheaf R)) )).

Definition kernel_iff_representable
  : { k : C & { i : k ~> x & IsKernelOf i } } ↔ Representable KillPresheaf.
Proof.
  split.
  - intros [k [i K]]; exact (kernel_Representable K).
  - exact kernel_of_representable.
Defined.

End KernelUniversal.

Arguments Kills {C ZM x y} f d.
Arguments KillPresheaf {C ZM x y} f.
Arguments IsKernelOf {C ZM x y} f {k} i.

(* * ** The zero-对象 case: [Structure/Kernel.v]'s kernels, unchanged （已译） *)

Section KernelUniversalZeroObject.

Context {C : Category}.
Context {Z : @ZeroObject C}.
Context {x y : C}.
Context (f : x ~> y).

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary zmor_is_zero_mor :
  @zmor C (ZeroMorphisms_of_ZeroObject Z) x y = @zero_mor C Z x y.
Proof. reflexivity. Qed.

(*
   本节说明核/余核、来源与用途相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary IsKernel_is_IsKernelOf {k : C} (i : k ~> x) :
  @IsKernel C Z x y k f i = @IsKernelOf C (ZeroMorphisms_of_ZeroObject Z) x y f k i.
Proof. reflexivity. Qed.

Definition kernel_universal_element {k : C} {i : k ~> x} (K : IsKernel f i)
  : AUniversalElement (@KillPresheaf C (ZeroMorphisms_of_ZeroObject Z) x y f) k
  := kernel_aue f K.

Definition kernel_representable {k : C} {i : k ~> x} (K : IsKernel f i)
  : Representable (@KillPresheaf C (ZeroMorphisms_of_ZeroObject Z) x y f)
  := kernel_Representable f K.

End KernelUniversalZeroObject.

(* 相关说明。 （已译） *)

(*
   本节说明等化子、（余）强度、核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Section EqualizerUniversal.

Context {C : Category}.
Context {x y : C}.
Context (f g : x ~> y).

Definition Forks (d : C) : Type := { h : d ~> x & f ∘ h ≈ g ∘ h }.

Program Definition Forks_Setoid (d : C) : Setoid (Forks d) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.

Program Definition ForkPresheaf : C^op ⟶ Sets := {|
  fobj := fun d => {| carrier := Forks d ; is_setoid := Forks_Setoid d |};
  fmap := fun d d' (u : d ~{C^op}~> d') =>
            {| morphism := fun p : Forks d => (`1 p ∘ u; _) |}
|}.
Next Obligation. rewrite !comp_assoc; now rewrite (`2 p). Qed.

(* 相关说明。 （已译） *)
Definition equalizer_aue {k : C} {i : k ~> x} (E : IsEqualizer f g k i)
  : AUniversalElement ForkPresheaf k :=
  @Build_AUniversalElement (C^op) ForkPresheaf k
    (existT _ i (fork_eq E))
    (fun d p => eq_desc E (`1 p) (`2 p)).

Definition aue_equalizer {k : C} (U : AUniversalElement ForkPresheaf k)
  : IsEqualizer f g k (`1 (@aue_elem (C^op) ForkPresheaf k U)) :=
  {| fork_eq := `2 (@aue_elem (C^op) ForkPresheaf k U)
   ; eq_desc := fun z h Hh =>
       @aue_universal (C^op) ForkPresheaf k U z (existT _ h Hh) |}.

(*
   本节说明核/余核相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary aue_equalizer_round {k : C} {i : k ~> x} (E : IsEqualizer f g k i) :
  aue_equalizer (equalizer_aue E) = E.
Proof. reflexivity. Qed.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Corollary aue_equalizer_round_universal {k : C}
  (U : AUniversalElement ForkPresheaf k) :
  @aue_universal (C^op) ForkPresheaf k (equalizer_aue (aue_equalizer U))
    = fun d p => @aue_universal (C^op) ForkPresheaf k U d (`1 p; `2 p).
Proof. reflexivity. Qed.

Corollary aue_equalizer_round_elem {k : C}
  (U : AUniversalElement ForkPresheaf k) :
  `1 (@aue_elem (C^op) ForkPresheaf k (equalizer_aue (aue_equalizer U)))
    = `1 (@aue_elem (C^op) ForkPresheaf k U).
Proof. reflexivity. Qed.

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)
Lemma aue_equalizer_round_mediator {k : C}
  (U : AUniversalElement ForkPresheaf k) (d : C) (p : Forks d) :
  unique_obj (@aue_universal (C^op) ForkPresheaf k
                (equalizer_aue (aue_equalizer U)) d p)
    = unique_obj (@aue_universal (C^op) ForkPresheaf k U d p).
Proof.
  (* 相关说明。 （已译） *)
  destruct p; reflexivity.
Qed.

Definition EqualizerData (k : C) : Type := { i : k ~> x & IsEqualizer f g k i }.

Program Definition EqualizerData_Setoid (k : C) : Setoid (EqualizerData k) := {|
  equiv := fun p q => `1 p ≈ `1 q
|}.

Definition EqualizerSetoid (k : C) : SetoidObject :=
  {| carrier := EqualizerData k ; is_setoid := EqualizerData_Setoid k |}.

Definition AUEEqualizerSetoid (k : C) : SetoidObject :=
  {| carrier := AUniversalElement ForkPresheaf k
   ; is_setoid := @AUniversalElementEquiv (C^op) ForkPresheaf k |}.

Program Definition equalizer_universal_element_iso (k : C)
  : @Isomorphism Sets (EqualizerSetoid k) (AUEEqualizerSetoid k) := {|
  to   := {| morphism := fun p : EqualizerData k => equalizer_aue (`2 p) |};
  from := {| morphism := fun U : AUniversalElement ForkPresheaf k =>
               (`1 (@aue_elem (C^op) ForkPresheaf k U); aue_equalizer U) |}
|}.

(* 相关说明。 （已译） *)
Definition equalizer_Representable {k : C} {i : k ~> x}
  (E : IsEqualizer f g k i) : Representable ForkPresheaf :=
  Representable_of_UniversalElement
    (UniversalElement_of_AUniversalElement (equalizer_aue E)).

Corollary equalizer_repr_obj {k : C} {i : k ~> x} (E : IsEqualizer f g k i) :
  @repr_obj (C^op) ForkPresheaf (equalizer_Representable E) = k.
Proof. reflexivity. Qed.

End EqualizerUniversal.

Arguments Forks {C x y} f g d.
Arguments ForkPresheaf {C x y} f g.

(* * ** How much zero 态射 buys （已译） *)

(*
   本节说明 Universal 相关定义、性质与动机。

   （本节英文长注释已压缩为中文导言；Coq 标识符/Require/API 未改。）
*)

Program Definition kill_fork_iso {C : Category} {ZM : ZeroMorphisms C}
  {x y : C} (f : x ~> y)
  : KillPresheaf f ≅[[C^op, Sets]] ForkPresheaf f zmor := {|
  to   := {| transform := fun d =>
               {| morphism := fun p : Kills f d => (`1 p; kill_fork f (`2 p)) |} |};
  from := {| transform := fun d =>
               {| morphism := fun p : Forks f zmor d => (`1 p; fork_kill f (`2 p)) |} |}
|}.
