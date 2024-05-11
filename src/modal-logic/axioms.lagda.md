# Modal logic axioms

```agda
module modal-logic.axioms where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-extensionality
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.dependent-identifications
open import foundation-core.equality-dependent-pair-types
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.injective-maps
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes
open import foundation-core.transport-along-identifications

open import modal-logic.deduction
open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.soundness
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l : Level} (i : Set l)
  where

  ax-1-parameter :
    (h : modal-formula i → modal-formula i) → is-injective h → modal-theory l i
  pr1 (ax-1-parameter h inj f) = Σ (modal-formula i) (λ a → f ＝ h a)
  pr2 (ax-1-parameter h inj f) (a , refl) =
    is-prop-is-contr
      ( is-contr-Σ-is-prop a refl
        ( λ b → is-set-formula (h a) (h b))
        ( λ x → inj))
      ( a , refl)

  ax-2-parameters :
    (h : modal-formula i → modal-formula i → modal-formula i) →
    ({x x' y y' : modal-formula i} → h x y ＝ h x' y' → x ＝ x') →
    ({x x' y y' : modal-formula i} → h x y ＝ h x' y' → y ＝ y') →
    modal-theory l i
  pr1 (ax-2-parameters h inj-1 inj-2 f) =
    Σ (modal-formula i) (λ a → Σ (modal-formula i) (λ b → f ＝ h a b))
  pr2 (ax-2-parameters h inj-1 inj-2 f) (a , b , refl) =
    is-prop-is-contr
      ( is-contr-Σ-is-prop a (b , refl)
        ( λ x → is-prop-type-Prop (ax-1-parameter (h x) inj-2 (h a b)))
        ( λ x (y , e) → inj-1 e))
      ( a , b , refl)

  ax-3-parameters :
    (h :
      modal-formula i → modal-formula i → modal-formula i → modal-formula i) →
    ({x x' y y' z z' : modal-formula i} → h x y z ＝ h x' y' z' → x ＝ x') →
    ({x x' y y' z z' : modal-formula i} → h x y z ＝ h x' y' z' → y ＝ y') →
    ({x x' y y' z z' : modal-formula i} → h x y z ＝ h x' y' z' → z ＝ z') →
    modal-theory l i
  pr1 (ax-3-parameters h inj-1 inj-2 inj-3 f) =
    Σ ( modal-formula i)
      ( λ a →
        ( Σ (modal-formula i)
          ( λ b → Σ (modal-formula i) ( λ c → f ＝ h a b c))))
  pr2 (ax-3-parameters h inj-1 inj-2 inj-3 f) (a , b , c , refl) =
    is-prop-is-contr
      ( is-contr-Σ-is-prop a (b , c , refl)
        ( λ x → is-prop-type-Prop (ax-2-parameters (h x) inj-2 inj-3 (h a b c)))
        ( λ x (y , z , e) → inj-1 e))
      ( a , b , c , refl)

  ax-k : modal-theory l i
  ax-k =
    ax-2-parameters
      ( λ a b → a →ₘ b →ₘ a)
      ( eq-implication-left)
      ( eq-implication-left ∘ eq-implication-right)

  ax-s : modal-theory l i
  ax-s =
    ax-3-parameters
      ( λ a b c → (a →ₘ b →ₘ c) →ₘ (a →ₘ b) →ₘ a →ₘ c)
      ( eq-implication-left ∘ eq-implication-left)
      ( eq-implication-left ∘ eq-implication-right ∘ eq-implication-left)
      ( eq-implication-right ∘ eq-implication-right ∘ eq-implication-left)

  ax-n : modal-theory l i
  ax-n =
    ax-2-parameters
      ( λ a b → □ₘ (a →ₘ b) →ₘ □ₘ a →ₘ □ₘ b)
      ( eq-implication-left ∘ eq-box ∘ eq-implication-left)
      ( eq-implication-right ∘ eq-box ∘ eq-implication-left)

  ax-dn : modal-theory l i
  ax-dn = ax-1-parameter (λ a → ¬¬ₘ a →ₘ a) eq-implication-right

  ax-m : modal-theory l i
  ax-m = ax-1-parameter (λ a → □ₘ a →ₘ a) eq-implication-right

  ax-b : modal-theory l i
  ax-b = ax-1-parameter (λ a → a →ₘ □ₘ ◇ₘ a) eq-implication-left

  ax-d : modal-theory l i
  ax-d = ax-1-parameter (λ a → □ₘ a →ₘ ◇ₘ a) (eq-box ∘ eq-implication-left)

  ax-4 : modal-theory l i
  ax-4 = ax-1-parameter (λ a → □ₘ a →ₘ □ₘ □ₘ a) (eq-box ∘ eq-implication-left)

  ax-5 : modal-theory l i
  ax-5 =
    ax-1-parameter ( λ a → ◇ₘ a →ₘ □ₘ ◇ₘ a) ( eq-diamond ∘ eq-implication-left)

module _
  {l1 l2 : Level}
  (i : Set l1)
  (l3 l4 : Level)
  where

  ax-k-soundness : soundness (ax-k i) (all-models l2 l3 i l4)
  ax-k-soundness .(a →ₘ b →ₘ a) (a , b , refl) M _ x fa _ = fa

  ax-s-soundness : soundness (ax-s i) (all-models l2 l3 i l4)
  ax-s-soundness
    .((a →ₘ b →ₘ c) →ₘ (a →ₘ b) →ₘ a →ₘ c)
    (a , b , c , refl)
    M in-class x fabc fab fa =
      fabc fa (fab fa)

  ax-n-soundness : soundness (ax-n i) (all-models l2 l3 i l4)
  ax-n-soundness
    .(□ₘ (a →ₘ b) →ₘ □ₘ a →ₘ □ₘ b)
    (a , b , refl)
    M in-class x fab fa y r =
      fab y r (fa y r)

  ax-dn-soundness : soundness (ax-dn i) (decidable-kripke-models l2 l3 i l4)
  ax-dn-soundness .(¬¬ₘ a →ₘ a) (a , refl) M is-dec x f
    with (is-dec a x)
  ... | inl fa = fa
  ... | inr fna = raise-ex-falso _ (f (λ fa -> map-raise (fna fa)))

  ax-m-soundness : soundness (ax-m i) (reflexive-kripke-models l2 l3 i l4)
  ax-m-soundness .(□ₘ a →ₘ a) (a , refl) M is-refl x fa = fa x (is-refl x)

  ax-b-soundness : soundness (ax-b i) (symmetry-kripke-models l2 l3 i l4)
  ax-b-soundness .(a →ₘ □ₘ ◇ₘ a) (a , refl) M is-sym x fa y r contra =
    contra x (is-sym x y r) fa

  ax-d-soundness : soundness (ax-d i) (serial-kripke-models l2 l3 i l4)
  ax-d-soundness .(□ₘ a →ₘ ◇ₘ a) (a , refl) M is-serial x fa contra =
    map-raise
      ( apply-universal-property-trunc-Prop
        ( is-serial x)
        ( empty-Prop)
        ( λ (y , r) → map-inv-raise (contra y r (fa y r))))

  ax-4-soundness : soundness (ax-4 i) (transitive-kripke-models l2 l3 i l4)
  ax-4-soundness .(□ₘ a →ₘ □ₘ □ₘ a) (a , refl) M is-trans x fa y r-xy z r-yz =
    fa z (is-trans x y z r-yz r-xy)

  ax-5-sooundness : soundness (ax-5 i) (euclidean-kripke-models l2 l3 i l4)
  ax-5-sooundness .(◇ₘ a →ₘ □ₘ ◇ₘ a) (a , refl) M is-eucl x fa y r-xy contra =
    fa (λ z r-xz → contra z (is-eucl x y z r-xy r-xz))
```
