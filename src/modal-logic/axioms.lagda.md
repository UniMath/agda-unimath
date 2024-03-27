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

open import modal-logic.formulas
open import modal-logic.kripke-semantics
open import modal-logic.logic-syntax
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

  ax-1-parameter : (h : formula i → formula i) → is-injective h → formulas l i
  pr1 (ax-1-parameter h inj f) = Σ (formula i) (λ a → f ＝ h a)
  pr2 (ax-1-parameter h inj f) (a , refl) =
    is-prop-is-contr
      ( is-contr-Σ-is-prop a refl
        ( λ _ → is-set-formula i _ _)
        ( λ x → inj))
      ( a , refl)

  ax-2-parameters :
    (h : formula i → formula i → formula i) →
    ({x x' y y' : formula i} → h x y ＝ h x' y' → x ＝ x') →
    ({x x' y y' : formula i} → h x y ＝ h x' y' → y ＝ y') →
    formulas l i
  pr1 (ax-2-parameters h inj-1 inj-2 f) =
    Σ (formula i) (λ a → Σ (formula i) (λ b → f ＝ h a b))
  pr2 (ax-2-parameters h inj-1 inj-2 f) (a , b , refl) =
    is-prop-is-contr
      ( is-contr-Σ-is-prop a (b , refl)
        ( λ x → is-prop-type-Prop (ax-1-parameter (h x) inj-2 (h a b)))
        ( λ x (y , e) → inj-1 e))
      ( a , b , refl)

  ax-3-parameters :
    (h : formula i → formula i → formula i → formula i) →
    ({x x' y y' z z' : formula i} → h x y z ＝ h x' y' z' → x ＝ x') →
    ({x x' y y' z z' : formula i} → h x y z ＝ h x' y' z' → y ＝ y') →
    ({x x' y y' z z' : formula i} → h x y z ＝ h x' y' z' → z ＝ z') →
    formulas l i
  pr1 (ax-3-parameters h inj-1 inj-2 inj-3 f) =
    Σ ( formula i)
      ( λ a → Σ (formula i) (λ b → Σ (formula i) ( λ c → f ＝ h a b c)))
  pr2 (ax-3-parameters h inj-1 inj-2 inj-3 f) (a , b , c , refl) =
    is-prop-is-contr
      ( is-contr-Σ-is-prop a (b , c , refl)
        ( λ x → is-prop-type-Prop (ax-2-parameters (h x) inj-2 inj-3 (h a b c)))
        ( λ x (y , z , e) → inj-1 e))
      ( a , b , c , refl)

  ax-k : formulas l i
  ax-k =
    ax-2-parameters
      ( λ a b → a →ₘ b →ₘ a)
      ( eq-implication-left)
      ( eq-implication-left ∘ eq-implication-right)

  ax-s : formulas l i
  ax-s =
    ax-3-parameters
      ( λ a b c → (a →ₘ b →ₘ c) →ₘ (a →ₘ b) →ₘ a →ₘ c)
      ( eq-implication-left ∘ eq-implication-left)
      ( eq-implication-left ∘ eq-implication-right ∘ eq-implication-left)
      ( eq-implication-right ∘ eq-implication-right ∘ eq-implication-left)

  ax-n : formulas l i
  ax-n =
    ax-2-parameters
      ( λ a b → □ (a →ₘ b) →ₘ □ a →ₘ □ b)
      ( eq-implication-left ∘ eq-box ∘ eq-implication-left)
      ( eq-implication-right ∘ eq-box ∘ eq-implication-left)

  ax-dn : formulas l i
  ax-dn = ax-1-parameter ( λ a → ~~ a →ₘ a) eq-implication-right

  ax-m : formulas l i
  ax-m = ax-1-parameter (λ a → □ a →ₘ a) eq-implication-right

  ax-b : formulas l i
  ax-b = ax-1-parameter (λ a → a →ₘ □ ◇ a) eq-implication-left

  ax-d : formulas l i
  ax-d = ax-1-parameter (λ a → □ a →ₘ ◇ a) (eq-box ∘ eq-implication-left)

  ax-4 : formulas l i
  ax-4 = ax-1-parameter (λ a → □ a →ₘ □ □ a) (eq-box ∘ eq-implication-left)

  ax-5 : formulas l i
  ax-5 =
    ax-1-parameter ( λ a → ◇ a →ₘ □ ◇ a) ( eq-diamond ∘ eq-implication-left)

module _
  {l1 l2 : Level}
  (i : Set l1)
  (l3 l4 : Level)
  where

  ax-k-soundness : soundness (ax-k i) (all-models l2 l3 i l4)
  ax-k-soundness (a →ₘ b →ₘ a) (_ , _ , refl) M _ x fa _ = fa

  ax-n-soundness : soundness (ax-n i) (all-models l2 l3 i l4)
  ax-n-soundness
    (□ (a →ₘ b) →ₘ □ a →ₘ □ b)
    (_ , _ , refl)
    M in-class x fab fa y r =
      fab y r (fa y r)

  ax-s-soundness : soundness (ax-s i) (all-models l2 l3 i l4)
  ax-s-soundness
    ((a →ₘ b →ₘ c) →ₘ (a →ₘ b) →ₘ a →ₘ c)
    (_ , _ , _ , refl)
    M in-class x fabc fab fa =
      fabc fa (fab fa)

  ax-dn-soundness : soundness (ax-dn i) (decidable-models l2 l3 i l4)
  ax-dn-soundness .(~~ a →ₘ a) (a , refl) M is-dec x f
    with (is-dec a x)
  ... | inl fa = fa
  ... | inr fna = raise-ex-falso _ (f (λ fa -> map-raise (fna fa)))

  ax-m-soundness : soundness (ax-m i) (reflexive-class l2 l3 i l4)
  ax-m-soundness (□ a →ₘ a) (_ , refl) M is-refl x fa = fa x (is-refl x)

  ax-b-soundness : soundness (ax-b i) (symmetry-class l2 l3 i l4)
  ax-b-soundness .(a →ₘ □ ◇ a) (a , refl) M is-sym x fa y r contra =
    contra x (is-sym x y r) fa

  ax-d-soundness : soundness (ax-d i) (serial-class l2 l3 i l4)
  ax-d-soundness .(□ a →ₘ ◇ a) (a , refl) M is-serial x fa contra =
    map-raise
      ( apply-universal-property-trunc-Prop
        ( is-serial x)
        ( empty-Prop)
        ( λ (y , r) → map-inv-raise (contra y r (fa y r))))

  ax-4-soundness : soundness (ax-4 i) (transitivity-class l2 l3 i l4)
  ax-4-soundness .(□ a →ₘ □ □ a) (a , refl) M is-trans x fa y r-xy z r-yz =
    fa z (is-trans x y z r-yz r-xy)

  ax-5-sooundness : soundness (ax-5 i) (euclidean-class l2 l3 i l4)
  ax-5-sooundness .(◇ a →ₘ □ ◇ a) (a , refl) M is-eucl x fa y r-xy contra =
    fa (λ z r-xz → contra z (is-eucl x y z r-xy r-xz))
```
