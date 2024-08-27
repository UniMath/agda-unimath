# The law of excluded middle

```agda
module foundation.law-of-excluded-middle where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.decidable-propositions
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.small-types
open import foundation.subtypes
open import foundation.universe-levels

open import foundation-core.coproduct-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.negation

open import univalent-combinatorics.2-element-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

The {{#concept "law of excluded middle" Agda=LEM}} asserts that any
[proposition](foundation-core.propositions.md) `P` is
[decidable](foundation.decidable-types.md).

## Definition

```agda
module _
  (l : Level)
  where

  LEM-Prop : Prop (lsuc l)
  LEM-Prop = Π-Prop (Prop l) is-decidable-Prop

  LEM : UU (lsuc l)
  LEM = type-Prop LEM-Prop

apply-LEM : {l : Level} → LEM l → {P : UU l} → is-prop P → is-decidable P
apply-LEM lem {P} is-prop-P = lem (P , is-prop-P)
```

## Properties

-- implies contraposition

### The law of excluded middle implies the contraposition of a proposition

```agda
contraposition :
  {l1 l2 : Level} → LEM l2 → {P : UU l1} (Q : Prop l2) →
  (¬ (type-Prop Q) → ¬ P) →
  P → type-Prop Q
contraposition lem Q = contraposition-is-decidable (lem Q)
```

### TODO

```agda
lower-LEM : {l1 : Level} (l2 : Level) → LEM (l1 ⊔ l2) → LEM l1
lower-LEM l2 lem P =
  is-decidable-equiv (compute-raise l2 (type-Prop P)) (lem (raise-Prop l2 P))
```

### Given LEM, we obtain a map from the type of propositions to the type of decidable propositions

```agda
decidable-prop-Prop :
  {l : Level} → LEM l → Prop l → Decidable-Prop l
pr1 (decidable-prop-Prop lem P) = type-Prop P
pr1 (pr2 (decidable-prop-Prop lem P)) = is-prop-type-Prop P
pr2 (pr2 (decidable-prop-Prop lem P)) = lem P
```

### Given LEM, Prop equiv Decidable-Prop

```agda
prop-equiv-decidable-prop :
  {l : Level} → LEM l → Prop l ≃ Decidable-Prop l
prop-equiv-decidable-prop lem =
  pair
    ( decidable-prop-Prop lem)
    ( is-equiv-is-invertible
      ( prop-Decidable-Prop)
      ( λ P →
        ( eq-pair-Σ
          ( refl)
          ( eq-is-prop (is-prop-is-decidable-prop (type-Decidable-Prop P)))))
      ( λ P → eq-pair-Σ refl (eq-is-prop (is-prop-is-prop (type-Prop P)))))

is-finite-Prop-LEM : {l : Level} → LEM l → is-finite (Prop l)
is-finite-Prop-LEM lem =
  is-finite-equiv'
    ( equiv-bool-Decidable-Prop ∘e prop-equiv-decidable-prop lem)
    ( is-finite-bool)

is-small-Prop-LEM : {l1 : Level} (l2 : Level) → LEM l1 → is-small l2 (Prop l1)
is-small-Prop-LEM {l1} l2 lem =
  is-small-equiv
    ( Decidable-Prop l1)
    ( prop-equiv-decidable-prop lem)
    ( is-small-Decidable-Prop l1 l2)

is-small-type-Prop-LEM :
  {l1 : Level} (l2 : Level) → LEM l1 → (P : Prop l1) → is-small l2 (type-Prop P)
is-small-type-Prop-LEM l2 lem P =
  is-small-is-decidable-prop l2 (type-Prop P) (is-prop-type-Prop P , lem P)

-- is-small-type-Prop-LEM :
--   {l1 : Level} (l2 : Level) → LEM l1 → is-small l2 (type-Prop l1)
-- is-small-type-Prop-LEM {l1} {l2} lem =
--   ?
--   -- is-small-Π
--   --   (is-small-Prop-LEM l2 lem)
--   --   (λ P → is-small-Π (is-small-Prop-LEM l2 lem) (λ _ → is-small-Prop-LEM l2 lem))
```

### Given LEM, type subtype is small

```agda
is-small-type-subtype-LEM :
  {l1 l2 : Level} {A : UU l1} (P : subtype l2 A) →
  LEM l2 →
  is-small l1 (type-subtype P)
is-small-type-subtype-LEM {l1} {l2} {A} P lem =
  is-small-Σ {l1} {l2} {l1} {l1}
    (is-small' {l1} {A})
    (λ x → is-small-type-Prop-LEM l1 lem (P x))
```

### The unrestricted law of excluded middle does not hold

```agda
abstract
  no-global-decidability :
    {l : Level} → ¬ ((X : UU l) → is-decidable X)
  no-global-decidability {l} d =
    is-not-decidable-type-2-Element-Type (λ X → d (pr1 X))
```
