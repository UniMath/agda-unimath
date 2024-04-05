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
open import foundation.universe-levels

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
```

## Properties

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

### TODO: Given LEM, Prop equiv Decidable-Prop

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
```

### The unrestricted law of excluded middle does not hold

```agda
abstract
  no-global-decidability :
    {l : Level} → ¬ ((X : UU l) → is-decidable X)
  no-global-decidability {l} d =
    is-not-decidable-type-2-Element-Type (λ X → d (pr1 X))
```
