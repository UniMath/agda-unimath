# Standard ternary pullbacks

```agda
module foundation.standard-ternary-pullbacks where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cones-over-cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.functoriality-cartesian-product-types
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.commuting-squares-of-maps
open import foundation-core.diagonal-maps-cartesian-products-of-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections
open import foundation-core.type-theoretic-principle-of-choice
open import foundation-core.universal-property-pullbacks
open import foundation-core.whiskering-identifications-concatenation
```

</details>

## Idea

Given two [cospan of types](foundation.cospans.md) with a shared vertex `B`:

```text
      f       g       h       i
  A ----> X <---- B ----> Y <---- C,
```

we call the standard limit of the diagram the
{{#concept "standard ternary pullback" Disambiguation="of types" Agda=standard-ternary-pullback}}.
It is defined as the [sum](foundation.dependent-pair-types.md)

```text
  standard-ternary-pullback f g h i :=
    Σ (a : A) (b : B) (c : C), ((f a ＝ g b) × (h b ＝ i c)).
```

## Definitions

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {X : UU l1} {Y : UU l2} {A : UU l3} {B : UU l4} {C : UU l5}
  (f : A → X) (g : B → X) (h : B → Y) (i : C → Y)
  where

  standard-ternary-pullback : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4 ⊔ l5)
  standard-ternary-pullback =
    Σ A (λ a → Σ B (λ b → Σ C (λ c → (f a ＝ g b) × (h b ＝ i c))))
```

## See also

- [Type arithmetic with standard pullbacks](foundation.type-arithmetic-standard-pullbacks.md)

## Table of files about pullbacks

The following table lists files that are about pullbacks as a general concept.

{{#include tables/pullbacks.md}}
