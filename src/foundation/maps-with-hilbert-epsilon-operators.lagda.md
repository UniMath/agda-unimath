# Maps with Hilbert ε-operators

```agda
module foundation.maps-with-hilbert-epsilon-operators where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.cartesian-morphisms-arrows
open import foundation.coproduct-types
open import foundation.decidable-dependent-pair-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-coproduct-types
open import foundation.hilberts-epsilon-operators
open import foundation.identity-types
open import foundation.mere-equality
open import foundation.pi-0-trivial-maps
open import foundation.propositional-truncations
open import foundation.retracts-of-maps
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import foundation-core.contractible-maps
open import foundation-core.contractible-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.homotopies
open import foundation-core.injective-maps
open import foundation-core.iterating-functions
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

We consider maps `f : A → B` [equippes](foundation.structure.md) with
[Hilbert ε-operators](foundation.hilberts-epsilon-operators.md) on its
[fibers](foundation-core.fibers-of-maps.md). I.e., for every `y : B` there is an
operator

```text
  ε_y : ║ fiber f y ║₋₁ → fiber f y
```

## Definitions

### The structure of an Hilbert ε-operator on a map

```agda
ε-operator-map-Hilbert :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
ε-operator-map-Hilbert {B = B} f = (y : B) → ε-operator-Hilbert (fiber f y)
```
