# The replacement axiom for type theory

```agda
module foundation.replacement where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.homotopies
open import foundation.images
open import foundation.locally-small-types
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.small-types
```

</details>

## Idea

The type theoretic replacement axiom asserts that the image of a map `f : A → B` from a small type `A` into a locally small type `B` is small.

## Definition

```agda
Replacement : (l : Level) → UUω
Replacement l =
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-small l A → is-locally-small l B → is-small l (im f)

postulate replacement : {l : Level} → Replacement l

replacement-UU :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  is-locally-small l1 B → is-small l1 (im f)
replacement-UU {l1} {l2} {A} f = replacement f is-small'
```
