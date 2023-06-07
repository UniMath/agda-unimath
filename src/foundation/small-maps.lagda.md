# Small maps

```agda
module foundation.small-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.locally-small-types
open import foundation.universe-levels

open import foundation-core.fibers-of-maps
open import foundation-core.propositions
open import foundation-core.small-types
```

</details>

## Idea

A map is said to be small if its fibers are small.

## Definition

```agda
is-small-map :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → UU (lsuc l ⊔ l1 ⊔ l2)
is-small-map l {B = B} f = (b : B) → is-small l (fib f b)
```

## Properties

### Any map between small types is small

```agda
abstract
  is-small-fib :
    (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-small l A → is-small l B → (b : B) → is-small l (fib f b)
  is-small-fib l f H K b =
    is-small-Σ H (λ a → is-locally-small-is-small K (f a) b)
```

### Being a small map is a property

```agda
abstract
  is-prop-is-small-map :
    (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-prop (is-small-map l f)
  is-prop-is-small-map l f =
    is-prop-Π (λ x → is-prop-is-small l (fib f x))

is-small-map-Prop :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  Prop (lsuc l ⊔ l1 ⊔ l2)
pr1 (is-small-map-Prop l f) = is-small-map l f
pr2 (is-small-map-Prop l f) = is-prop-is-small-map l f
```
