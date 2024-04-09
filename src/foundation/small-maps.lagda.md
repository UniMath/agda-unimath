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

A map is said to be
{{#concept "small" Disambiguation="map of types" Agda=is-small-map}} if its
[fibers](foundation-core.fibers-of-maps.md) are
[small](foundation-core.small-types.md).

More specifically, a map `f : A → B` is said to be _small_ with respect to a
universe `𝒰` if, for every `b : B`, the fiber of `f` over `y`

```text
  fiber f b ≐ Σ (x : A), (f x ＝ b),
```

is [equivalent](foundation-core.equivalences.md) to a type in `𝒰` that may vary
depending on `b`.

## Definition

```agda
is-small-map :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  (A → B) → UU (lsuc l ⊔ l1 ⊔ l2)
is-small-map l {B = B} f = (b : B) → is-small l (fiber f b)
```

## Properties

### Any map between small types is small

```agda
abstract
  is-small-fiber :
    {l l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-small l A → is-small l B → (b : B) → is-small l (fiber f b)
  is-small-fiber f H K b =
    is-small-Σ H (λ a → is-locally-small-is-small K (f a) b)
```

### Being a small map is a property

```agda
abstract
  is-prop-is-small-map :
    (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
    is-prop (is-small-map l f)
  is-prop-is-small-map l f =
    is-prop-Π (λ x → is-prop-is-small l (fiber f x))

is-small-map-Prop :
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  Prop (lsuc l ⊔ l1 ⊔ l2)
pr1 (is-small-map-Prop l f) = is-small-map l f
pr2 (is-small-map-Prop l f) = is-prop-is-small-map l f
```
