# Small maps

```agda
module foundation.small-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.locally-small-types
open import foundation.retracts-of-arrows
open import foundation.split-idempotent-maps
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

More specifically, a map `f : A → B` is _small_ with respect to a universe `𝒰`
if, for every `b : B`, the fiber of `f` over `y`

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
module _
  (l : Level) {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  abstract
    is-prop-is-small-map : is-prop (is-small-map l f)
    is-prop-is-small-map = is-prop-Π (λ x → is-prop-is-small l (fiber f x))

  is-small-map-Prop : Prop (lsuc l ⊔ l1 ⊔ l2)
  is-small-map-Prop = is-small-map l f , is-prop-is-small-map
```

### Small maps are closed under retracts of arrows

```agda
module _
  {l1 l2 l3 l4 l : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  {f : A → B} {g : X → Y} (R : f retract-of-arrow g)
  where

  is-small-map-retract : is-small-map l g → is-small-map l f
  is-small-map-retract is-small-g b =
    is-small-retract
      ( is-small-g (map-codomain-inclusion-retract-arrow f g R b))
      ( retract-fiber-retract-arrow f g R b)
```
