# Invertible maps

```agda
module foundation-core.invertible-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.retractions
open import foundation-core.sections
```

</details>

## Idea

An **inverse** for a map `f : A → B` is a map `g : B → A` equipped with
[homotopies](foundation-core.homotopies.md) ` (f ∘ g) ~ id` and `(g ∘ f) ~ id`.
Such data, however is [structure](foundation.structure.md) on the map `f`, and
not generally a [property](foundation-core.propositions.md).

## Definition

### The predicate that a map `g` is an inverse of a map `f`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-inverse : (A → B) → (B → A) → UU (l1 ⊔ l2)
  is-inverse f g = ((f ∘ g) ~ id) × ((g ∘ f) ~ id)

  is-section-is-inverse :
    {f : A → B} {g : B → A} → is-inverse f g → (f ∘ g) ~ id
  is-section-is-inverse = pr1

  is-retraction-is-inverse :
    {f : A → B} {g : B → A} → is-inverse f g → (g ∘ f) ~ id
  is-retraction-is-inverse = pr2
```

### The predicate that a map `f` is invertible

```agda
is-invertible :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → (A → B) → UU (l1 ⊔ l2)
is-invertible {A = A} {B} f = Σ (B → A) (is-inverse f)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B} (g : is-invertible f)
  where

  map-inv-is-invertible : B → A
  map-inv-is-invertible = pr1 g

  is-inverse-map-inv-is-invertible : is-inverse f map-inv-is-invertible
  is-inverse-map-inv-is-invertible = pr2 g

  is-retraction-is-invertible : (f ∘ map-inv-is-invertible) ~ id
  is-retraction-is-invertible = pr1 is-inverse-map-inv-is-invertible

  is-section-is-invertible : (map-inv-is-invertible ∘ f) ~ id
  is-section-is-invertible = pr2 is-inverse-map-inv-is-invertible

  section-is-invertible : section f
  pr1 section-is-invertible = map-inv-is-invertible
  pr2 section-is-invertible = is-retraction-is-invertible

  retraction-is-invertible : retraction f
  pr1 retraction-is-invertible = map-inv-is-invertible
  pr2 retraction-is-invertible = is-section-is-invertible
```

### The type of invertible maps

```agda
invertible-map : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
invertible-map A B = Σ (A → B) (is-invertible)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-invertible-map : invertible-map A B → A → B
  map-invertible-map = pr1

  is-invertible-map-invertible-map :
    (f : invertible-map A B) → is-invertible (map-invertible-map f)
  is-invertible-map-invertible-map = pr2

  map-inv-invertible-map : invertible-map A B → B → A
  map-inv-invertible-map =
    map-inv-is-invertible ∘ is-invertible-map-invertible-map

  is-section-map-invertible-map :
    (f : invertible-map A B) →
    (map-inv-invertible-map f ∘ map-invertible-map f) ~ id
  is-section-map-invertible-map =
    is-section-is-invertible ∘ is-invertible-map-invertible-map

  is-retraction-map-invertible-map :
    (f : invertible-map A B) →
    (map-invertible-map f ∘ map-inv-invertible-map f) ~ id
  is-retraction-map-invertible-map =
    is-retraction-is-invertible ∘ is-invertible-map-invertible-map
```

## Properties

### The invertible inverse of an invertible map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  inv-is-inverse : {g : B → A} → is-inverse f g → is-inverse g f
  pr1 (inv-is-inverse {g} H) = is-section-is-invertible (g , H)
  pr2 (inv-is-inverse {g} H) = is-retraction-is-invertible (g , H)

  inv-is-invertible :
    (g : is-invertible f) → is-invertible (map-inv-is-invertible g)
  pr1 (inv-is-invertible g) = f
  pr2 (inv-is-invertible g) =
    inv-is-inverse (is-inverse-map-inv-is-invertible g)
```

## See also

- For the coherent notion of invertible maps see
  [`foundation.coherently-invertible-maps`](foundation.coherently-invertible-maps.md).
- For the notion of biinvertible maps see
  [`foundation.equivalences`](foundation.equivalences.md).
- For the notion of maps with contractible fibers see
  [`foundation.contractible-maps`](foundation.contractible-maps.md).
- For the notion of path-split maps see
  [`foundation.path-split-maps`](foundation.path-split-maps.md).
