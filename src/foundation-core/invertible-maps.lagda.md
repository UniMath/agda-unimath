# Invertible maps

```agda
module foundation-core.invertible-maps where

```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation.action-on-identifications-functions
open import foundation-core.cartesian-product-types
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
```

</details>

## Idea

An **inverse** for a map `f : A → B` is a map `g : B → A` equipped with
[homotopies](foundation-core.homotopies.md) ` (f ∘ g) ~ id` and `(g ∘ f) ~ id`.
Such data, however is [structure](foundation.structure.md) on the map `f`, and
not a [property](foundation-core.propositions.md).

## Definition

### The type of inverse proofs

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

### The type of inverses of a map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  has-inverse : (A → B) → UU (l1 ⊔ l2)
  has-inverse f = Σ (B → A) (is-inverse f)

  map-inv-has-inverse : {f : A → B} → has-inverse f → B → A
  map-inv-has-inverse = pr1

  is-inverse-map-inv-has-inverse :
    {f : A → B} (g : has-inverse f) → is-inverse f (map-inv-has-inverse g)
  is-inverse-map-inv-has-inverse = pr2

  is-retraction-has-inverse :
    {f : A → B} (has-inverse-f : has-inverse f) →
    (f ∘ map-inv-has-inverse has-inverse-f) ~ id
  is-retraction-has-inverse = pr1 ∘ is-inverse-map-inv-has-inverse

  is-section-has-inverse :
    {f : A → B} (has-inverse-f : has-inverse f) →
    (map-inv-has-inverse has-inverse-f ∘ f) ~ id
  is-section-has-inverse = pr2 ∘ is-inverse-map-inv-has-inverse
```

### The type of invertible maps

```agda
invertible-map : {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (l1 ⊔ l2)
invertible-map A B = Σ (A → B) (has-inverse)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  map-invertible-map : invertible-map A B → A → B
  map-invertible-map = pr1

  has-inverse-map-invertible-map : (f : invertible-map A B) → has-inverse (map-invertible-map f)
  has-inverse-map-invertible-map = pr2

  map-inv-invertible-map : invertible-map A B → B → A
  map-inv-invertible-map = map-inv-has-inverse ∘ has-inverse-map-invertible-map

  is-section-map-invertible-map :
    (f : invertible-map A B) →
    (map-inv-invertible-map f ∘ map-invertible-map f) ~ id
  is-section-map-invertible-map =
    is-section-has-inverse ∘ has-inverse-map-invertible-map

  is-retraction-map-invertible-map :
    (f : invertible-map A B) →
    (map-invertible-map f ∘ map-inv-invertible-map f) ~ id
  is-retraction-map-invertible-map =
    is-retraction-has-inverse ∘ has-inverse-map-invertible-map
```

## Properties

### The iterated inverse invertible map

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} {f : A → B}
  where

  is-section-map-inv-has-inverse :
    (H : has-inverse f) → (f ∘ map-inv-has-inverse H) ~ id
  is-section-map-inv-has-inverse H y =
    ( inv (is-retraction-has-inverse H (f (map-inv-has-inverse H y)))) ∙
    ( ( ap f (is-section-has-inverse H (map-inv-has-inverse H y))) ∙
      ( is-retraction-has-inverse H y))

  is-retraction-map-inv-has-inverse :
    (H : has-inverse f) → (map-inv-has-inverse H ∘ f) ~ id
  is-retraction-map-inv-has-inverse = is-section-has-inverse

  inv-is-inverse : {g : B → A} → is-inverse f g → is-inverse g f
  pr1 (inv-is-inverse {g} H) = is-retraction-map-inv-has-inverse (g , H)
  pr2 (inv-is-inverse {g} H) = is-section-map-inv-has-inverse (g , H)

  inv-has-inverse : (g : has-inverse f) → has-inverse (map-inv-has-inverse g)
  pr1 (inv-has-inverse g) = f
  pr2 (inv-has-inverse g) = inv-is-inverse (is-inverse-map-inv-has-inverse g)
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
