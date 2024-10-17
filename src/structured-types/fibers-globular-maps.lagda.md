# Fibers of globular maps

```agda
{-# OPTIONS --guardedness #-}

module structured-types.fibers-globular-maps where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps
open import foundation.identity-types
open import foundation.universe-levels

open import structured-types.dependent-globular-types
open import structured-types.globular-maps
open import structured-types.globular-types
```

</details>

## Idea

Consider a [globular map](structured-types.globular-maps.md) `f : H → G` between two [globular types](structured-types.globular-types.md) `H` and `G`. The {{#concept "fiber" Disambiguation="globular map" Agda=fiber-globular-map}} of `f` is a [dependent globular type](structured-types.dependent-globular-types.md) `fib_f` given by

```text
  (fib_f)₀ x := fib f₀ x
  (fib_f)' (y , refl) (y' , refl) := fib_f'.
```

## Definitions

### The fiber of a globular map

```agda
fiber-globular-map :
  {l1 l2 l3 l4 : Level}
  (H : Globular-Type l1 l2) (G : Globular-Type l3 l4)
  (f : globular-map H G) →
  Dependent-Globular-Type (l1 ⊔ l3) (l2 ⊔ l4) G
0-cell-Dependent-Globular-Type
  ( fiber-globular-map H G f)=
  fiber (0-cell-globular-map f)
1-cell-dependent-globular-type-Dependent-Globular-Type
  ( fiber-globular-map H G f) {x} {x'} (y , refl) (y' , refl) =
  fiber-globular-map
    ( 1-cell-globular-type-Globular-Type H y y')
    ( 1-cell-globular-type-Globular-Type G _ _)
    ( 1-cell-globular-map-globular-map f)
```
