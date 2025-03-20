# Fibers of globular maps

```agda
{-# OPTIONS --guardedness #-}

open import foundation.function-extensionality-axiom

module
  globular-types.fibers-globular-maps
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.fibers-of-maps funext
open import foundation.identity-types funext
open import foundation.universe-levels

open import globular-types.dependent-globular-types funext
open import globular-types.globular-maps funext
open import globular-types.globular-types
```

</details>

## Idea

Consider a [globular map](globular-types.globular-maps.md) `f : H → G` between
two [globular types](globular-types.globular-types.md) `H` and `G`. The
{{#concept "fiber" Disambiguation="globular map" Agda=fiber-globular-map}} of
`f` is a [dependent globular type](globular-types.dependent-globular-types.md)
`fib_f` given by

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
  ( fiber-globular-map H G f) =
  fiber (0-cell-globular-map f)
1-cell-dependent-globular-type-Dependent-Globular-Type
  ( fiber-globular-map H G f) {x} {x'} (y , refl) (y' , refl) =
  fiber-globular-map
    ( 1-cell-globular-type-Globular-Type H y y')
    ( 1-cell-globular-type-Globular-Type G _ _)
    ( 1-cell-globular-map-globular-map f)
```
