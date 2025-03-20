# Constant span diagrams

```agda
open import foundation.function-extensionality-axiom

module
  foundation.constant-span-diagrams
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext
open import foundation.dependent-pair-types
open import foundation.span-diagrams funext
open import foundation.spans
open import foundation.universe-levels

open import foundation-core.equivalences
```

</details>

## Idea

The {{#concept "constant span diagram" Agda=constant-span-diagram}} at a type
`X` is the [span diagram](foundation.span-diagrams.md)

```text
      id       id
  X <----- X -----> X.
```

Alternatively, a span diagram

```text
       f       g
  A <----- S -----> B
```

is said to be constant if both `f` and `g` are
[equivalences](foundation-core.equivalences.md).

## Definitions

### Constant span diagrams at a type

```agda
module _
  {l1 : Level}
  where

  constant-span-diagram : UU l1 → span-diagram l1 l1 l1
  pr1 (constant-span-diagram X) = X
  pr1 (pr2 (constant-span-diagram X)) = X
  pr2 (pr2 (constant-span-diagram X)) = id-span
```

### The predicate of being a constant span diagram

```agda
module _
  {l1 l2 l3 : Level} (𝒮 : span-diagram l1 l2 l3)
  where

  is-constant-span-diagram : UU (l1 ⊔ l2 ⊔ l3)
  is-constant-span-diagram =
    is-equiv (left-map-span-diagram 𝒮) × is-equiv (right-map-span-diagram 𝒮)
```
