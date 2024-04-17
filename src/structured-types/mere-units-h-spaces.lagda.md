# Mere units of H-spaces

```agda
module structured-types.mere-units-h-spaces where
```

<details><summary>Imports</summary>

```agda
open import foundation.connected-components
open import foundation.dependent-pair-types
open import foundation.mere-equality
open import foundation.propositions
open import foundation.universe-levels

open import structured-types.h-spaces
```

</details>

## Idea

A {{#concept "mere unit" Disambiguation="H-space"}} in an [H-space](structured-types.h-spaces.md) `A` is an element `x` that is [merely equal](foundation.mere-equality.md) to the unit element of `A`. The type of mere units of an H-space always forms a [connected H-space](structured-types.connected-h-spaces.md).

## Definitions

### The predicate of being a mere unit of an H-space

```agda
module _
  {l1 : Level} (A : H-Space l1)
  where

  is-mere-unit-prop-H-Space : type-H-Space A → Prop l1
  is-mere-unit-prop-H-Space x = mere-eq-Prop (unit-H-Space A) x

  is-mere-unit-H-Space : type-H-Space A → UU l1
  is-mere-unit-H-Space x = mere-eq (unit-H-Space A) x

  is-prop-is-mere-unit-H-Space :
    (x : type-H-Space A) → is-prop (is-mere-unit-H-Space x)
  is-prop-is-mere-unit-H-Space x =
    is-prop-mere-eq (unit-H-Space A) x
```

### The type of mere units of an H-space

```agda
module _
  {l1 : Level} (A : H-Space l1)
  where

  mere-unit-H-Space : UU l1
  mere-unit-H-Space = Σ (type-H-Space A) (is-mere-unit-H-Space A)
```

### The connected component of the unit of an H-Space

```agda
module _
  {l1 : Level} (A : H-Space l1)
  where

  connected-component-unit-H-Space : UU l1
  connected-component-unit-H-Space =
    connected-component (type-H-Space A) (unit-H-Space A)
```
