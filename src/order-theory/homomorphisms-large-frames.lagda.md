# Homomorphisms of large frames

```agda
module order-theory.homomorphisms-large-frames where
```

<details><summary>Imports</summary>

```agda
open import foundation.functions
open import foundation.universe-levels

open import order-theory.large-frames
open import order-theory.order-preserving-maps-large-posets
```

</details>

## Idea

A **homomorphism of large frames** from `K` to `L` is an order preserving map from `K` to `L` which preserves meets, the top element, and suprema.

## Definitions

### The predicate of being a frame homomorphism

```agda
module _
  {αK αL : Level → Level} {βK βL : Level → Level → Level}
  (K : Large-Frame αK βK) (L : Large-Frame αL βL)
  where

  is-frame-homomorphism-hom-Large-Poset :
    hom-Large-Poset id
      ( large-poset-Large-Frame K)
      ( large-poset-Large-Frame L) → UUω
```
