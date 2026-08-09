# Freely generated vector spaces

```agda
module linear-algebra.freely-generated-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.universe-levels

open import linear-algebra.freely-generated-left-modules-rings
open import linear-algebra.universal-property-free-vector-spaces
open import linear-algebra.vector-spaces
```

</details>

## Idea

The {{#concept "freely generated vector space" Agda=free-Vector-Space}} over a
[Heyting field](commutative-algebra.heyting-fields.md) `K` with generator type
`G` is a canonical construction of a
[vector space](linear-algebra.vector-spaces.md) satisfying the
[universal property of freely generated vector spaces](linear-algebra.universal-property-free-vector-spaces.md).
Notably, this is equivalent to the direct sum of copies of `K` as a vector space
over itself indexed by `G`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (K : Heyting-Field l1)
  (G : UU l2)
  where

  opaque
    free-Vector-Space : Vector-Space (l1 ⊔ l2) K
    free-Vector-Space = free-left-module-Ring (ring-Heyting-Field K) G

  type-free-Vector-Space : UU (l1 ⊔ l2)
  type-free-Vector-Space = type-Vector-Space K free-Vector-Space

  opaque
    unfolding free-Vector-Space

    in-free-Vector-Space : G → type-free-Vector-Space
    in-free-Vector-Space = in-free-left-module-Ring (ring-Heyting-Field K) G

    is-free-free-Vector-Space :
      is-free-Vector-Space K G free-Vector-Space in-free-Vector-Space
    is-free-free-Vector-Space =
      is-free-free-left-module-Ring (ring-Heyting-Field K) G
```
