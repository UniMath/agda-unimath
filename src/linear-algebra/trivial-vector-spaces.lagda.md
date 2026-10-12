# Trivial vector spaces

```agda
module linear-algebra.trivial-vector-spaces where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.heyting-fields

open import foundation.propositions
open import foundation.universe-levels

open import linear-algebra.trivial-left-modules-rings
open import linear-algebra.vector-spaces
```

</details>

## Idea

The
{{#concept "trivial vector space" Disambiguation="over a Heyting field" Agda=trivial-Vector-Space}}
over a [Heyting field](commutative-algebra.heyting-fields.md) `K` is the
[vector space](linear-algebra.vector-spaces.md) over `K` consisting of exactly
one element, `0`.

## Definition

### The property of being a trivial vector space

```agda
module _
  {l1 l2 : Level}
  (K : Heyting-Field l1)
  (V : Vector-Space l2 K)
  where

  is-trivial-prop-Vector-Space : Prop l2
  is-trivial-prop-Vector-Space =
    is-trivial-prop-left-module-Ring (ring-Heyting-Field K) V

  is-trivial-Vector-Space : UU l2
  is-trivial-Vector-Space = type-Prop is-trivial-prop-Vector-Space
```

### The trivial vector space

```agda
module _
  {l : Level}
  (K : Heyting-Field l)
  where

  trivial-Vector-Space : Vector-Space lzero K
  trivial-Vector-Space = trivial-left-module-Ring (ring-Heyting-Field K)

  is-trivial-trivial-Vector-Space :
    is-trivial-Vector-Space K trivial-Vector-Space
  is-trivial-trivial-Vector-Space =
    is-trivial-trivial-left-module-Ring (ring-Heyting-Field K)
```
