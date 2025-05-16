# Sums of counted families of elements in semirings

```agda
module ring-theory.sums-of-counted-families-in-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import group-theory.sums-of-counted-families-in-commutative-monoids

open import ring-theory.semirings

open import univalent-combinatorics.counting
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="over a counted family of elements of a semiring" WD="sum" WDID=Q218005 Agda=sum-count-Semiring}}
extends the binary addition operation on a [semiring](ring-theory.semirings.md)
`R` to any family of elements of `R` indexed by a
[counted](univalent-combinatorics.counting.md) type.

## Definition

```agda
sum-count-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (A : UU l2) (cA : count A) →
  (A → type-Semiring R) → type-Semiring R
sum-count-Semiring R =
  sum-count-Commutative-Monoid (additive-commutative-monoid-Semiring R)
```
