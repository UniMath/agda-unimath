# Sums of counted families of elements in commutative semirings

```agda
module commutative-algebra.sums-of-counted-families-in-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import foundation.universe-levels

open import ring-theory.sums-of-counted-families-in-semirings

open import univalent-combinatorics.counting
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="over a counted family of elements of a commutative semiring" WD="sum" WDID=Q218005 Agda=sum-fin-sequence-type-Commutative-Semiring}}
extends the binary addition operation on a
[commutative semiring](commutative-algebra.commutative-semirings.md) `R` to any
family of elements of `R` indexed by a
[counted](univalent-combinatorics.counting.md) type.

## Definition

```agda
sum-count-Commutative-Semiring :
  {l1 l2 : Level} (R : Commutative-Semiring l1) (A : UU l2) → count A →
  (A → type-Commutative-Semiring R) → type-Commutative-Semiring R
sum-count-Commutative-Semiring R =
  sum-count-Semiring (semiring-Commutative-Semiring R)
```
