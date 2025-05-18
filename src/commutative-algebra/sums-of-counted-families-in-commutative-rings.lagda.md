# Sums of counted families of elements in commutative rings

```agda
module commutative-algebra.sums-of-counted-families-in-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.universe-levels

open import ring-theory.sums-of-counted-families-in-rings

open import univalent-combinatorics.counting
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="over a counted family of elements of a commutative ring" WD="sum" WDID=Q218005 Agda=sum-count-Commutative-Ring}}
extends the binary addition operation on a
[commutative ring](commutative-algebra.commutative-rings.md) `A` to any family
of elements of `A` indexed by a
[counted type](univalent-combinatorics.counting.md).

## Definition

```agda
sum-count-Commutative-Ring :
  {l1 l2 : Level} (R : Commutative-Ring l1) (A : UU l2) → count A →
  (A → type-Commutative-Ring R) → type-Commutative-Ring R
sum-count-Commutative-Ring R = sum-count-Ring (ring-Commutative-Ring R)
```
