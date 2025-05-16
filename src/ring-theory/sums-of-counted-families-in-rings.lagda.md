# Sums of counted families of elements in rings

```agda
module ring-theory.sums-of-counted-families-in-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import ring-theory.rings
open import ring-theory.sums-of-counted-families-in-semirings

open import univalent-combinatorics.counting
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="over a counted family of elements of a ring" WD="sum" WDID=Q218005 Agda=sum-fin-sequence-type-Ring}}
extends the binary addition operation on a [ring](ring-theory.rings.md) `R` to
any family of elements of `R` indexed by a
[counted](univalent-combinatorics.counting.md) type.

## Definition

```agda
sum-count-Ring :
  {l1 l2 : Level} (R : Ring l1) (A : UU l2) → count A → (A → type-Ring R) →
  type-Ring R
sum-count-Ring R = sum-count-Semiring (semiring-Ring R)
```
