# Left modules over rings with ordered basis

```agda
module linear-algebra.left-modules-with-ordered-bases-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.cartesian-product-types

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-independence-left-modules-rings
open import linear-algebra.linear-spans-left-modules-rings
open import linear-algebra.subsets-left-modules-rings

open import lists.tuples

open import ring-theory.rings
```

</details>

## Idea

A
{{#concept "left module over a ring with an ordered basis" Agda=left-module-with-ordered-basis-Ring}}
is a [left module](linear-algebra.left-modules-rings.md) `M` over a
[ring](ring-theory.rings.md) `R` with a linearly independent tuple whose linear
span is the whole of `M`.

## Definitions

### Left modules over rings with ordered bases

```agda
left-module-with-ordered-basis-Ring :
  {l1 : Level} (n : ℕ) (l : Level) (R : Ring l1) → UU (l1 ⊔ lsuc l)
left-module-with-ordered-basis-Ring {l1} n l R =
  Σ
    ( Σ ( left-module-Ring l R)
        ( λ M → linearly-independent-tuple-left-module-Ring n R M))
    ( λ (M , b) → is-linear-span-subset-left-module-Ring R M
      ( whole-subset-left-module-Ring R M)
      ( subset-tuple (tuple-linearly-independent-tuple R M b)))
```
