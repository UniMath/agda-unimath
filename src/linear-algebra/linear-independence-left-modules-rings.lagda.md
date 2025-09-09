# Linear independence

```agda
module linear-algebra.linear-independence-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.sets

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-combinations-tuples-of-vectors-left-modules-rings

open import lists.tuples

open import ring-theory.rings
```

</details>

## Idea

Let `M` be a [left module](linear-algebra.left-modules-rings.md) over a
[ring](ring-theory.rings.md) `R`. A tuple `x_1, ..., x_n` of elements of `M` is
{{#concept "linearly independent" Agda=is-linearly-independent-tuple-prop Agda=linearly-independent-tuple}},
if `r_1 * x_1 + ... + r_n * x_n = 0` implies `r_1 = ... = r_n = 0`.

## Definitions

### The condition of a tuple being linearly independent

```agda
module _
  {l1 l2 : Level}
  {n : ℕ}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (vectors : tuple (type-left-module-Ring R M) n)
  where

  is-linearly-independent-tuple-left-module-Ring-prop : Prop (l1 ⊔ l2)
  is-linearly-independent-tuple-left-module-Ring-prop =
    Π-Prop
      ( tuple (type-Ring R) n)
      λ scalars →
        hom-Prop
          ( Id-Prop
            ( set-left-module-Ring R M)
            ( linear-combination-tuple-left-module-Ring R M scalars vectors)
            ( zero-left-module-Ring R M))
          ( Id-Prop
            ( tuple-Set (set-Ring R) n)
            ( scalars)
            ( trivial-tuple-left-module-Ring R M n))

  is-linearly-independent-tuple-left-module-Ring : UU (l1 ⊔ l2)
  is-linearly-independent-tuple-left-module-Ring =
    type-Prop is-linearly-independent-tuple-left-module-Ring-prop
```

### Linearly independent tuple in a left-module over ring

```agda
linearly-independent-tuple-left-module-Ring :
  {l1 l2 : Level}
  (n : ℕ) (R : Ring l1) (M : left-module-Ring l2 R) → UU (l1 ⊔ l2)
linearly-independent-tuple-left-module-Ring n R M =
  Σ
    ( tuple (type-left-module-Ring R M) n)
    ( λ v → is-linearly-independent-tuple-left-module-Ring R M v)

module _
  {l1 l2 : Level}
  {n : ℕ}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (v : linearly-independent-tuple-left-module-Ring n R M)
  where

  tuple-linearly-independent-tuple : tuple (type-left-module-Ring R M) n
  tuple-linearly-independent-tuple = pr1 v
```
