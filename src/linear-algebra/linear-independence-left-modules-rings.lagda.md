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
open import linear-algebra.subsets-left-modules-rings
open import linear-algebra.linear-combinations-tuples-of-vectors-left-modules-rings

open import lists.tuples
open import lists.functoriality-tuples

open import ring-theory.rings
```

</details>

## Idea

Let `M` be a [left module](linear-algebra.left-modules-rings.md) over a
[ring](ring-theory.rings.md) `R`.

A tuple `x_1, ..., x_n` of elements of `M` is a
{{#concept "linearly independent tuple" Agda=is-linearly-independent-tuple-left-module-prop-Ring Agda=linearly-independent-tuple-left-module-Ring}},
if `r_1 * x_1 + ... + r_n * x_n = 0` implies `r_1 = ... = r_n = 0`.

A subset `S` of `M` is a
{{#concept "linearly independent subset" Agda=is-linearly-independent-subset-left-module-prop-Ring Agda=linearly-independent-subset-left-module-Ring}}
if any tuple `x_1, ..., x_n` of elements of `S` is linearly independent.

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

  is-linearly-independent-tuple-left-module-prop-Ring : Prop (l1 ⊔ l2)
  is-linearly-independent-tuple-left-module-prop-Ring =
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
    type-Prop is-linearly-independent-tuple-left-module-prop-Ring
```

### Linearly independent tuple in a left-module over a ring

```agda
linearly-independent-tuple-left-module-Ring :
  {l1 l2 : Level}
  (n : ℕ) (R : Ring l1) (M : left-module-Ring l2 R) → UU (l1 ⊔ l2)
linearly-independent-tuple-left-module-Ring n R M =
  Σ ( tuple (type-left-module-Ring R M) n)
    ( λ v → is-linearly-independent-tuple-left-module-Ring R M v)

module _
  {l1 l2 : Level}
  {n : ℕ}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (vectors : linearly-independent-tuple-left-module-Ring n R M)
  where

  tuple-linearly-independent-tuple : tuple (type-left-module-Ring R M) n
  tuple-linearly-independent-tuple = pr1 vectors
```

### The condition of a subset being linearly independent

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (S : subset-left-module-Ring l3 R M)
  where

  is-linearly-independent-subset-left-module-prop-Ring : Prop (l1 ⊔ l2 ⊔ l3)
  is-linearly-independent-subset-left-module-prop-Ring =
    Π-Prop
      ( ℕ)
      ( λ n →
        Π-Prop
          ( tuple (type-subset-left-module-Ring R M S) n)
          ( λ vectors → is-linearly-independent-tuple-left-module-prop-Ring R M
            ( map-tuple (inclusion-subset-left-module-Ring R M S) vectors)))

  is-linearly-independent-subset-left-module-Ring : UU (l1 ⊔ l2 ⊔ l3)
  is-linearly-independent-subset-left-module-Ring =
    type-Prop is-linearly-independent-subset-left-module-prop-Ring
```

### Linearly independent subset of a left module over a ring

```agda
linearly-independent-subset-left-module-Ring :
  {l1 l2 : Level}
  (l3 : Level) (R : Ring l1) (M : left-module-Ring l2 R) →
  UU (l1 ⊔ l2 ⊔ lsuc l3)
linearly-independent-subset-left-module-Ring l3 R M =
  Σ ( subset-left-module-Ring l3 R M)
    ( λ S → is-linearly-independent-subset-left-module-Ring R M S)

module _
  {l1 l2 l3 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (S : linearly-independent-subset-left-module-Ring l3 R M)
  where

  subset-linearly-independent-tuple : subset-left-module-Ring l3 R M
  subset-linearly-independent-tuple = pr1 S
```
