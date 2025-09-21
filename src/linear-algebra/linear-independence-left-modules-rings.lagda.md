# Linear independence

```agda
module linear-algebra.linear-independence-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.distance-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.negation
open import foundation.propositions
open import foundation.universe-levels

open import foundation-core.empty-types
open import foundation-core.sets

open import linear-algebra.left-modules-rings
open import linear-algebra.linear-combinations-tuples-of-vectors-left-modules-rings
open import linear-algebra.subsets-left-modules-rings

open import lists.concatenation-tuples
open import lists.functoriality-tuples
open import lists.tuples

open import ring-theory.rings
open import ring-theory.trivial-rings

open import univalent-combinatorics.standard-finite-types
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
      ( λ scalars →
        hom-Prop
          ( Id-Prop
            ( set-left-module-Ring R M)
            ( linear-combination-tuple-left-module-Ring R M scalars vectors)
            ( zero-left-module-Ring R M))
          ( Id-Prop
            ( tuple-Set (set-Ring R) n)
            ( scalars)
            ( trivial-tuple-Ring R n)))
  is-linearly-independent-tuple-left-module-Ring : UU (l1 ⊔ l2)
  is-linearly-independent-tuple-left-module-Ring =
    type-Prop is-linearly-independent-tuple-left-module-prop-Ring
```

### Linearly independent tuple in a left module over a ring

```agda
linearly-independent-tuple-left-module-Ring :
  {l1 l2 : Level}
  (R : Ring l1) (M : left-module-Ring l2 R) (n : ℕ) → UU (l1 ⊔ l2)
linearly-independent-tuple-left-module-Ring R M n =
  Σ ( tuple (type-left-module-Ring R M) n)
    ( λ v → is-linearly-independent-tuple-left-module-Ring R M v)

module _
  {l1 l2 : Level}
  {n : ℕ}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  (vectors : linearly-independent-tuple-left-module-Ring R M n)
  where

  tuple-linearly-independent-tuple : tuple (type-left-module-Ring R M) n
  tuple-linearly-independent-tuple = pr1 vectors
```

### The condition on a subset of being linearly independent

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

### Linearly independent subsets of a left module over a ring

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

## Properties

### A tuple with a repeating element is linearly dependent

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  non-trivial-tuple-linearly-dependent-repeated-element-tuple-left-module-Ring :
    (n : ℕ) → (i j : Fin n) → tuple (type-Ring R) n
  non-trivial-tuple-linearly-dependent-repeated-element-tuple-left-module-Ring
    n i j =
    ( with-value-tuple i
      ( one-Ring R)
      ( with-value-tuple j (neg-one-Ring R) (trivial-tuple-Ring R n)))

  gives-zero-linearly-dependent-repeated-element-tuple :
    (n : ℕ) →
    (vectors : tuple (type-left-module-Ring R M) n) →
    (i j : Fin n) →
    (i ≠ j) →
    (component-tuple n vectors i ＝ component-tuple n vectors j) →
    linear-combination-tuple-left-module-Ring R M
      ( non-trivial-tuple-linearly-dependent-repeated-element-tuple-left-module-Ring
        ( n)
        ( i)
        ( j))
      ( vectors) ＝
    zero-left-module-Ring R M
  gives-zero-linearly-dependent-repeated-element-tuple
    n vectors i j i≠j identity =
    {! !}

  linearly-dependent-repeated-element-tuple-left-module-Ring :
    (is-nontrivial-Ring R) →
    (n : ℕ) →
    (vectors : tuple (type-left-module-Ring R M) n) →
    (i j : Fin n) →
    (i ≠ j) →
    (component-tuple n vectors i ＝ component-tuple n vectors j) →
    ¬ is-linearly-independent-tuple-left-module-Ring R M vectors
  linearly-dependent-repeated-element-tuple-left-module-Ring
    zero-is-not-one n vectors i j i≠j identity implies-trivial-tuple =
    zero-is-not-one
      ( equational-reasoning
        zero-Ring R
        ＝ component-tuple n (trivial-tuple-Ring R n) i
          by zero-component-trivial-tuple n i
        ＝ component-tuple n
            ( non-trivial-tuple-linearly-dependent-repeated-element-tuple-left-module-Ring
              ( n)
              ( i)
              ( j))
            ( i)
          by
            eq-component-eq-tuple
              ( n)
              ( i)
              ( trivial-tuple-Ring R n)
              ( non-trivial-tuple-linearly-dependent-repeated-element-tuple-left-module-Ring
                ( n)
                ( i)
                ( j))
              ( inv
                ( implies-trivial-tuple
                  ( non-trivial-tuple-linearly-dependent-repeated-element-tuple-left-module-Ring
                    ( n)
                    ( i)
                    ( j))
                  ( gives-zero-linearly-dependent-repeated-element-tuple
                    ( n)
                    ( vectors)
                    ( i)
                    ( j)
                    ( i≠j)
                    ( identity))))
        ＝ component-tuple n
          ( with-value-tuple i (one-Ring R)
            ( with-value-tuple j (neg-one-Ring R) (trivial-tuple-Ring R n)))
          ( i)
          by refl
        ＝ one-Ring R
          by
            component-tuple-with-value-identity-tuple
              ( with-value-tuple j (neg-one-Ring R) (trivial-tuple-Ring R n))
              ( i)
              ( one-Ring R))
```

### An empty tuple is linearly independent

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  linearly-independent-empty-tuple-left-module-Ring :
    tuple (type-left-module-Ring R M) zero-ℕ →
    linearly-independent-tuple-left-module-Ring R M zero-ℕ
  pr1 (linearly-independent-empty-tuple-left-module-Ring vectors) = vectors
  pr2 (linearly-independent-empty-tuple-left-module-Ring vectors)
    scalars identity = zero-empty-tuple scalars
```

### An empty subset is linearly independent

```agda
module _
  {l1 l2 : Level}
  (R : Ring l1)
  (M : left-module-Ring l2 R)
  where

  linearly-independent-empty-subset-left-module-Ring :
    {l : Level} →
    (S : subset-left-module-Ring l R M) →
    is-empty (type-subset-left-module-Ring R M S) →
    linearly-independent-subset-left-module-Ring l R M
  pr1 (linearly-independent-empty-subset-left-module-Ring S empty) = S
  pr2 (linearly-independent-empty-subset-left-module-Ring S empty)
    zero-ℕ vectors scalars identity = zero-empty-tuple scalars
  pr2 (linearly-independent-empty-subset-left-module-Ring S empty)
    (succ-ℕ n) (x ∷ vectors) scalars identity = ex-falso (empty x)
```
