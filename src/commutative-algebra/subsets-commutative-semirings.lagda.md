# Subsets of commutative semirings

```agda
module commutative-algebra.subsets-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import foundation.action-on-identifications-functions
open import foundation.dependent-products-propositions
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.subsets-semirings
```

</details>

## Idea

A {{#concept "subset" Disambiguation="commutative semiring" Agda=subset-Commutative-Semiring}} of a [commutative semiring](commutative-algebra.commutative-semirings.md) is a [subtype](foundation-core.subtypes.md) of its underlying type.

## Definitions

### Subsets of commutative semirings

```agda
subset-Commutative-Semiring :
  (l : Level) {l1 : Level} (A : Commutative-Semiring l1) → UU (lsuc l ⊔ l1)
subset-Commutative-Semiring l A =
  subset-Semiring l (semiring-Commutative-Semiring A)

is-set-subset-Commutative-Semiring :
  (l : Level) {l1 : Level} (A : Commutative-Semiring l1) →
  is-set (subset-Commutative-Semiring l A)
is-set-subset-Commutative-Semiring l A =
  is-set-subset-Semiring l (semiring-Commutative-Semiring A)

module _
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 A)
  where

  type-subset-Commutative-Semiring : UU (l1 ⊔ l2)
  type-subset-Commutative-Semiring =
    type-subset-Semiring (semiring-Commutative-Semiring A) S

  inclusion-subset-Commutative-Semiring :
    type-subset-Commutative-Semiring → type-Commutative-Semiring A
  inclusion-subset-Commutative-Semiring =
    inclusion-subset-Semiring (semiring-Commutative-Semiring A) S

  ap-inclusion-subset-Commutative-Semiring :
    (x y : type-subset-Commutative-Semiring) →
    x ＝ y →
    ( inclusion-subset-Commutative-Semiring x ＝
      inclusion-subset-Commutative-Semiring y)
  ap-inclusion-subset-Commutative-Semiring =
    ap-inclusion-subset-Semiring (semiring-Commutative-Semiring A) S

  is-in-subset-Commutative-Semiring : type-Commutative-Semiring A → UU l2
  is-in-subset-Commutative-Semiring = is-in-subtype S

  is-prop-is-in-subset-Commutative-Semiring :
    (x : type-Commutative-Semiring A) →
    is-prop (is-in-subset-Commutative-Semiring x)
  is-prop-is-in-subset-Commutative-Semiring =
    is-prop-is-in-subtype S

  is-closed-under-eq-subset-Commutative-Semiring :
    {x y : type-Commutative-Semiring A} →
    is-in-subset-Commutative-Semiring x → x ＝ y →
    is-in-subset-Commutative-Semiring y
  is-closed-under-eq-subset-Commutative-Semiring =
    is-closed-under-eq-subtype S

  is-in-subset-inclusion-subset-Commutative-Semiring :
    (x : type-subset-Commutative-Semiring) →
    is-in-subset-Commutative-Semiring (inclusion-subset-Commutative-Semiring x)
  is-in-subset-inclusion-subset-Commutative-Semiring =
    is-in-subtype-inclusion-subtype S
```

### The condition that a subset contains zero

This condition asserts that `0 ∈ S`.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 A)
  where

  contains-zero-prop-subset-Commutative-Semiring :
    Prop l2
  contains-zero-prop-subset-Commutative-Semiring =
    contains-zero-prop-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)

  contains-zero-subset-Commutative-Semiring :
    UU l2
  contains-zero-subset-Commutative-Semiring =
    contains-zero-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)

  is-prop-contains-zero-subset-Commutative-Semiring :
    is-prop contains-zero-subset-Commutative-Semiring
  is-prop-contains-zero-subset-Commutative-Semiring =
    is-prop-contains-zero-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
```

### The condition that a subset contains one

This condition asserts that `1 ∈ S`.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 A)
  where

  contains-one-prop-subset-Commutative-Semiring :
    Prop l2
  contains-one-prop-subset-Commutative-Semiring =
    contains-one-prop-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)

  contains-one-subset-Commutative-Semiring :
    UU l2
  contains-one-subset-Commutative-Semiring =
    contains-one-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)

  is-prop-contains-one-subset-Commutative-Semiring :
    is-prop contains-one-subset-Commutative-Semiring
  is-prop-contains-one-subset-Commutative-Semiring =
    is-prop-contains-one-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
```

### The condition that a subset is closed under addition

This condition asserts that for any `x y ∈ S` we have `x + y ∈ S`.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 A)
  where

  is-closed-under-addition-prop-subset-Commutative-Semiring :
    Prop (l1 ⊔ l2)
  is-closed-under-addition-prop-subset-Commutative-Semiring =
    is-closed-under-addition-prop-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)

  is-closed-under-addition-subset-Commutative-Semiring :
    UU (l1 ⊔ l2)
  is-closed-under-addition-subset-Commutative-Semiring =
    is-closed-under-addition-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)

  is-prop-is-closed-under-addition-subset-Commutative-Semiring :
    is-prop is-closed-under-addition-subset-Commutative-Semiring
  is-prop-is-closed-under-addition-subset-Commutative-Semiring =
    is-prop-is-closed-under-addition-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
```

### The condition that a subset is an additive submonoid

This condition asserts that the subset contains `0` and is closed under addition.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 A)
  where

  is-additive-submonoid-prop-subset-Commutative-Semiring :
    Prop (l1 ⊔ l2)
  is-additive-submonoid-prop-subset-Commutative-Semiring =
    is-additive-submonoid-prop-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
      
  is-additive-submonoid-subset-Commutative-Semiring :
    UU (l1 ⊔ l2)
  is-additive-submonoid-subset-Commutative-Semiring =
    is-additive-submonoid-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)

  is-prop-is-additive-submonoid-subset-Commutative-Semiring :
    is-prop is-additive-submonoid-subset-Commutative-Semiring
  is-prop-is-additive-submonoid-subset-Commutative-Semiring =
   is-prop-is-additive-submonoid-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
```

### The condition that a subset is closed under multiplication

This condition asserts that for any `x y ∈ S` we have `xy ∈ S`.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 A)
  where

  is-closed-under-multiplication-prop-subset-Commutative-Semiring :
    Prop (l1 ⊔ l2)
  is-closed-under-multiplication-prop-subset-Commutative-Semiring =
    is-closed-under-multiplication-prop-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
      
  is-closed-under-multiplication-subset-Commutative-Semiring :
    UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Commutative-Semiring =
    is-closed-under-multiplication-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)

  is-prop-is-closed-under-multiplication-subset-Commutative-Semiring :
    is-prop is-closed-under-multiplication-subset-Commutative-Semiring
  is-prop-is-closed-under-multiplication-subset-Commutative-Semiring =
    is-prop-is-closed-under-multiplication-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
```

### The condition that a subset is closed under multiplication from the left by an arbitrary element

This condition asserts that for any `r x : R`, if `x ∈ S` then `rx ∈ S`.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 A)
  where

  is-closed-under-left-multiplication-prop-subset-Commutative-Semiring :
    Prop (l1 ⊔ l2)
  is-closed-under-left-multiplication-prop-subset-Commutative-Semiring =
    is-closed-under-left-multiplication-prop-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
      
  is-closed-under-left-multiplication-subset-Commutative-Semiring :
    UU (l1 ⊔ l2)
  is-closed-under-left-multiplication-subset-Commutative-Semiring =
    is-closed-under-left-multiplication-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)

  is-prop-is-closed-under-left-multiplication-subset-Commutative-Semiring :
    is-prop is-closed-under-left-multiplication-subset-Commutative-Semiring
  is-prop-is-closed-under-left-multiplication-subset-Commutative-Semiring =
    is-prop-is-closed-under-left-multiplication-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
```

### The condition that a subset is closed under multiplication from the right by an arbitrary element

This condition asserts that for any `x r : R`, if `x ∈ S` then `xr ∈ S`.

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 A)
  where

  is-closed-under-right-multiplication-prop-subset-Commutative-Semiring :
    Prop (l1 ⊔ l2)
  is-closed-under-right-multiplication-prop-subset-Commutative-Semiring =
    is-closed-under-right-multiplication-prop-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
      
  is-closed-under-right-multiplication-subset-Commutative-Semiring :
    UU (l1 ⊔ l2)
  is-closed-under-right-multiplication-subset-Commutative-Semiring =
    is-closed-under-right-multiplication-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)

  is-prop-is-closed-under-right-multiplication-subset-Commutative-Semiring :
    is-prop is-closed-under-right-multiplication-subset-Commutative-Semiring
  is-prop-is-closed-under-right-multiplication-subset-Commutative-Semiring =
    is-prop-is-closed-under-right-multiplication-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
```

### The condition that a subset is closed under two-sided multiplication by arbitrary elements

This condition asserts that for any `r x u : R`, if `x ∈ S` then `(rx)u ∈ S`.

The operation `r x u ↦ (rx)u` is the standard form of two-sided multiplication in `R`, which gives the semiring `R` the structure of an (additive) [monoid with `R`-action](commutative-algebra.monoids-with-commutative-semiring-action.md).

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 A)
  where

  is-closed-under-two-sided-multiplication-prop-subset-Commutative-Semiring :
    Prop (l1 ⊔ l2)
  is-closed-under-two-sided-multiplication-prop-subset-Commutative-Semiring =
    is-closed-under-two-sided-multiplication-prop-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
      
  is-closed-under-two-sided-multiplication-subset-Commutative-Semiring :
    UU (l1 ⊔ l2)
  is-closed-under-two-sided-multiplication-subset-Commutative-Semiring =
    is-closed-under-two-sided-multiplication-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)

  is-prop-is-closed-under-two-sided-multiplication-subset-Commutative-Semiring :
    is-prop is-closed-under-two-sided-multiplication-subset-Commutative-Semiring
  is-prop-is-closed-under-two-sided-multiplication-subset-Commutative-Semiring =
    is-prop-is-closed-under-two-sided-multiplication-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
```

### The condition that a subset of a commutative semiring is an multiplicative submonoid

This condition asserts that the subset contains `1` and is closed under multiplication.

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Semiring l1) (S : subset-Commutative-Semiring l2 R)
  where

  is-multiplicative-submonoid-subset-Commutative-Semiring : UU (l1 ⊔ l2)
  is-multiplicative-submonoid-subset-Commutative-Semiring =
    is-multiplicative-submonoid-subset-Semiring
      ( semiring-Commutative-Semiring R)
      ( S)

  is-prop-is-multiplicative-submonoid-subset-Commutative-Semiring :
    is-prop is-multiplicative-submonoid-subset-Commutative-Semiring
  is-prop-is-multiplicative-submonoid-subset-Commutative-Semiring =
    is-prop-is-multiplicative-submonoid-subset-Semiring
      ( semiring-Commutative-Semiring R)
      ( S)

  is-multiplicative-submonoid-prop-subset-Commutative-Semiring : Prop (l1 ⊔ l2)
  is-multiplicative-submonoid-prop-subset-Commutative-Semiring =
    is-multiplicative-submonoid-prop-subset-Semiring
      ( semiring-Commutative-Semiring R)
      ( S)
```
