# Full ideals of commutative semirings

```agda
module commutative-algebra.full-ideals-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.ideals-commutative-semirings
open import commutative-algebra.poset-of-ideals-commutative-semirings
open import commutative-algebra.commutative-semirings
open import commutative-algebra.subsets-commutative-semirings

open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions
open import foundation.full-subtypes
open import foundation.propositions
open import foundation.raising-universe-levels
open import foundation.raising-universe-levels-unit-type
open import foundation.subtypes
open import foundation.unit-type
open import foundation.universe-levels

open import order-theory.top-elements-large-posets

open import ring-theory.full-ideals-semirings
```

</details>

## Idea

A
{{#concept "full ideal" Disambiguation="of a commutative semiring" Agda=is-full-ideal-Commutative-Semiring Agda=full-ideal-Commutative-Semiring}}
of a [commutative semiring](commutative-algebra.commutative-semirings.md) `A` is an [ideal](commutative-algebra.ideals-commutative-semirings.md)
that contains every element of `R`.

## Definitions

### The predicate of being a full ideal

```agda
module _
  {l1 l2 : Level}
  (A : Commutative-Semiring l1) (I : ideal-Commutative-Semiring l2 A)
  where

  is-full-prop-ideal-Commutative-Semiring :
    Prop (l1 ⊔ l2)
  is-full-prop-ideal-Commutative-Semiring =
    is-full-prop-left-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-full-ideal-Commutative-Semiring :
    UU (l1 ⊔ l2)
  is-full-ideal-Commutative-Semiring =
    is-full-left-ideal-Semiring (semiring-Commutative-Semiring A) I

  is-prop-is-full-ideal-Commutative-Semiring :
    is-prop is-full-ideal-Commutative-Semiring
  is-prop-is-full-ideal-Commutative-Semiring =
    is-prop-is-full-left-ideal-Semiring (semiring-Commutative-Semiring A) I
```

### The (standard) full ideal

```agda
module _
  {l1 : Level} (A : Commutative-Semiring l1)
  where

  subset-full-ideal-Commutative-Semiring :
    subset-Commutative-Semiring lzero A
  subset-full-ideal-Commutative-Semiring =
    subset-full-ideal-Semiring (semiring-Commutative-Semiring A)

  is-in-full-ideal-Commutative-Semiring :
    type-Commutative-Semiring A → UU lzero
  is-in-full-ideal-Commutative-Semiring =
    is-in-full-ideal-Semiring (semiring-Commutative-Semiring A)

  contains-zero-full-ideal-Commutative-Semiring :
    contains-zero-subset-Commutative-Semiring A
      subset-full-ideal-Commutative-Semiring
  contains-zero-full-ideal-Commutative-Semiring =
    contains-zero-full-ideal-Semiring (semiring-Commutative-Semiring A)

  is-closed-under-addition-full-ideal-Commutative-Semiring :
    is-closed-under-addition-subset-Commutative-Semiring A
      subset-full-ideal-Commutative-Semiring
  is-closed-under-addition-full-ideal-Commutative-Semiring {x} {y} =
    is-closed-under-addition-full-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      { x}
      { y}

  is-additive-submonoid-full-ideal-Commutative-Semiring :
    is-additive-submonoid-subset-Commutative-Semiring A
      subset-full-ideal-Commutative-Semiring
  is-additive-submonoid-full-ideal-Commutative-Semiring =
    is-additive-submonoid-full-ideal-Semiring (semiring-Commutative-Semiring A)

  is-closed-under-left-multiplication-full-ideal-Commutative-Semiring :
    is-closed-under-left-multiplication-subset-Commutative-Semiring A
      subset-full-ideal-Commutative-Semiring
  is-closed-under-left-multiplication-full-ideal-Commutative-Semiring {x} {y} =
    is-closed-under-left-multiplication-full-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      { x}
      { y}

  is-closed-under-right-multiplication-full-ideal-Commutative-Semiring :
    is-closed-under-right-multiplication-subset-Commutative-Semiring A
      subset-full-ideal-Commutative-Semiring
  is-closed-under-right-multiplication-full-ideal-Commutative-Semiring {x} {y} =
    is-closed-under-right-multiplication-full-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      { x}
      { y}

  is-closed-under-two-sided-multiplication-full-ideal-Commutative-Semiring :
    is-closed-under-two-sided-multiplication-subset-Commutative-Semiring A
      subset-full-ideal-Commutative-Semiring
  is-closed-under-two-sided-multiplication-full-ideal-Commutative-Semiring
    {x} {y} {z} =
    is-closed-under-two-sided-multiplication-full-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      { x}
      { y}
      { z}

  is-ideal-full-ideal-Commutative-Semiring :
    is-ideal-subset-Commutative-Semiring A
      subset-full-ideal-Commutative-Semiring
  is-ideal-full-ideal-Commutative-Semiring =
    is-left-ideal-full-ideal-Semiring (semiring-Commutative-Semiring A)

  full-ideal-Commutative-Semiring :
    ideal-Commutative-Semiring lzero A
  full-ideal-Commutative-Semiring =
    full-left-ideal-Semiring (semiring-Commutative-Semiring A)

  is-full-full-ideal-Commutative-Semiring :
    is-full-ideal-Commutative-Semiring A full-ideal-Commutative-Semiring
  is-full-full-ideal-Commutative-Semiring =
    is-full-full-ideal-Semiring (semiring-Commutative-Semiring A)
```

## Properties

### Any ideal is full if and only if it contains `1`

```agda
module _
  {l1 l2 : Level}
  (A : Commutative-Semiring l1) (I : ideal-Commutative-Semiring l2 A)
  where

  is-full-contains-one-ideal-Commutative-Semiring :
    is-in-ideal-Commutative-Semiring A I (one-Commutative-Semiring A) →
    is-full-ideal-Commutative-Semiring A I
  is-full-contains-one-ideal-Commutative-Semiring =
    is-full-contains-one-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( two-sided-ideal-ideal-Commutative-Semiring A I)

  contains-one-is-full-ideal-Commutative-Semiring :
    is-full-ideal-Commutative-Semiring A I →
    is-in-ideal-Commutative-Semiring A I (one-Commutative-Semiring A)
  contains-one-is-full-ideal-Commutative-Semiring =
    contains-one-is-full-ideal-Semiring
      ( semiring-Commutative-Semiring A)
      ( two-sided-ideal-ideal-Commutative-Semiring A I)
```

### Any ideal is full if and only if it is a top element in the large poset of ideals

```agda
module _
  {l1 l2 : Level}
  (A : Commutative-Semiring l1) (I : ideal-Commutative-Semiring l2 A)
  where

  is-full-is-top-element-ideal-Commutative-Semiring :
    is-top-element-Large-Poset (ideal-Commutative-Semiring-Large-Poset A) I →
    is-full-ideal-Commutative-Semiring A I
  is-full-is-top-element-ideal-Commutative-Semiring H x =
    H ( full-ideal-Commutative-Semiring A)
      ( x)
      ( is-full-full-ideal-Commutative-Semiring A x)

  is-top-element-is-full-ideal-Commutative-Semiring :
    is-full-ideal-Commutative-Semiring A I →
    is-top-element-Large-Poset (ideal-Commutative-Semiring-Large-Poset A) I
  is-top-element-is-full-ideal-Commutative-Semiring H I x K =
    H x

module _
  {l1 : Level} (A : Commutative-Semiring l1)
  where

  is-top-element-full-ideal-Commutative-Semiring :
    is-top-element-Large-Poset
      ( ideal-Commutative-Semiring-Large-Poset A)
      ( full-ideal-Commutative-Semiring A)
  is-top-element-full-ideal-Commutative-Semiring =
    is-top-element-is-full-ideal-Commutative-Semiring A
      ( full-ideal-Commutative-Semiring A)
      ( is-full-full-ideal-Commutative-Semiring A)

  has-top-element-ideal-Commutative-Semiring :
    has-top-element-Large-Poset (ideal-Commutative-Semiring-Large-Poset A)
  top-has-top-element-Large-Poset
    has-top-element-ideal-Commutative-Semiring =
    full-ideal-Commutative-Semiring A
  is-top-element-top-has-top-element-Large-Poset
    has-top-element-ideal-Commutative-Semiring =
    is-top-element-full-ideal-Commutative-Semiring
```
