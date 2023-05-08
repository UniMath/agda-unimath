# Subsets of commutative semirings

```agda
module commutative-algebra.subsets-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.subsets-semirings
```

</details>

## Idea

A **subset** of a commutative semiring is a subtype of its underlying type.

## Definition

### Subsets of commutative semirings

```agda
subset-Commutative-Semiring :
  (l : Level) {l1 : Level} (A : Commutative-Semiring l1) → UU ((lsuc l) ⊔ l1)
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

```agda
module _
  {l1 l2 : Level} (A : Commutative-Semiring l1)
  (S : subset-Commutative-Semiring l2 A)
  where

  contains-zero-subset-Commutative-Semiring : UU l2
  contains-zero-subset-Commutative-Semiring =
    contains-zero-subset-Semiring (semiring-Commutative-Semiring A) S
```

### The condition that a subset contains one

```agda
  contains-one-subset-Commutative-Semiring : UU l2
  contains-one-subset-Commutative-Semiring =
    contains-one-subset-Semiring (semiring-Commutative-Semiring A) S
```

### The condition that a subset is closed under addition

```agda
  is-closed-under-addition-subset-Commutative-Semiring : UU (l1 ⊔ l2)
  is-closed-under-addition-subset-Commutative-Semiring =
    is-closed-under-addition-subset-Semiring (semiring-Commutative-Semiring A) S
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-subset-Commutative-Semiring : UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Commutative-Semiring =
    is-closed-under-multiplication-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
```

### The condition that a subset is closed under multiplication from the left by an arbitrary element

```agda
  is-closed-under-left-multiplication-subset-Commutative-Semiring : UU (l1 ⊔ l2)
  is-closed-under-left-multiplication-subset-Commutative-Semiring =
    is-closed-under-left-multiplication-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
```

### The condition that a subset is closed-under-multiplication from the right by an arbitrary element

```agda
  is-closed-under-right-multiplication-subset-Commutative-Semiring :
    UU (l1 ⊔ l2)
  is-closed-under-right-multiplication-subset-Commutative-Semiring =
    is-closed-under-right-multiplication-subset-Semiring
      ( semiring-Commutative-Semiring A)
      ( S)
```
