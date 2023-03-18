# Subsets of semirings

```agda
module ring-theory.subsets-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositional-extensionality
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.semirings
```

</details>

## Idea

A subset of a semiring is a subtype of the underlying type of a semiring

## Definition

### Subsets of semirings

```agda
subset-Semiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → UU ((lsuc l) ⊔ l1)
subset-Semiring l R = subtype l (type-Semiring R)

is-set-subset-Semiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → is-set (subset-Semiring l R)
is-set-subset-Semiring l R =
  is-set-function-type is-set-type-Prop

module _
  {l1 l2 : Level} (R : Semiring l1) (S : subset-Semiring l2 R)
  where

  type-subset-Semiring : UU (l1 ⊔ l2)
  type-subset-Semiring = type-subtype S

  inclusion-subset-Semiring : type-subset-Semiring → type-Semiring R
  inclusion-subset-Semiring = pr1
```

### The condition that a subset contains zero

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (S : subset-Semiring l2 R)
  where

  contains-zero-subset-Semiring : UU l2
  contains-zero-subset-Semiring = is-in-subtype S (zero-Semiring R)
```

### The condition that a subset contains one

```agda
  contains-one-subset-Semiring : UU l2
  contains-one-subset-Semiring = is-in-subtype S (one-Semiring R)
```

### The condition that a subset is closed under addition

```agda
  is-closed-under-addition-subset-Semiring : UU (l1 ⊔ l2)
  is-closed-under-addition-subset-Semiring =
    (x y : type-Semiring R) →
    is-in-subtype S x → is-in-subtype S y →
    is-in-subtype S (add-Semiring R x y)
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-subset-Semiring : UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Semiring =
    (x y : type-Semiring R) → is-in-subtype S x → is-in-subtype S y →
    is-in-subtype S (mul-Semiring R x y)
```

### The condition that a subset is closed under multiplication from the left by an arbitrary element

```agda
  is-closed-under-left-multiplication-subset-Semiring : UU (l1 ⊔ l2)
  is-closed-under-left-multiplication-subset-Semiring =
    (x y : type-Semiring R) → is-in-subtype S y →
    is-in-subtype S (mul-Semiring R x y)
```

### The condition that a subset is closed-under-multiplication from the right by an arbitrary element

```agda
  is-closed-under-right-multiplication-subset-Semiring : UU (l1 ⊔ l2)
  is-closed-under-right-multiplication-subset-Semiring =
    (x y : type-Semiring R) → is-in-subtype S x →
    is-in-subtype S (mul-Semiring R x y)
```
