# Subsets of rings

```agda
module ring-theory.subsets-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.propositional-extensionality
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.rings
```

</details>

## Idea

A subset of a ring is a subtype of the underlying type of a ring

## Definition

### Subsets of rings

```agda
subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU ((lsuc l) ⊔ l1)
subset-Ring l R = subtype l (type-Ring R)

is-set-subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → is-set (subset-Ring l R)
is-set-subset-Ring l R =
  is-set-function-type is-set-type-Prop

module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  type-subset-Ring : UU (l1 ⊔ l2)
  type-subset-Ring = type-subtype S

  inclusion-subset-Ring : type-subset-Ring → type-Ring R
  inclusion-subset-Ring = pr1
```

### The condition that a subset contains zero

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  contains-zero-subset-Ring : UU l2
  contains-zero-subset-Ring = is-in-subtype S (zero-Ring R)
```

### The condition that a subset contains one

```agda
  contains-one-subset-Ring : UU l2
  contains-one-subset-Ring = is-in-subtype S (one-Ring R)
```

### The condition that a subset is closed under addition

```agda
  is-closed-under-addition-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-addition-subset-Ring =
    (x y : type-Ring R) →
    is-in-subtype S x → is-in-subtype S y →
    is-in-subtype S (add-Ring R x y)
```

### The condition that a subset is closed under negatives

```agda
  is-closed-under-negatives-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-negatives-subset-Ring =
    (x : type-Ring R) → is-in-subtype S x → is-in-subtype S (neg-Ring R x)
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Ring =
    (x y : type-Ring R) → is-in-subtype S x → is-in-subtype S y →
    is-in-subtype S (mul-Ring R x y)
```

### The condition that a subset is closed under multiplication from the left by an arbitrary element

```agda
  is-closed-under-left-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-left-multiplication-subset-Ring =
    (x y : type-Ring R) → is-in-subtype S y →
    is-in-subtype S (mul-Ring R x y)
```

### The condition that a subset is closed-under-multiplication from the right by an arbitrary element

```agda
  is-closed-under-right-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-right-multiplication-subset-Ring =
    (x y : type-Ring R) → is-in-subtype S x →
    is-in-subtype S (mul-Ring R x y)
```
