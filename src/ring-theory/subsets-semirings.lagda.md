# Subsets of semirings

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module ring-theory.subsets-semirings
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-products-propositions funext
open import foundation.identity-types funext
open import foundation.propositional-extensionality funext univalence truncations
open import foundation.propositions funext univalence
open import foundation.sets funext univalence
open import foundation.subtypes funext univalence truncations
open import foundation.universe-levels

open import ring-theory.semirings funext univalence truncations
```

</details>

## Idea

A subset of a semiring is a subtype of the underlying type of a semiring

## Definition

### Subsets of semirings

```agda
subset-Semiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → UU (lsuc l ⊔ l1)
subset-Semiring l R = subtype l (type-Semiring R)

is-set-subset-Semiring :
  (l : Level) {l1 : Level} (R : Semiring l1) → is-set (subset-Semiring l R)
is-set-subset-Semiring l R =
  is-set-function-type is-set-type-Prop

module _
  {l1 l2 : Level} (R : Semiring l1) (S : subset-Semiring l2 R)
  where

  is-in-subset-Semiring : type-Semiring R → UU l2
  is-in-subset-Semiring = is-in-subtype S

  is-prop-is-in-subset-Semiring :
    (x : type-Semiring R) → is-prop (is-in-subset-Semiring x)
  is-prop-is-in-subset-Semiring = is-prop-is-in-subtype S

  type-subset-Semiring : UU (l1 ⊔ l2)
  type-subset-Semiring = type-subtype S

  inclusion-subset-Semiring : type-subset-Semiring → type-Semiring R
  inclusion-subset-Semiring = inclusion-subtype S

  ap-inclusion-subset-Semiring :
    (x y : type-subset-Semiring) →
    x ＝ y → (inclusion-subset-Semiring x ＝ inclusion-subset-Semiring y)
  ap-inclusion-subset-Semiring = ap-inclusion-subtype S

  is-in-subset-inclusion-subset-Semiring :
    (x : type-subset-Semiring) →
    is-in-subset-Semiring (inclusion-subset-Semiring x)
  is-in-subset-inclusion-subset-Semiring =
    is-in-subtype-inclusion-subtype S

  is-closed-under-eq-subset-Semiring :
    {x y : type-Semiring R} →
    is-in-subset-Semiring x → (x ＝ y) → is-in-subset-Semiring y
  is-closed-under-eq-subset-Semiring =
    is-closed-under-eq-subtype S

  is-closed-under-eq-subset-Semiring' :
    {x y : type-Semiring R} →
    is-in-subset-Semiring y → (x ＝ y) → is-in-subset-Semiring x
  is-closed-under-eq-subset-Semiring' =
    is-closed-under-eq-subtype' S
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
