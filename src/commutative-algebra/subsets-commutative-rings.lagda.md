# Subsets of commutative rings

```agda
module commutative-algebra.subsets-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.identity-types
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.subgroups-abelian-groups

open import ring-theory.subsets-rings
```

</details>

## Idea

A **subset** of a commutative ring is a subtype of its underlying type.

## Definition

### Subsets of rings

```agda
subset-Commutative-Ring :
  (l : Level) {l1 : Level} (A : Commutative-Ring l1) → UU ((lsuc l) ⊔ l1)
subset-Commutative-Ring l A = subtype l (type-Commutative-Ring A)

is-set-subset-Commutative-Ring :
  (l : Level) {l1 : Level} (A : Commutative-Ring l1) →
  is-set (subset-Commutative-Ring l A)
is-set-subset-Commutative-Ring l A =
  is-set-function-type is-set-type-Prop

module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (S : subset-Commutative-Ring l2 A)
  where

  is-in-subset-Commutative-Ring : type-Commutative-Ring A → UU l2
  is-in-subset-Commutative-Ring = is-in-subtype S

  is-prop-is-in-subset-Commutative-Ring :
    (x : type-Commutative-Ring A) → is-prop (is-in-subset-Commutative-Ring x)
  is-prop-is-in-subset-Commutative-Ring = is-prop-is-in-subtype S

  type-subset-Commutative-Ring : UU (l1 ⊔ l2)
  type-subset-Commutative-Ring = type-subtype S

  inclusion-subset-Commutative-Ring :
    type-subset-Commutative-Ring → type-Commutative-Ring A
  inclusion-subset-Commutative-Ring = inclusion-subtype S

  ap-inclusion-subset-Commutative-Ring :
    (x y : type-subset-Commutative-Ring) → x ＝ y →
    inclusion-subset-Commutative-Ring x ＝ inclusion-subset-Commutative-Ring y
  ap-inclusion-subset-Commutative-Ring = ap-inclusion-subtype S

  is-in-subset-inclusion-subset-Commutative-Ring :
    (x : type-subset-Commutative-Ring) →
    is-in-subset-Commutative-Ring (inclusion-subset-Commutative-Ring x)
  is-in-subset-inclusion-subset-Commutative-Ring =
    is-in-subtype-inclusion-subtype S

  is-closed-under-eq-subset-Commutative-Ring :
    {x y : type-Commutative-Ring A} →
    is-in-subset-Commutative-Ring x → (x ＝ y) → is-in-subset-Commutative-Ring y
  is-closed-under-eq-subset-Commutative-Ring =
    is-closed-under-eq-subtype S

  is-closed-under-eq-subset-Commutative-Ring' :
    {x y : type-Commutative-Ring A} →
    is-in-subset-Commutative-Ring y → (x ＝ y) → is-in-subset-Commutative-Ring x
  is-closed-under-eq-subset-Commutative-Ring' =
    is-closed-under-eq-subtype' S
```

### The condition that a subset contains zero

```agda
module _
  {l1 l2 : Level} (A : Commutative-Ring l1) (S : subset-Commutative-Ring l2 A)
  where

  contains-zero-subset-Commutative-Ring : UU l2
  contains-zero-subset-Commutative-Ring =
    is-in-subset-Commutative-Ring A S (zero-Commutative-Ring A)
```

### The condition that a subset contains one

```agda
  contains-one-subset-Commutative-Ring : UU l2
  contains-one-subset-Commutative-Ring =
    is-in-subset-Commutative-Ring A S (one-Commutative-Ring A)
```

### The condition that a subset is closed under addition

```agda
  is-closed-under-addition-subset-Commutative-Ring : UU (l1 ⊔ l2)
  is-closed-under-addition-subset-Commutative-Ring =
    is-closed-under-addition-subset-Ring (ring-Commutative-Ring A) S
```

### The condition that a subset is closed under negatives

```agda
  is-closed-under-negatives-subset-Commutative-Ring : UU (l1 ⊔ l2)
  is-closed-under-negatives-subset-Commutative-Ring =
    is-closed-under-negatives-subset-Ring (ring-Commutative-Ring A) S
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-subset-Commutative-Ring : UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Commutative-Ring =
    is-closed-under-multiplication-subset-Ring (ring-Commutative-Ring A) S
```

### The condition that a subset is closed under multiplication from the left by an arbitrary element

```agda
  is-closed-under-left-multiplication-subset-Commutative-Ring : UU (l1 ⊔ l2)
  is-closed-under-left-multiplication-subset-Commutative-Ring =
    is-closed-under-left-multiplication-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)
```

### The condition that a subset is closed under multiplication from the right by an arbitrary element

```agda
  is-closed-under-right-multiplication-subset-Commutative-Ring : UU (l1 ⊔ l2)
  is-closed-under-right-multiplication-subset-Commutative-Ring =
    is-closed-under-right-multiplication-subset-Ring
      ( ring-Commutative-Ring A)
      ( S)
```

### The condition that a subset is an additive subgroup

```agda
module _
  {l1 : Level} (A : Commutative-Ring l1)
  where

  is-additive-subgroup-subset-Commutative-Ring :
    {l2 : Level} → subset-Commutative-Ring l2 A → UU (l1 ⊔ l2)
  is-additive-subgroup-subset-Commutative-Ring =
    is-subgroup-Ab (ab-Commutative-Ring A)
```
