# Subsets of algebras over commutative rings

```agda
module commutative-algebra.subsets-algebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.algebras-commutative-rings
open import commutative-algebra.commutative-rings

open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.subsets-left-modules-commutative-rings
```

</details>

## Idea

A
{{#concept "subset" Disambiguation="of an algebra over a commutative ring" Agda=subset-algebra-Commutative-Ring}}
of an [algebra](commutative-algebra.algebras-commutative-rings.md) `A` over a
[commutative ring](commutative-algebra.commutative-rings.md) `R` is a
[subset](foundation.subtypes.md) of the underlying type of `A`.

## Definition

```agda
module _
  {l1 l2 : Level} (l3 : Level)
  (R : Commutative-Ring l1)
  (A : algebra-Commutative-Ring l2 R)
  where

  subset-algebra-Commutative-Ring : UU (l2 ⊔ lsuc l3)
  subset-algebra-Commutative-Ring =
    subtype l3 (type-algebra-Commutative-Ring R A)
```

## Properties

### The condition that a subset contains zero

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : algebra-Commutative-Ring l2 R)
  where

  contains-zero-prop-subset-algebra-Commutative-Ring :
    subset-algebra-Commutative-Ring l3 R A → Prop l3
  contains-zero-prop-subset-algebra-Commutative-Ring =
    contains-zero-prop-subset-left-module-Commutative-Ring
      ( R)
      ( left-module-algebra-Commutative-Ring R A)

  contains-zero-subset-algebra-Commutative-Ring :
    subset-algebra-Commutative-Ring l3 R A → UU l3
  contains-zero-subset-algebra-Commutative-Ring S =
    type-Prop (contains-zero-prop-subset-algebra-Commutative-Ring S)
```

### The condition that a subset is closed under addition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : algebra-Commutative-Ring l2 R)
  where

  is-closed-under-addition-prop-subset-algebra-Commutative-Ring :
    subset-algebra-Commutative-Ring l3 R A → Prop (l2 ⊔ l3)
  is-closed-under-addition-prop-subset-algebra-Commutative-Ring =
    is-closed-under-addition-prop-subset-left-module-Commutative-Ring
      ( R)
      ( left-module-algebra-Commutative-Ring R A)

  is-closed-under-addition-subset-algebra-Commutative-Ring :
    subset-algebra-Commutative-Ring l3 R A → UU (l2 ⊔ l3)
  is-closed-under-addition-subset-algebra-Commutative-Ring S =
    type-Prop (is-closed-under-addition-prop-subset-algebra-Commutative-Ring S)
```

### The condition that a subset is closed under scalar multiplication

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : algebra-Commutative-Ring l2 R)
  where

  is-closed-under-scalar-multiplication-prop-subset-algebra-Commutative-Ring :
    subset-algebra-Commutative-Ring l3 R A → Prop (l1 ⊔ l2 ⊔ l3)
  is-closed-under-scalar-multiplication-prop-subset-algebra-Commutative-Ring =
    is-closed-under-scalar-multiplication-prop-subset-left-module-Commutative-Ring
      ( R)
      ( left-module-algebra-Commutative-Ring R A)

  is-closed-under-scalar-multiplication-subset-algebra-Commutative-Ring :
    subset-algebra-Commutative-Ring l3 R A → UU (l1 ⊔ l2 ⊔ l3)
  is-closed-under-scalar-multiplication-subset-algebra-Commutative-Ring S =
    type-Prop
      ( is-closed-under-scalar-multiplication-prop-subset-algebra-Commutative-Ring
        ( S))
```

### The condition that a subset is closed under multiplication

```agda
module _
  {l1 l2 l3 : Level}
  (R : Commutative-Ring l1)
  (A : algebra-Commutative-Ring l2 R)
  where

  is-closed-under-multiplication-prop-subset-algebra-Commutative-Ring :
    subset-algebra-Commutative-Ring l3 R A → Prop (l2 ⊔ l3)
  is-closed-under-multiplication-prop-subset-algebra-Commutative-Ring S =
    Π-Prop
      ( type-algebra-Commutative-Ring R A)
      ( λ x →
        Π-Prop
          ( type-algebra-Commutative-Ring R A)
          ( λ y →
            hom-Prop
              ( S x)
              ( hom-Prop
                ( S y)
                ( S (mul-algebra-Commutative-Ring R A x y)))))

  is-closed-under-multiplication-subset-algebra-Commutative-Ring :
    subset-algebra-Commutative-Ring l3 R A → UU (l2 ⊔ l3)
  is-closed-under-multiplication-subset-algebra-Commutative-Ring S =
    type-Prop
      ( is-closed-under-multiplication-prop-subset-algebra-Commutative-Ring S)
```
