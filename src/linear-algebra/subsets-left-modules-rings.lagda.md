# Subsets of left modules over rings

```agda
module linear-algebra.subsets-left-modules-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.conjunction
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels

open import linear-algebra.left-modules-rings

open import ring-theory.rings
```

</details>

## Idea

A subset of a [left module](./left-modules-rings.lagda.md) `M` over a
[ring](../ring-theory/rings.lagda.md) `R` is a
[subset](../foundation/subtypes.lagda.md) of the underlying type of `M`.

## Definitions

### Subsets of left modules over rings

```agda
subset-left-module-Ring :
  {l1 l2 : Level}
  (l : Level) (R : Ring l1) (M : left-module-Ring l2 R) → UU (l2 ⊔ lsuc l)
subset-left-module-Ring l R M = subtype l (type-left-module-Ring R M)
```

### The condition that a subset is closed under addition

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1) (M : left-module-Ring l2 R) (S : subset-left-module-Ring l3 R M)
  where

  is-closed-under-addition-prop-subset-left-module-Ring : Prop (l2 ⊔ l3)
  is-closed-under-addition-prop-subset-left-module-Ring =
    Π-Prop
      ( type-left-module-Ring R M)
      ( λ x →
        Π-Prop
          ( type-left-module-Ring R M)
          ( λ y →
            hom-Prop
              ( S x)
              ( hom-Prop
                  ( S y)
                  ( S (add-left-module-Ring R M x y)))))

  is-closed-under-addition-subset-left-module-Ring : UU (l2 ⊔ l3)
  is-closed-under-addition-subset-left-module-Ring =
    type-Prop is-closed-under-addition-prop-subset-left-module-Ring
```

### The condition that a subset is closed under multiplication by a scalar

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1) (M : left-module-Ring l2 R) (S : subset-left-module-Ring l3 R M)
  where

  is-closed-under-multiplication-by-scalar-prop-subset-left-module-Ring :
    Prop (l1 ⊔ l2 ⊔ l3)
  is-closed-under-multiplication-by-scalar-prop-subset-left-module-Ring =
    Π-Prop
      ( type-Ring R)
      ( λ r →
        Π-Prop
          ( type-left-module-Ring R M)
          ( λ x →
            hom-Prop
              ( S x)
              ( S (mul-left-module-Ring R M r x))))

  is-closed-under-multiplication-by-scalar-subset-left-module-Ring :
    UU (l1 ⊔ l2 ⊔ l3)
  is-closed-under-multiplication-by-scalar-subset-left-module-Ring =
    type-Prop
      is-closed-under-multiplication-by-scalar-prop-subset-left-module-Ring
```

### The condition that a subset contains zero

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1) (M : left-module-Ring l2 R) (S : subset-left-module-Ring l3 R M)
  where

  contains-zero-prop-subset-left-module-Ring : Prop l3
  contains-zero-prop-subset-left-module-Ring = S (zero-left-module-Ring R M)

  contains-zero-subset-left-module-Ring : UU l3
  contains-zero-subset-left-module-Ring =
    type-Prop contains-zero-prop-subset-left-module-Ring
```

### The condition that a subset is closed under negations

```agda
module _
  {l1 l2 l3 : Level}
  (R : Ring l1) (M : left-module-Ring l2 R) (S : subset-left-module-Ring l3 R M)
  where

  is-closed-under-negation-prop-subset-left-module-Ring : Prop (l2 ⊔ l3)
  is-closed-under-negation-prop-subset-left-module-Ring =
    Π-Prop
      ( type-left-module-Ring R M)
      ( λ x → hom-Prop (S x) (S (neg-left-module-Ring R M x)))

  is-closed-under-negation-subset-left-module-Ring : UU (l2 ⊔ l3)
  is-closed-under-negation-subset-left-module-Ring =
    type-Prop is-closed-under-negation-prop-subset-left-module-Ring
```
