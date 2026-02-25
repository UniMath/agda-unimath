# Subsets of rings

```agda
module ring-theory.subsets-rings where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.iterated-dependent-product-types
open import foundation.propositional-extensionality
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.universe-levels

open import group-theory.subgroups-abelian-groups

open import ring-theory.rings
```

</details>

## Idea

A {{#concept "subset" Disambiguation="of a ring" Agda=subset-Ring}} of a
[ring](ring-theory.rings.md) `R` is a [subtype](foundation.subtypes.md) of the
underlying type of `R`.

## Definition

### Subsets of rings

```agda
subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → UU (lsuc l ⊔ l1)
subset-Ring l R = subtype l (type-Ring R)

is-set-subset-Ring :
  (l : Level) {l1 : Level} (R : Ring l1) → is-set (subset-Ring l R)
is-set-subset-Ring l R =
  is-set-function-type is-set-type-Prop

module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  is-in-subset-Ring : type-Ring R → UU l2
  is-in-subset-Ring = is-in-subtype S

  is-prop-is-in-subset-Ring : (x : type-Ring R) → is-prop (is-in-subset-Ring x)
  is-prop-is-in-subset-Ring = is-prop-is-in-subtype S

  type-subset-Ring : UU (l1 ⊔ l2)
  type-subset-Ring = type-subtype S

  inclusion-subset-Ring : type-subset-Ring → type-Ring R
  inclusion-subset-Ring = inclusion-subtype S

  ap-inclusion-subset-Ring :
    (x y : type-subset-Ring) →
    x ＝ y → (inclusion-subset-Ring x ＝ inclusion-subset-Ring y)
  ap-inclusion-subset-Ring = ap-inclusion-subtype S

  is-in-subset-inclusion-subset-Ring :
    (x : type-subset-Ring) → is-in-subset-Ring (inclusion-subset-Ring x)
  is-in-subset-inclusion-subset-Ring =
    is-in-subtype-inclusion-subtype S

  is-closed-under-eq-subset-Ring :
    {x y : type-Ring R} → is-in-subset-Ring x → (x ＝ y) → is-in-subset-Ring y
  is-closed-under-eq-subset-Ring =
    is-closed-under-eq-subtype S

  is-closed-under-eq-subset-Ring' :
    {x y : type-Ring R} → is-in-subset-Ring y → (x ＝ y) → is-in-subset-Ring x
  is-closed-under-eq-subset-Ring' =
    is-closed-under-eq-subtype' S
```

### The condition that a subset contains zero

```agda
module _
  {l1 l2 : Level} (R : Ring l1) (S : subset-Ring l2 R)
  where

  contains-zero-prop-subset-Ring : Prop l2
  contains-zero-prop-subset-Ring = S (zero-Ring R)

  contains-zero-subset-Ring : UU l2
  contains-zero-subset-Ring = is-in-subset-Ring R S (zero-Ring R)
```

### The condition that a subset contains one

```agda
  contains-one-prop-subset-Ring : Prop l2
  contains-one-prop-subset-Ring = S (one-Ring R)

  contains-one-subset-Ring : UU l2
  contains-one-subset-Ring = is-in-subset-Ring R S (one-Ring R)
```

### The condition that a subset is closed under addition

```agda
  is-closed-under-addition-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-addition-subset-Ring =
    {x y : type-Ring R} →
    is-in-subset-Ring R S x → is-in-subset-Ring R S y →
    is-in-subset-Ring R S (add-Ring R x y)

  abstract
    is-prop-is-closed-under-addition-subset-Ring :
      is-prop is-closed-under-addition-subset-Ring
    is-prop-is-closed-under-addition-subset-Ring =
      is-prop-iterated-implicit-Π 2
        ( λ x y → is-prop-function-Prop (hom-Prop (S y) (S (add-Ring R x y))))

  is-closed-under-addition-prop-subset-Ring : Prop (l1 ⊔ l2)
  is-closed-under-addition-prop-subset-Ring =
    ( is-closed-under-addition-subset-Ring ,
      is-prop-is-closed-under-addition-subset-Ring)
```

### The condition that a subset is closed under negatives

```agda
  is-closed-under-negatives-prop-subset-Ring : Prop (l1 ⊔ l2)
  is-closed-under-negatives-prop-subset-Ring =
    implicit-Π-Prop
      ( type-Ring R)
      ( λ x → hom-Prop (S x) (S (neg-Ring R x)))

  is-closed-under-negatives-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-negatives-subset-Ring =
    {x : type-Ring R} →
    is-in-subset-Ring R S x → is-in-subset-Ring R S (neg-Ring R x)
```

### The condition that a subset is closed under multiplication

```agda
  is-closed-under-multiplication-prop-subset-Ring : Prop (l1 ⊔ l2)
  is-closed-under-multiplication-prop-subset-Ring =
    Π-Prop
      ( type-Ring R)
      ( λ x →
        Π-Prop
          ( type-Ring R)
          ( λ y → hom-Prop (S x) (hom-Prop (S y) (S (mul-Ring R x y)))))

  is-closed-under-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-multiplication-subset-Ring =
    (x y : type-Ring R) → is-in-subset-Ring R S x → is-in-subset-Ring R S y →
    is-in-subset-Ring R S (mul-Ring R x y)
```

### The condition that a subset is closed under multiplication from the left by an arbitrary element

```agda
  is-closed-under-left-multiplication-subset-Ring-Prop : Prop (l1 ⊔ l2)
  is-closed-under-left-multiplication-subset-Ring-Prop =
    Π-Prop
      ( type-Ring R)
      ( λ x →
        Π-Prop
          ( type-Ring R)
          ( λ y →
            function-Prop
              ( is-in-subset-Ring R S y)
              ( S (mul-Ring R x y))))

  is-closed-under-left-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-left-multiplication-subset-Ring =
    type-Prop is-closed-under-left-multiplication-subset-Ring-Prop

  is-prop-is-closed-under-left-multiplication-subset-Ring :
    is-prop is-closed-under-left-multiplication-subset-Ring
  is-prop-is-closed-under-left-multiplication-subset-Ring =
    is-prop-type-Prop is-closed-under-left-multiplication-subset-Ring-Prop
```

### The condition that a subset is closed-under-multiplication from the right by an arbitrary element

```agda
  is-closed-under-right-multiplication-subset-Ring-Prop : Prop (l1 ⊔ l2)
  is-closed-under-right-multiplication-subset-Ring-Prop =
    Π-Prop
      ( type-Ring R)
      ( λ x →
        Π-Prop
          ( type-Ring R)
          ( λ y →
            function-Prop
              ( is-in-subset-Ring R S x)
              ( S (mul-Ring R x y))))

  is-closed-under-right-multiplication-subset-Ring : UU (l1 ⊔ l2)
  is-closed-under-right-multiplication-subset-Ring =
    type-Prop is-closed-under-right-multiplication-subset-Ring-Prop

  is-prop-is-closed-under-right-multiplication-subset-Ring :
    is-prop is-closed-under-right-multiplication-subset-Ring
  is-prop-is-closed-under-right-multiplication-subset-Ring =
    is-prop-type-Prop is-closed-under-right-multiplication-subset-Ring-Prop
```

### The condition that a subset is an additive subgroup

```agda
module _
  {l1 : Level} (R : Ring l1)
  where

  is-additive-subgroup-subset-Ring :
    {l2 : Level} → subset-Ring l2 R → UU (l1 ⊔ l2)
  is-additive-subgroup-subset-Ring = is-subgroup-Ab (ab-Ring R)

  is-prop-is-additive-subgroup-subset-Ring :
    {l2 : Level} (A : subset-Ring l2 R) →
    is-prop (is-additive-subgroup-subset-Ring A)
  is-prop-is-additive-subgroup-subset-Ring =
    is-prop-is-subgroup-Ab (ab-Ring R)
```
