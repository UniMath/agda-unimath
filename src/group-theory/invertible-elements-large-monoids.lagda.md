# Invertible elements in large monoids

```agda
module group-theory.invertible-elements-large-monoids where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.invertible-elements-monoids
open import group-theory.large-monoids
```

</details>

## Idea

An element `x` in a [large monoid](group-theory.large-monoids.md) `M` is said to
be **left invertible** if there is an element `y : M` at the same universe level
such that `yx ＝ e`, and it is said to be **right invertible** if there is an
element `y : M` such that `xy ＝ e`. The element `x` is said to be
{{#concept "invertible" Disambiguation="in a large monoid" Agda=is-invertible-element-Large-Monoid}}
if it has a two-sided inverse, i.e., if there is an element `y : M` such that
`xy = e` and `yx = e`. Left inverses of elements are also called **retractions**
and right inverses are also called **sections**.

## Definition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (M : Large-Monoid α β)
  {l1 : Level}
  (x : type-Large-Monoid M l1)
  where

  is-left-inverse-element-prop-Large-Monoid :
    {l2 : Level} (y : type-Large-Monoid M l2) → Prop (β (l1 ⊔ l2) lzero)
  is-left-inverse-element-prop-Large-Monoid y =
    is-unit-prop-Large-Monoid M (mul-Large-Monoid M y x)

  is-right-inverse-element-prop-Large-Monoid :
    {l2 : Level} (y : type-Large-Monoid M l2) → Prop (β (l1 ⊔ l2) lzero)
  is-right-inverse-element-prop-Large-Monoid y =
    is-unit-prop-Large-Monoid M (mul-Large-Monoid M x y)

  is-inverse-element-prop-Large-Monoid :
    {l2 : Level} (y : type-Large-Monoid M l2) → Prop (β (l1 ⊔ l2) lzero)
  is-inverse-element-prop-Large-Monoid y =
    ( is-right-inverse-element-prop-Large-Monoid y) ∧
    ( is-left-inverse-element-prop-Large-Monoid y)

  is-left-inverse-element-Large-Monoid :
    {l2 : Level} (y : type-Large-Monoid M l2) → UU (β (l1 ⊔ l2) lzero)
  is-left-inverse-element-Large-Monoid =
    is-in-subtype is-left-inverse-element-prop-Large-Monoid

  is-right-inverse-element-Large-Monoid :
    {l2 : Level} (y : type-Large-Monoid M l2) → UU (β (l1 ⊔ l2) lzero)
  is-right-inverse-element-Large-Monoid =
    is-in-subtype is-right-inverse-element-prop-Large-Monoid

  is-inverse-element-Large-Monoid :
    {l2 : Level} (y : type-Large-Monoid M l2) → UU (β (l1 ⊔ l2) lzero)
  is-inverse-element-Large-Monoid =
    is-in-subtype is-inverse-element-prop-Large-Monoid

  is-left-invertible-element-Large-Monoid : UU (α l1 ⊔ β l1 lzero)
  is-left-invertible-element-Large-Monoid =
    Σ (type-Large-Monoid M l1) is-left-inverse-element-Large-Monoid

  is-right-invertible-element-Large-Monoid : UU (α l1 ⊔ β l1 lzero)
  is-right-invertible-element-Large-Monoid =
    Σ (type-Large-Monoid M l1) is-right-inverse-element-Large-Monoid

  is-invertible-element-Large-Monoid : UU (α l1 ⊔ β l1 lzero)
  is-invertible-element-Large-Monoid =
    Σ (type-Large-Monoid M l1) is-inverse-element-Large-Monoid

  inv-is-invertible-element-Large-Monoid :
    is-invertible-element-Large-Monoid → type-Large-Monoid M l1
  inv-is-invertible-element-Large-Monoid = pr1

  is-inverse-inv-is-invertible-element-Large-Monoid :
    (H : is-invertible-element-Large-Monoid) →
    is-inverse-element-Large-Monoid (inv-is-invertible-element-Large-Monoid H)
  is-inverse-inv-is-invertible-element-Large-Monoid = pr2
```

## Properties

### Being an invertible element is a proposition

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (M : Large-Monoid α β)
  {l1 : Level}
  (x : type-Large-Monoid M l1)
  (let _*M_ = mul-Large-Monoid M)
  where

  open similarity-reasoning-Large-Monoid M

  abstract
    all-elements-equal-is-invertible-element-Large-Monoid :
      all-elements-equal (is-invertible-element-Large-Monoid M x)
    all-elements-equal-is-invertible-element-Large-Monoid
      (y , xy~1 , yx~1) (z , xz~1 , zx~1) =
      eq-type-subtype
        ( is-inverse-element-prop-Large-Monoid M x)
        ( eq-sim-Large-Monoid M y z
          ( similarity-reasoning
            y
            ~ y *M (x *M z)
              by
                symmetric-sim-Large-Monoid M _ _
                  ( sim-right-is-unit-law-mul-Large-Monoid M _ _ xz~1)
            ~ (y *M x) *M z
              by
                sim-eq-Large-Monoid M
                  ( inv (associative-mul-Large-Monoid M y x z))
            ~ z
              by sim-left-is-unit-law-mul-Large-Monoid M _ _ yx~1))

    is-prop-is-invertible-element-Large-Monoid :
      is-prop (is-invertible-element-Large-Monoid M x)
    is-prop-is-invertible-element-Large-Monoid =
      is-prop-all-elements-equal
        ( all-elements-equal-is-invertible-element-Large-Monoid)

  is-invertible-element-prop-Large-Monoid : Prop (α l1 ⊔ β l1 lzero)
  is-invertible-element-prop-Large-Monoid =
    ( is-invertible-element-Large-Monoid M x ,
      is-prop-is-invertible-element-Large-Monoid)
```

### If `x` is invertible, so is its inverse

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (M : Large-Monoid α β)
  {l1 : Level}
  (x : type-Large-Monoid M l1)
  where

  inverse-is-invertible-element-Large-Monoid :
    (H : is-invertible-element-Large-Monoid M x) →
    is-invertible-element-Large-Monoid M
      ( inv-is-invertible-element-Large-Monoid M x H)
  inverse-is-invertible-element-Large-Monoid (y , xy~1 , yx~1) =
    ( x , yx~1 , xy~1)
```

### An element is invertible in a large monoid if and only if it is invertible in the corresponding small monoid

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (M : Large-Monoid α β)
  {l1 : Level}
  (x : type-Large-Monoid M l1)
  where

  is-invertible-small-is-invertible-element-Large-Monoid :
    is-invertible-element-Large-Monoid M x →
    is-invertible-element-Monoid (monoid-Large-Monoid M l1) x
  is-invertible-small-is-invertible-element-Large-Monoid (x' , xx'~1 , x'x~1) =
    ( x' ,
      eq-raise-unit-is-unit-Large-Monoid M _ xx'~1 ,
      eq-raise-unit-is-unit-Large-Monoid M _ x'x~1)

  is-invertible-is-invertible-small-element-Large-Monoid :
    is-invertible-element-Monoid (monoid-Large-Monoid M l1) x →
    is-invertible-element-Large-Monoid M x
  is-invertible-is-invertible-small-element-Large-Monoid (x' , xx'=1 , x'x=1) =
    ( x' ,
      inv-tr
        ( is-unit-Large-Monoid M)
        ( xx'=1)
        ( is-unit-raise-unit-Large-Monoid M _) ,
      inv-tr
        ( is-unit-Large-Monoid M)
        ( x'x=1)
        ( is-unit-raise-unit-Large-Monoid M _))

  is-invertible-small-iff-is-invertible-element-Large-Monoid :
    is-invertible-element-Large-Monoid M x ↔
    is-invertible-element-Monoid (monoid-Large-Monoid M l1) x
  is-invertible-small-iff-is-invertible-element-Large-Monoid =
    ( is-invertible-small-is-invertible-element-Large-Monoid ,
      is-invertible-is-invertible-small-element-Large-Monoid)
```

### Invertible elements are closed under multiplication

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (M : Large-Monoid α β)
  {l1 l2 : Level}
  (x : type-Large-Monoid M l1)
  (y : type-Large-Monoid M l2)
  (let _*M_ = mul-Large-Monoid M)
  where

  open similarity-reasoning-Large-Monoid M

  is-left-invertible-element-mul-Large-Monoid :
    is-left-invertible-element-Large-Monoid M x →
    is-left-invertible-element-Large-Monoid M y →
    is-left-invertible-element-Large-Monoid M (mul-Large-Monoid M x y)
  is-left-invertible-element-mul-Large-Monoid (x' , x'x~1) (y' , y'y~1) =
    ( y' *M x' ,
      ( similarity-reasoning
        (y' *M x') *M (x *M y)
        ~ y' *M (x' *M (x *M y))
          by sim-eq-Large-Monoid M (associative-mul-Large-Monoid M y' x' _)
        ~ y' *M ((x' *M x) *M y)
          by
            sim-eq-Large-Monoid M
              ( ap
                ( y' *M_)
                ( inv (associative-mul-Large-Monoid M x' x y)))
        ~ y' *M y
          by
            preserves-sim-left-mul-Large-Monoid M y' _ _
              ( sim-left-is-unit-law-mul-Large-Monoid M (x' *M x) y x'x~1)
        ~ unit-Large-Monoid M
          by y'y~1))

  is-right-invertible-element-mul-Large-Monoid :
    is-right-invertible-element-Large-Monoid M x →
    is-right-invertible-element-Large-Monoid M y →
    is-right-invertible-element-Large-Monoid M (mul-Large-Monoid M x y)
  is-right-invertible-element-mul-Large-Monoid (x' , xx'~1) (y' , yy'~1) =
    ( y' *M x' ,
      ( similarity-reasoning
        (x *M y) *M (y' *M x')
        ~ x *M (y *M (y' *M x'))
          by
            sim-eq-Large-Monoid M (associative-mul-Large-Monoid M x y _)
        ~ x *M ((y *M y') *M x')
          by
            sim-eq-Large-Monoid M
              ( ap
                ( x *M_)
                ( inv (associative-mul-Large-Monoid M y y' x')))
        ~ x *M x'
          by
            preserves-sim-left-mul-Large-Monoid M x _ _
              ( sim-left-is-unit-law-mul-Large-Monoid M (y *M y') x' yy'~1)
        ~ unit-Large-Monoid M
          by xx'~1))

  is-invertible-element-mul-Large-Monoid :
    is-invertible-element-Large-Monoid M x →
    is-invertible-element-Large-Monoid M y →
    is-invertible-element-Large-Monoid M (mul-Large-Monoid M x y)
  is-invertible-element-mul-Large-Monoid
    ( x' , xx'~1 , x'x~1) (y' , yy'~1 , y'y~1) =
    ( y' *M x' ,
      pr2
        ( is-right-invertible-element-mul-Large-Monoid
          ( x' , xx'~1)
          ( y' , yy'~1)) ,
      pr2
        ( is-left-invertible-element-mul-Large-Monoid
          ( x' , x'x~1)
          ( y' , y'y~1)))
```

### An element of a large monoid is invertible if and only if multiplying by it on the left (or right) is an equivalence

```agda
module _
  {α : Level → Level}
  {β : Level → Level → Level}
  (M : Large-Monoid α β)
  {l1 : Level}
  (x : type-Large-Monoid M l1)
  where

  is-equiv-left-mul-iff-is-invertible-element-Large-Monoid :
    is-invertible-element-Large-Monoid M x ↔
    is-equiv (mul-Large-Monoid M x)
  is-equiv-left-mul-iff-is-invertible-element-Large-Monoid =
    ( is-equiv-mul-iff-is-invertible-element-Monoid
      ( monoid-Large-Monoid M l1)) ∘iff
    ( is-invertible-small-iff-is-invertible-element-Large-Monoid M x)

  is-equiv-right-mul-iff-is-invertible-element-Large-Monoid :
    is-invertible-element-Large-Monoid M x ↔
    is-equiv (mul-Large-Monoid' M x)
  is-equiv-right-mul-iff-is-invertible-element-Large-Monoid =
    ( is-equiv-mul-iff-is-invertible-element-Monoid'
      ( monoid-Large-Monoid M l1)) ∘iff
    ( is-invertible-small-iff-is-invertible-element-Large-Monoid M x)
```

## See also

- [Invertible elements in (small) monoids](group-theory.invertible-elements-monoids.md)
