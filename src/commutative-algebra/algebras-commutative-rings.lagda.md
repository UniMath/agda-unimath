# Algebras over commutative rings

```agda
module commutative-algebra.algebras-commutative-rings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-rings

open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.sets
open import foundation.universe-levels

open import group-theory.abelian-groups

open import linear-algebra.bilinear-maps-left-modules-commutative-rings
open import linear-algebra.left-modules-commutative-rings
open import linear-algebra.linear-maps-left-modules-commutative-rings
```

</details>

## Idea

An
{{#concept "algebra" WDID=Q2030545 WD="algebra over a commutative ring" Disambiguation="over a commutative ring" Agda=algebra-Commutative-Ring}}
over a [commutative ring](commutative-algebra.commutative-rings.md) `R` is a
[left module](linear-algebra.left-modules-commutative-rings.md) `M` over `R`
equipped with a
[bilinear map](linear-algebra.bilinear-maps-left-modules-commutative-rings.md),
called its product, `* : M → M → M`.

## Definition

```agda
algebra-Commutative-Ring :
  {l1 : Level} (l2 : Level) → Commutative-Ring l1 → UU (l1 ⊔ lsuc l2)
algebra-Commutative-Ring l2 R =
  Σ ( left-module-Commutative-Ring l2 R)
    ( λ M → bilinear-map-left-module-Commutative-Ring R M M M)
```

## Properties

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : algebra-Commutative-Ring l2 R)
  where

  left-module-algebra-Commutative-Ring : left-module-Commutative-Ring l2 R
  left-module-algebra-Commutative-Ring = pr1 A

  set-algebra-Commutative-Ring : Set l2
  set-algebra-Commutative-Ring =
    set-left-module-Commutative-Ring R left-module-algebra-Commutative-Ring

  type-algebra-Commutative-Ring : UU l2
  type-algebra-Commutative-Ring = type-Set set-algebra-Commutative-Ring

  ab-add-algebra-Commutative-Ring : Ab l2
  ab-add-algebra-Commutative-Ring =
    ab-left-module-Commutative-Ring R left-module-algebra-Commutative-Ring

  add-algebra-Commutative-Ring :
    type-algebra-Commutative-Ring → type-algebra-Commutative-Ring →
    type-algebra-Commutative-Ring
  add-algebra-Commutative-Ring = add-Ab ab-add-algebra-Commutative-Ring

  zero-algebra-Commutative-Ring : type-algebra-Commutative-Ring
  zero-algebra-Commutative-Ring = zero-Ab ab-add-algebra-Commutative-Ring

  neg-algebra-Commutative-Ring :
    type-algebra-Commutative-Ring → type-algebra-Commutative-Ring
  neg-algebra-Commutative-Ring = neg-Ab ab-add-algebra-Commutative-Ring

  scalar-mul-algebra-Commutative-Ring :
    type-Commutative-Ring R → type-algebra-Commutative-Ring →
    type-algebra-Commutative-Ring
  scalar-mul-algebra-Commutative-Ring =
    mul-left-module-Commutative-Ring R left-module-algebra-Commutative-Ring

  bilinear-mul-algebra-Commutative-Ring :
    bilinear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-algebra-Commutative-Ring)
      ( left-module-algebra-Commutative-Ring)
      ( left-module-algebra-Commutative-Ring)
  bilinear-mul-algebra-Commutative-Ring = pr2 A

  mul-algebra-Commutative-Ring :
    type-algebra-Commutative-Ring → type-algebra-Commutative-Ring →
    type-algebra-Commutative-Ring
  mul-algebra-Commutative-Ring =
    map-bilinear-map-left-module-Commutative-Ring
      ( R)
      ( left-module-algebra-Commutative-Ring)
      ( left-module-algebra-Commutative-Ring)
      ( left-module-algebra-Commutative-Ring)
      ( bilinear-mul-algebra-Commutative-Ring)
```

### Distributivity of multiplication over addition

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : algebra-Commutative-Ring l2 R)
  where

  abstract
    left-distributive-mul-add-algebra-Commutative-Ring :
      (x y z : type-algebra-Commutative-Ring R A) →
      mul-algebra-Commutative-Ring R A
        ( x)
        ( add-algebra-Commutative-Ring R A y z) ＝
      add-algebra-Commutative-Ring R A
        ( mul-algebra-Commutative-Ring R A x y)
        ( mul-algebra-Commutative-Ring R A x z)
    left-distributive-mul-add-algebra-Commutative-Ring x =
      is-additive-map-linear-map-left-module-Commutative-Ring
        ( R)
        ( left-module-algebra-Commutative-Ring R A)
        ( left-module-algebra-Commutative-Ring R A)
        ( right-linear-map-bilinear-map-left-module-Commutative-Ring
          ( R)
          ( left-module-algebra-Commutative-Ring R A)
          ( left-module-algebra-Commutative-Ring R A)
          ( left-module-algebra-Commutative-Ring R A)
          ( bilinear-mul-algebra-Commutative-Ring R A)
          ( x))

    right-distributive-mul-add-algebra-Commutative-Ring :
      (x y z : type-algebra-Commutative-Ring R A) →
      mul-algebra-Commutative-Ring R A
        ( add-algebra-Commutative-Ring R A x y)
        ( z) ＝
      add-algebra-Commutative-Ring R A
        ( mul-algebra-Commutative-Ring R A x z)
        ( mul-algebra-Commutative-Ring R A y z)
    right-distributive-mul-add-algebra-Commutative-Ring x y z =
      is-additive-map-linear-map-left-module-Commutative-Ring
        ( R)
        ( left-module-algebra-Commutative-Ring R A)
        ( left-module-algebra-Commutative-Ring R A)
        ( left-linear-map-bilinear-map-left-module-Commutative-Ring
          ( R)
          ( left-module-algebra-Commutative-Ring R A)
          ( left-module-algebra-Commutative-Ring R A)
          ( left-module-algebra-Commutative-Ring R A)
          ( bilinear-mul-algebra-Commutative-Ring R A)
          ( z))
        ( x)
        ( y)
```

### Zero laws of multiplication

```agda
module _
  {l1 l2 : Level}
  (R : Commutative-Ring l1)
  (A : algebra-Commutative-Ring l2 R)
  where

  abstract
    left-zero-law-mul-algebra-Commutative-Ring :
      (x : type-algebra-Commutative-Ring R A) →
      mul-algebra-Commutative-Ring R A (zero-algebra-Commutative-Ring R A) x ＝
      zero-algebra-Commutative-Ring R A
    left-zero-law-mul-algebra-Commutative-Ring =
      left-zero-law-bilinear-map-left-module-Commutative-Ring
        ( R)
        ( left-module-algebra-Commutative-Ring R A)
        ( left-module-algebra-Commutative-Ring R A)
        ( left-module-algebra-Commutative-Ring R A)
        ( bilinear-mul-algebra-Commutative-Ring R A)

    right-zero-law-mul-algebra-Commutative-Ring :
      (x : type-algebra-Commutative-Ring R A) →
      mul-algebra-Commutative-Ring R A x (zero-algebra-Commutative-Ring R A) ＝
      zero-algebra-Commutative-Ring R A
    right-zero-law-mul-algebra-Commutative-Ring =
      right-zero-law-bilinear-map-left-module-Commutative-Ring
        ( R)
        ( left-module-algebra-Commutative-Ring R A)
        ( left-module-algebra-Commutative-Ring R A)
        ( left-module-algebra-Commutative-Ring R A)
        ( bilinear-mul-algebra-Commutative-Ring R A)
```

### Every commutative ring is an algebra over itself

```agda
algebra-commutative-ring-Commutative-Ring :
  {l : Level} (R : Commutative-Ring l) → algebra-Commutative-Ring l R
algebra-commutative-ring-Commutative-Ring R =
  ( left-module-commutative-ring-Commutative-Ring R ,
    mul-Commutative-Ring R ,
    ( λ x →
      ( ( λ y z → right-distributive-mul-add-Commutative-Ring R y z x) ,
        ( λ y z → associative-mul-Commutative-Ring R y z x))) ,
    ( λ y →
      ( left-distributive-mul-add-Commutative-Ring R y ,
        left-swap-mul-Commutative-Ring R y)))
```

## External links

- [Algebras over rings](https://en.wikipedia.org/wiki/Algebra_over_a_field#Generalization:_algebra_over_a_ring)
  on Wikipedia
