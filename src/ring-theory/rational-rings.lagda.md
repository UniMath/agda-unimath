# Rational rings

```agda
{-# OPTIONS --lossy-unification #-}

module ring-theory.rational-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.ring-of-integers
open import elementary-number-theory.ring-of-rational-numbers
open import elementary-number-theory.unit-fractions-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-abelian-groups

open import ring-theory.dependent-products-rings
open import ring-theory.groups-of-units-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.localizations-rings
open import ring-theory.opposite-rings
open import ring-theory.rings
```

</details>

## Idea

A {{#concept "rational ring" Agda=Rational-Ring}} is a
[ring](ring-theory.rings.md) where the images of
[positive integers](elementary-number-theory.positive-integers.md) by the
[initial ring homomorphism](elementary-number-theory.ring-of-integers.md)) are
[invertible elements](ring-theory.invertible-elements-rings.md). For any ring
`R`, if there exists a [ring homomorphism](ring-theory.homomorphisms-rings.md)
`f : ℚ → R`, then `R` is **rational** and `f` is
[homotopic](foundation.homotopies.md) to the extension of the
[initial ring homomorphism](elementary-number-theory.ring-of-integers.md)
`ι : ℤ → R` defined by `γ : (p/q : ℚ) ↦ (ι p)(ι q)⁻¹`. Therefore, for any ring
`R`, the type of ring homomorphisms `ℚ → R` is a
[proposition](foundation.propositions.md).

## Definitions

### The property of being a rational ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-rational-prop-Ring : Prop l
  is-rational-prop-Ring =
    inverts-subset-prop-hom-Ring
      ( ℤ-Ring)
      ( R)
      ( subtype-positive-ℤ)
      ( initial-hom-Ring R)

  is-rational-Ring : UU l
  is-rational-Ring = type-Prop is-rational-prop-Ring

  is-prop-is-rational-Ring : is-prop is-rational-Ring
  is-prop-is-rational-Ring = is-prop-type-Prop is-rational-prop-Ring
```

### The type of rational rings

```agda
Rational-Ring : (l : Level) → UU (lsuc l)
Rational-Ring l = Σ (Ring l) is-rational-Ring

module _
  {l : Level} (R : Rational-Ring l)
  where

  ring-Rational-Ring : Ring l
  ring-Rational-Ring = pr1 R

  type-Rational-Ring : UU l
  type-Rational-Ring = type-Ring ring-Rational-Ring

  is-rational-ring-Rational-Ring : is-rational-Ring ring-Rational-Ring
  is-rational-ring-Rational-Ring = pr2 R

  mul-Rational-Ring :
    type-Rational-Ring → type-Rational-Ring → type-Rational-Ring
  mul-Rational-Ring = mul-Ring ring-Rational-Ring

  add-Rational-Ring :
    type-Rational-Ring → type-Rational-Ring → type-Rational-Ring
  add-Rational-Ring = add-Ring ring-Rational-Ring

  is-invertible-positive-integer-Rational-Ring :
    (k : ℤ⁺) →
    is-invertible-element-Ring
      ( ring-Rational-Ring)
      ( map-initial-hom-Ring ring-Rational-Ring (int-positive-ℤ k))
  is-invertible-positive-integer-Rational-Ring (k , k>0) =
    is-rational-ring-Rational-Ring k k>0

  inv-positive-integer-Rational-Ring : ℤ⁺ → type-Rational-Ring
  inv-positive-integer-Rational-Ring k =
    inv-is-invertible-element-Ring
      ( ring-Rational-Ring)
      ( is-invertible-positive-integer-Rational-Ring k)

  left-inverse-law-positive-integer-Rational-Ring :
    (k : ℤ⁺) →
    mul-Ring
      ( ring-Rational-Ring)
      ( inv-positive-integer-Rational-Ring k)
      ( map-initial-hom-Ring ring-Rational-Ring (int-positive-ℤ k)) ＝
    one-Ring ring-Rational-Ring
  left-inverse-law-positive-integer-Rational-Ring (k , k>0) =
    is-left-inverse-inv-is-invertible-element-Ring
      ( ring-Rational-Ring)
      ( is-rational-ring-Rational-Ring k k>0)

  right-inverse-law-positive-integer-Rational-Ring :
    (k : ℤ⁺) →
    mul-Ring
      ( ring-Rational-Ring)
      ( map-initial-hom-Ring ring-Rational-Ring (int-positive-ℤ k))
      ( inv-positive-integer-Rational-Ring k) ＝
    one-Ring ring-Rational-Ring
  right-inverse-law-positive-integer-Rational-Ring (k , k>0) =
    is-right-inverse-inv-is-invertible-element-Ring
      ( ring-Rational-Ring)
      ( is-rational-ring-Rational-Ring k k>0)
```

### Homorphisms of rational rings

```agda
module _
  {l1 l2 : Level} (A : Rational-Ring l1) (B : Rational-Ring l2)
  where

  hom-Rational-Ring : UU (l1 ⊔ l2)
  hom-Rational-Ring =
    hom-Ring
      ( ring-Rational-Ring A)
      ( ring-Rational-Ring B)

  map-hom-Rational-Ring :
    hom-Rational-Ring → type-Rational-Ring A → type-Rational-Ring B
  map-hom-Rational-Ring =
    map-hom-Ring
      ( ring-Rational-Ring A)
      ( ring-Rational-Ring B)
```

### The initial ring homomorphism into a rational ring

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  initial-hom-integer-Rational-Ring : hom-Ring ℤ-Ring (ring-Rational-Ring R)
  initial-hom-integer-Rational-Ring =
    initial-hom-Ring (ring-Rational-Ring R)

  map-initial-hom-integer-Rational-Ring : ℤ → type-Rational-Ring R
  map-initial-hom-integer-Rational-Ring =
    map-initial-hom-Ring (ring-Rational-Ring R)
```

### Fractional extension of the initial ring homomorphism into a rational ring

It is defined as `φ : (p/q : fraction-ℤ) ↦ (ι p)(ι q)⁻¹ = (ι q)⁻¹(ι p)` where
`ι : ℤ → R` is the initial ring homomorphism.

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  map-initial-hom-fraction-Rational-Ring : fraction-ℤ → type-Rational-Ring R
  map-initial-hom-fraction-Rational-Ring (p , q) =
    mul-Rational-Ring
      ( R)
      ( map-initial-hom-integer-Rational-Ring R p)
      ( inv-positive-integer-Rational-Ring R q)

  map-initial-hom-fraction-Rational-Ring' : fraction-ℤ → type-Rational-Ring R
  map-initial-hom-fraction-Rational-Ring' (p , q) =
    mul-Rational-Ring
      ( R)
      ( inv-positive-integer-Rational-Ring R q)
      ( map-initial-hom-integer-Rational-Ring R p)

  htpy-map-initial-hom-fraction-Rational-Ring' :
    map-initial-hom-fraction-Rational-Ring ~
    map-initial-hom-fraction-Rational-Ring'
  htpy-map-initial-hom-fraction-Rational-Ring' (p , q) =
    ( inv
      ( left-unit-law-mul-Ring
        ( ring-Rational-Ring R)
        ( mul-Rational-Ring R pr qr'))) ∙
    ( ap
      ( mul-Ring'
        ( ring-Rational-Ring R)
        ( mul-Rational-Ring R pr qr'))
      ( inv (qr'×qr=1))) ∙
    ( associative-mul-Ring
      ( ring-Rational-Ring R)
      ( qr')
      ( qr)
      ( mul-Rational-Ring R pr qr')) ∙
    ( ap (mul-Rational-Ring R qr') (qr×pr×qr'=pr))
    where

    pr qr qr' : type-Rational-Ring R
    pr = map-initial-hom-Ring (ring-Rational-Ring R) p
    qr = map-initial-hom-Ring (ring-Rational-Ring R) (int-positive-ℤ q)
    qr' = inv-positive-integer-Rational-Ring R q

    qr'×qr=1 :
      mul-Ring (ring-Rational-Ring R) qr' qr ＝ one-Ring (ring-Rational-Ring R)
    qr'×qr=1 =
      left-inverse-law-positive-integer-Rational-Ring R q

    qr×pr×qr'=pr : mul-Rational-Ring R qr (mul-Rational-Ring R pr qr') ＝ pr
    qr×pr×qr'=pr =
      ( inv (associative-mul-Ring (ring-Rational-Ring R) qr pr qr')) ∙
      ( ap
        ( mul-Ring' (ring-Rational-Ring R) qr')
        ( is-commutative-map-initial-hom-Ring
          ( ring-Rational-Ring R)
          ( int-positive-ℤ q)
          ( p))) ∙
      ( associative-mul-Ring (ring-Rational-Ring R) pr qr qr') ∙
      ( ap
        ( mul-Rational-Ring R pr)
        ( right-inverse-law-positive-integer-Rational-Ring R q)) ∙
      ( right-unit-law-mul-Ring
        ( ring-Rational-Ring R)
        ( pr))
```

### Rational extension of the initial ring homomorphism into a rational ring

It is defined as `γ : (p/q : ℚ) ↦ (ι p)(ι q)⁻¹ = (ι q)⁻¹(ι p)` where `ι : ℤ → R`
is the initial ring homomorphism.

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  map-initial-hom-Rational-Ring : ℚ → type-Rational-Ring R
  map-initial-hom-Rational-Ring =
    map-initial-hom-fraction-Rational-Ring R ∘ fraction-ℚ

  map-initial-hom-Rational-Ring' : ℚ → type-Rational-Ring R
  map-initial-hom-Rational-Ring' =
    map-initial-hom-fraction-Rational-Ring' R ∘ fraction-ℚ

  htpy-map-initial-hom-Rational-Ring' :
    map-initial-hom-Rational-Ring ~
    map-initial-hom-Rational-Ring'
  htpy-map-initial-hom-Rational-Ring' x =
    htpy-map-initial-hom-fraction-Rational-Ring' R (fraction-ℚ x)
```

### The type of rational homomorphisms into a rational ring

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  rational-hom-Rational-Ring : UU l
  rational-hom-Rational-Ring =
    hom-Ring ring-ℚ (ring-Rational-Ring R)

  map-rational-hom-Rational-Ring :
    rational-hom-Rational-Ring → ℚ → type-Rational-Ring R
  map-rational-hom-Rational-Ring =
    map-hom-Ring ring-ℚ (ring-Rational-Ring R)
```

## Properties

### A ring is rational if and only if its opposite ring is rational

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-rational-op-is-rational-Ring :
    is-rational-Ring R → is-rational-Ring (op-Ring R)
  is-rational-op-is-rational-Ring H k k>0 =
    ( inv-positive-integer-Rational-Ring (R , H) (k , k>0)) ,
    ( left-inverse-law-positive-integer-Rational-Ring (R , H) (k , k>0)) ,
    ( right-inverse-law-positive-integer-Rational-Ring (R , H) (k , k>0))

  is-rational-is-rational-op-Ring :
    is-rational-Ring (op-Ring R) → is-rational-Ring R
  is-rational-is-rational-op-Ring H k k>0 =
    ( inv-positive-integer-Rational-Ring (op-Ring R , H) (k , k>0)) ,
    ( left-inverse-law-positive-integer-Rational-Ring
      ( op-Ring R , H)
      ( k , k>0)) ,
    ( right-inverse-law-positive-integer-Rational-Ring
      ( op-Ring R , H)
      ( k , k>0))

module _
  {l : Level}
  where

  op-Rational-Ring : Rational-Ring l → Rational-Ring l
  op-Rational-Ring R =
    ( op-Ring (ring-Rational-Ring R)) ,
    ( is-rational-op-is-rational-Ring
      ( ring-Rational-Ring R)
      ( is-rational-ring-Rational-Ring R))
```

### The product of rational rings is rational

```agda
module _
  {l1 l2 : Level} (I : UU l1) (R : I → Rational-Ring l2)
  where

  is-rational-ring-Π-Rational-Ring :
    is-rational-Ring (Π-Ring I (ring-Rational-Ring ∘ R))
  is-rational-ring-Π-Rational-Ring k k>0 =
    ( λ i → inv-positive-integer-Rational-Ring (R i) (k , k>0)) ,
    ( eq-htpy
      ( λ i →
        inv-tr
          ( λ h →
            mul-Rational-Ring
              ( R i)
              ( map-hom-Ring
                ( ℤ-Ring)
                ( Π-Ring I (ring-Rational-Ring ∘ R))
                ( h)
                ( k)
                ( i))
              ( inv-positive-integer-Rational-Ring (R i) (k , k>0)) ＝
            one-Ring (ring-Rational-Ring (R i)))
          ( eq-initial-hom-Π-Ring I (ring-Rational-Ring ∘ R))
          ( right-inverse-law-positive-integer-Rational-Ring
            ( R i)
            ( k , k>0)))) ,
    ( eq-htpy
      ( λ i →
        inv-tr
          ( λ h →
            mul-Rational-Ring
              ( R i)
              ( inv-positive-integer-Rational-Ring (R i) (k , k>0))
              ( map-hom-Ring
                ( ℤ-Ring)
                ( Π-Ring I (ring-Rational-Ring ∘ R))
                ( h)
                ( k)
                ( i)) ＝
            one-Ring (ring-Rational-Ring (R i)))
          ( eq-initial-hom-Π-Ring I (ring-Rational-Ring ∘ R))
          ( left-inverse-law-positive-integer-Rational-Ring
            ( R i)
            ( k , k>0))))

  Π-Rational-Ring : Rational-Ring (l1 ⊔ l2)
  Π-Rational-Ring =
    ( Π-Ring I (ring-Rational-Ring ∘ R)) ,
    ( is-rational-ring-Π-Rational-Ring)
```

### The inverse of the image of one in a rational ring is one

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  eq-one-inv-positive-one-Rational-Ring :
    one-Ring (ring-Rational-Ring R) ＝
    inv-positive-integer-Rational-Ring R one-ℤ⁺
  eq-one-inv-positive-one-Rational-Ring =
    contraction-right-inverse-is-invertible-element-Ring
      ( ring-Rational-Ring R)
      ( one-Ring (ring-Rational-Ring R))
      ( is-invertible-element-one-Ring (ring-Rational-Ring R))
      ( inv-positive-integer-Rational-Ring R one-ℤ⁺)
      ( ( ap
          ( mul-Ring'
            ( ring-Rational-Ring R)
            ( inv-positive-integer-Rational-Ring R one-ℤ⁺))
          ( inv (preserves-one-initial-hom-Ring (ring-Rational-Ring R)))) ∙
        ( right-inverse-law-positive-integer-Rational-Ring R one-ℤ⁺))
```

### The inverse of a product of positive integers in a rational ring is the product of their inverses

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  eq-mul-inv-positive-integer-Rational-Ring :
    (p q : ℤ⁺) →
    inv-positive-integer-Rational-Ring R (mul-positive-ℤ p q) ＝
    mul-Rational-Ring
      ( R)
      ( inv-positive-integer-Rational-Ring R p)
      ( inv-positive-integer-Rational-Ring R q)
  eq-mul-inv-positive-integer-Rational-Ring p q =
    contraction-right-inverse-is-invertible-element-Ring
      ( ring-Rational-Ring R)
      ( map-initial-hom-integer-Rational-Ring
        ( R)
        ( int-positive-ℤ (mul-positive-ℤ p q)))
      ( is-invertible-positive-integer-Rational-Ring
        ( R)
        ( mul-positive-ℤ p q))
      ( mul-Rational-Ring
        ( R)
        ( inv-positive-integer-Rational-Ring R p)
        ( inv-positive-integer-Rational-Ring R q))
      ( is-right-inverse-mul-inv-positive-integer-Rational-Ring)
    where

    lemma-map-mul :
      ( map-initial-hom-integer-Rational-Ring
        ( R)
        ( int-positive-ℤ (mul-positive-ℤ p q))) ＝
      mul-Rational-Ring
        ( R)
        ( map-initial-hom-integer-Rational-Ring R (int-positive-ℤ p))
        ( map-initial-hom-integer-Rational-Ring R (int-positive-ℤ q))
    lemma-map-mul =
      preserves-mul-initial-hom-Ring
        ( ring-Rational-Ring R)
        ( int-positive-ℤ p)
        ( int-positive-ℤ q)

    is-right-inverse-mul-inv-positive-integer-Rational-Ring :
      mul-Rational-Ring
        ( R)
        ( map-initial-hom-integer-Rational-Ring
          ( R)
          ( int-positive-ℤ (mul-positive-ℤ p q)))
        ( mul-Rational-Ring
          ( R)
          ( inv-positive-integer-Rational-Ring R p)
          ( inv-positive-integer-Rational-Ring R q)) ＝
      one-Ring (ring-Rational-Ring R)
    is-right-inverse-mul-inv-positive-integer-Rational-Ring =
      ( inv
        ( associative-mul-Ring
          ( ring-Rational-Ring R)
          ( map-initial-hom-integer-Rational-Ring
            ( R)
            ( int-positive-ℤ (mul-positive-ℤ p q)))
          ( inv-positive-integer-Rational-Ring R p)
          ( inv-positive-integer-Rational-Ring R q))) ∙
      ( ap
        ( mul-Ring'
          ( ring-Rational-Ring R)
          ( inv-positive-integer-Rational-Ring R q))
        ( ( htpy-map-initial-hom-fraction-Rational-Ring'
            ( R)
            ( int-positive-ℤ (mul-positive-ℤ p q) , p)) ∙
          ( ap
            ( mul-Rational-Ring R (inv-positive-integer-Rational-Ring R p))
            ( lemma-map-mul)) ∙
          ( inv
            ( associative-mul-Ring
              ( ring-Rational-Ring R)
              ( inv-positive-integer-Rational-Ring R p)
              ( map-initial-hom-integer-Rational-Ring R (int-positive-ℤ p))
              ( map-initial-hom-integer-Rational-Ring R (int-positive-ℤ q)))) ∙
            ( ap
              ( mul-Ring'
                ( ring-Rational-Ring R)
                ( map-initial-hom-integer-Rational-Ring R (int-positive-ℤ q)))
              ( left-inverse-law-positive-integer-Rational-Ring R p)) ∙
            ( left-unit-law-mul-Ring
              ( ring-Rational-Ring R)
              ( map-initial-hom-integer-Rational-Ring R (int-positive-ℤ q))))) ∙
      ( right-inverse-law-positive-integer-Rational-Ring R q)
```

### A ring `R` that admits a ring homomorphism `ℚ → R` is rational

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-rational-has-rational-hom-Ring : hom-Ring ring-ℚ R → is-rational-Ring R
  is-rational-has-rational-hom-Ring f =
    inv-tr
      ( inverts-subset-hom-Ring
        ( ℤ-Ring)
        ( R)
        ( subtype-positive-ℤ))
      ( contraction-initial-hom-Ring
        ( R)
        ( comp-hom-Ring ℤ-Ring ring-ℚ R f hom-ring-rational-ℤ))
      ( inverts-positive-integers-rational-hom-Ring R f)

  rational-ring-has-rational-hom-Ring : hom-Ring ring-ℚ R → Rational-Ring l
  rational-ring-has-rational-hom-Ring f =
    ( R , is-rational-has-rational-hom-Ring f)

  inv-positive-integer-has-rational-hom-Ring :
    hom-Ring ring-ℚ R → (k : ℤ⁺) → type-Ring R
  inv-positive-integer-has-rational-hom-Ring =
    inv-positive-integer-Rational-Ring ∘ rational-ring-has-rational-hom-Ring
```

### Any ring homomorphism `ℚ → R` is an extension of the initial ring homomorphism `ℤ → R`

```agda
module _
  {l : Level} (R : Ring l) (f : hom-Ring ring-ℚ R)
  where

  htpy-map-integer-rational-hom-Ring :
    ( map-hom-Ring ring-ℚ R f ∘ rational-ℤ) ~
    ( map-initial-hom-Ring R)
  htpy-map-integer-rational-hom-Ring k =
    inv
      ( htpy-initial-hom-Ring
        ( R)
        ( comp-hom-Ring
          ( ℤ-Ring)
          ( ring-ℚ)
          ( R)
          ( f)
          ( hom-ring-rational-ℤ))
        ( k))

module _
  {l : Level} (R : Rational-Ring l) (f : rational-hom-Rational-Ring R)
  where

  htpy-map-integer-rational-hom-Rational-Ring :
    ( map-rational-hom-Rational-Ring R f ∘ rational-ℤ) ~
    ( map-initial-hom-integer-Rational-Ring R)
  htpy-map-integer-rational-hom-Rational-Ring =
    htpy-map-integer-rational-hom-Ring (ring-Rational-Ring R) f
```

### A ring homomorphism `ℚ → R` preserves reciprocals of positive integers

```agda
module _
  {l : Level} (R : Rational-Ring l) (f : rational-hom-Rational-Ring R)
  where

  htpy-map-reciprocal-rational-hom-Rational-Ring :
    map-rational-hom-Rational-Ring R f ∘ reciprocal-rational-ℤ⁺ ~
    inv-positive-integer-Rational-Ring R
  htpy-map-reciprocal-rational-hom-Rational-Ring k =
    inv
      ( contraction-right-inverse-is-invertible-element-Ring
        ( ring-Rational-Ring R)
        ( map-initial-hom-integer-Rational-Ring R (int-positive-ℤ k))
        ( is-invertible-positive-integer-Rational-Ring R k)
        ( map-rational-hom-Rational-Ring R f (reciprocal-rational-ℤ⁺ k))
        ( is-right-inverse-map-reciprocal))
    where

    is-right-inverse-map-reciprocal :
      is-right-inverse-element-Ring
        ( ring-Rational-Ring R)
        ( map-initial-hom-integer-Rational-Ring R (int-positive-ℤ k))
        ( map-rational-hom-Rational-Ring R f (reciprocal-rational-ℤ⁺ k))
    is-right-inverse-map-reciprocal =
      ( ap
        ( mul-Ring'
          ( ring-Rational-Ring R)
          ( map-hom-Ring
            ( ring-ℚ)
            ( ring-Rational-Ring R)
            ( f)
            ( reciprocal-rational-ℤ⁺ k)))
        ( inv
          ( htpy-map-integer-rational-hom-Rational-Ring
            ( R)
            ( f)
            ( int-positive-ℤ k)))) ∙
      ( inv
        ( preserves-mul-hom-Ring
          ( ring-ℚ)
          ( ring-Rational-Ring R)
          ( f))) ∙
      ( ap
        ( map-hom-Ring ring-ℚ (ring-Rational-Ring R) f)
        ( right-inverse-law-reciprocal-rational-ℤ⁺
          k)) ∙
      ( preserves-one-hom-Ring ring-ℚ (ring-Rational-Ring R) f)

module _
  {l : Level} (R : Ring l) (f : hom-Ring ring-ℚ R)
  where

  htpy-map-reciprocal-rational-hom-Ring :
    map-hom-Ring ring-ℚ R f ∘ reciprocal-rational-ℤ⁺ ~
    inv-positive-integer-has-rational-hom-Ring R f
  htpy-map-reciprocal-rational-hom-Ring =
    htpy-map-reciprocal-rational-hom-Rational-Ring
      ( rational-ring-has-rational-hom-Ring R f)
      ( f)
```

### Any ring homomorphism `ℚ → R` is homotopic to the rational initial ring homomorphism

```agda
module _
  {l : Level} (R : Rational-Ring l) (f : rational-hom-Rational-Ring R)
  where

  htpy-map-initial-hom-Rational-Ring :
    ( map-rational-hom-Rational-Ring R f) ~
    ( map-initial-hom-Rational-Ring R)
  htpy-map-initial-hom-Rational-Ring x =
    ( ap
      ( map-rational-hom-Rational-Ring R f)
      ( inv (eq-mul-numerator-reciprocal-denominator-ℚ x))) ∙
    ( preserves-mul-hom-Ring
      ( ring-ℚ)
      ( ring-Rational-Ring R)
      ( f)) ∙
    ( ap-binary
      ( mul-Ring (ring-Rational-Ring R))
      ( htpy-map-integer-rational-hom-Rational-Ring R f (numerator-ℚ x))
      ( htpy-map-reciprocal-rational-hom-Rational-Ring
        ( R)
        ( f)
        ( positive-denominator-ℚ x)))

module _
  {l : Level} (R : Ring l) (f : hom-Ring ring-ℚ R)
  where

  htpy-map-rational-hom-Ring :
    ( map-hom-Ring ring-ℚ R f) ~
    ( map-initial-hom-Rational-Ring
      ( rational-ring-has-rational-hom-Ring R f))
  htpy-map-rational-hom-Ring =
    htpy-map-initial-hom-Rational-Ring
      ( rational-ring-has-rational-hom-Ring R f)
      ( f)
```

### All ring homomorphisms `ℚ → R` into a rational ring are equal

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  all-htpy-rational-hom-Rational-Ring :
    (f g : rational-hom-Rational-Ring R) →
    map-rational-hom-Rational-Ring R f ~ map-rational-hom-Rational-Ring R g
  all-htpy-rational-hom-Rational-Ring f g x =
    ( htpy-map-initial-hom-Rational-Ring R f x) ∙
    ( inv (htpy-map-initial-hom-Rational-Ring R g x))

  all-eq-rational-hom-Rational-Ring :
    (f g : rational-hom-Rational-Ring R) →
    f ＝ g
  all-eq-rational-hom-Rational-Ring f g =
    eq-htpy-hom-Ring
      ( ring-ℚ)
      ( ring-Rational-Ring R)
      ( f)
      ( g)
      ( all-htpy-rational-hom-Rational-Ring f g)

  is-prop-has-rational-hom-Rational-Ring :
    is-prop (rational-hom-Rational-Ring R)
  is-prop-has-rational-hom-Rational-Ring =
    is-prop-all-elements-equal all-eq-rational-hom-Rational-Ring

  has-rational-hom-prop-Rational-Ring : Prop l
  has-rational-hom-prop-Rational-Ring =
    rational-hom-Rational-Ring R , is-prop-has-rational-hom-Rational-Ring
```

### All ring homomorphisms `ℚ → R` into a ring are equal

```agda
module _
  {l : Level} (R : Ring l)
  where

  all-htpy-rational-hom-Ring : (f g : hom-Ring ring-ℚ R) →
    map-hom-Ring ring-ℚ R f ~ map-hom-Ring ring-ℚ R g
  all-htpy-rational-hom-Ring f =
    all-htpy-rational-hom-Rational-Ring
      ( rational-ring-has-rational-hom-Ring R f)
      ( f)

  all-eq-rational-hom-Ring : (f g : hom-Ring ring-ℚ R) → f ＝ g
  all-eq-rational-hom-Ring f g =
    eq-htpy-hom-Ring ring-ℚ R f g (all-htpy-rational-hom-Ring f g)

  is-prop-has-rational-hom-Ring : is-prop (hom-Ring ring-ℚ R)
  is-prop-has-rational-hom-Ring =
    is-prop-all-elements-equal all-eq-rational-hom-Ring

  has-rational-hom-prop-Ring : Prop l
  has-rational-hom-prop-Ring =
    hom-Ring ring-ℚ R , is-prop-has-rational-hom-Ring
```

## See also

- [rational ring of rational numbers](elementary-number-theory.rational-ring-of-rational-numbers.md)
  where it is proved that `ℚ` is the initial rational ring
