# Ring extension of the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module ring-theory.rational-extensions-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.multiplication-rational-numbers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions
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

For a [ring](ring-theory.rings.md) `R`, the following conditions are equivalent
propositions:

- the images of
  [positive integers](elementary-number-theory.positive-integers.md) by the
  [initial ring homomorphism](elementary-number-theory.ring-of-integers.md)) are
  [invertible elements](ring-theory.invertible-elements-rings.md), i.e., the
  initial ring homomorphism [inverts](ring-theory.localizations-rings.md) the
  subset of positive integers;
- there exist a [ring homomorphism](ring-theory.homomorphisms-rings.md) `ℚ → R`
  from the
  [ring of rational numbers](elementary-number-theory.ring-of-rational-numbers.md)
  to `R`;
- the type of ring homomorphisms `ℚ → R` is
  [contractible](foundation-core.contractible-types.md).

In that case, `R` is called a a
{{#concept "ring extension of ℚ" Agda=Rational-Extension-Ring}}.

The unique ring homomorphism from `ℚ` to a ring extension of `ℚ` is given by
`(p/q : ℚ) ↦ (ι p)(ι q)⁻¹` where `ι : ℤ → R` is the
[initial ring homomorphism](elementary-number-theory.ring-of-integers.md) in
`R`.

As a corollary, `ℚ` is the [localization](ring-theory.localizations-rings.md) of
`ℤ` at `ℤ⁺`: any ring homomorphism `ℤ → R` that inverts the positive integers
extends to a ring homomorphism `ℚ → R`.

## Definitions

### The property of being a rational ring

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-rational-extension-prop-Ring : Prop l
  is-rational-extension-prop-Ring =
    inverts-subset-prop-hom-Ring
      ( ℤ-Ring)
      ( R)
      ( subtype-positive-ℤ)
      ( initial-hom-Ring R)

  is-rational-extension-Ring : UU l
  is-rational-extension-Ring = type-Prop is-rational-extension-prop-Ring

  is-prop-is-rational-extension-Ring : is-prop is-rational-extension-Ring
  is-prop-is-rational-extension-Ring =
    is-prop-type-Prop is-rational-extension-prop-Ring
```

### The type of ring extensions of `ℚ`

```agda
Rational-Extension-Ring : (l : Level) → UU (lsuc l)
Rational-Extension-Ring l = Σ (Ring l) is-rational-extension-Ring

module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  ring-Rational-Extension-Ring : Ring l
  ring-Rational-Extension-Ring = pr1 R

  type-Rational-Extension-Ring : UU l
  type-Rational-Extension-Ring = type-Ring ring-Rational-Extension-Ring

  is-rational-extension-ring-Rational-Extension-Ring :
    is-rational-extension-Ring ring-Rational-Extension-Ring
  is-rational-extension-ring-Rational-Extension-Ring = pr2 R

  mul-Rational-Extension-Ring :
    type-Rational-Extension-Ring →
    type-Rational-Extension-Ring →
    type-Rational-Extension-Ring
  mul-Rational-Extension-Ring = mul-Ring ring-Rational-Extension-Ring

  add-Rational-Extension-Ring :
    type-Rational-Extension-Ring →
    type-Rational-Extension-Ring →
    type-Rational-Extension-Ring
  add-Rational-Extension-Ring = add-Ring ring-Rational-Extension-Ring

  is-invertible-positive-integer-Rational-Extension-Ring :
    (k : ℤ⁺) →
    is-invertible-element-Ring
      ( ring-Rational-Extension-Ring)
      ( map-initial-hom-Ring ring-Rational-Extension-Ring (int-positive-ℤ k))
  is-invertible-positive-integer-Rational-Extension-Ring (k , k>0) =
    is-rational-extension-ring-Rational-Extension-Ring k k>0

  inv-positive-integer-Rational-Extension-Ring :
    ℤ⁺ → type-Rational-Extension-Ring
  inv-positive-integer-Rational-Extension-Ring k =
    inv-is-invertible-element-Ring
      ( ring-Rational-Extension-Ring)
      ( is-invertible-positive-integer-Rational-Extension-Ring k)

  left-inverse-law-positive-integer-Rational-Extension-Ring :
    (k : ℤ⁺) →
    mul-Ring
      ( ring-Rational-Extension-Ring)
      ( inv-positive-integer-Rational-Extension-Ring k)
      ( map-initial-hom-Ring ring-Rational-Extension-Ring (int-positive-ℤ k)) ＝
    one-Ring ring-Rational-Extension-Ring
  left-inverse-law-positive-integer-Rational-Extension-Ring (k , k>0) =
    is-left-inverse-inv-is-invertible-element-Ring
      ( ring-Rational-Extension-Ring)
      ( is-rational-extension-ring-Rational-Extension-Ring k k>0)

  right-inverse-law-positive-integer-Rational-Extension-Ring :
    (k : ℤ⁺) →
    mul-Ring
      ( ring-Rational-Extension-Ring)
      ( map-initial-hom-Ring ring-Rational-Extension-Ring (int-positive-ℤ k))
      ( inv-positive-integer-Rational-Extension-Ring k) ＝
    one-Ring ring-Rational-Extension-Ring
  right-inverse-law-positive-integer-Rational-Extension-Ring (k , k>0) =
    is-right-inverse-inv-is-invertible-element-Ring
      ( ring-Rational-Extension-Ring)
      ( is-rational-extension-ring-Rational-Extension-Ring k k>0)
```

### Homorphisms of rational rings

```agda
module _
  {l1 l2 : Level}
  (A : Rational-Extension-Ring l1)
  (B : Rational-Extension-Ring l2)
  where

  hom-Rational-Extension-Ring : UU (l1 ⊔ l2)
  hom-Rational-Extension-Ring =
    hom-Ring
      ( ring-Rational-Extension-Ring A)
      ( ring-Rational-Extension-Ring B)

  map-hom-Rational-Extension-Ring :
    hom-Rational-Extension-Ring →
    type-Rational-Extension-Ring A →
    type-Rational-Extension-Ring B
  map-hom-Rational-Extension-Ring =
    map-hom-Ring
      ( ring-Rational-Extension-Ring A)
      ( ring-Rational-Extension-Ring B)
```

### The initial ring homomorphism into a rational ring

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  initial-hom-integer-Rational-Extension-Ring :
    hom-Ring ℤ-Ring (ring-Rational-Extension-Ring R)
  initial-hom-integer-Rational-Extension-Ring =
    initial-hom-Ring (ring-Rational-Extension-Ring R)

  map-initial-hom-integer-Rational-Extension-Ring :
    ℤ → type-Rational-Extension-Ring R
  map-initial-hom-integer-Rational-Extension-Ring =
    map-initial-hom-Ring (ring-Rational-Extension-Ring R)
```

### Fractional extension of the initial ring homomorphism into a rational ring

It is defined as `φ : (p/q : fraction-ℤ) ↦ (ι p)(ι q)⁻¹ = (ι q)⁻¹(ι p)` where
`ι : ℤ → R` is the initial ring homomorphism.

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  map-initial-hom-fraction-Rational-Extension-Ring :
    fraction-ℤ → type-Rational-Extension-Ring R
  map-initial-hom-fraction-Rational-Extension-Ring (p , q) =
    mul-Rational-Extension-Ring
      ( R)
      ( map-initial-hom-integer-Rational-Extension-Ring R p)
      ( inv-positive-integer-Rational-Extension-Ring R q)

  map-initial-hom-fraction-Rational-Extension-Ring' :
    fraction-ℤ → type-Rational-Extension-Ring R
  map-initial-hom-fraction-Rational-Extension-Ring' (p , q) =
    mul-Rational-Extension-Ring
      ( R)
      ( inv-positive-integer-Rational-Extension-Ring R q)
      ( map-initial-hom-integer-Rational-Extension-Ring R p)

  htpy-map-initial-hom-fraction-Rational-Extension-Ring' :
    map-initial-hom-fraction-Rational-Extension-Ring ~
    map-initial-hom-fraction-Rational-Extension-Ring'
  htpy-map-initial-hom-fraction-Rational-Extension-Ring' (p , q) =
    ( inv
      ( left-unit-law-mul-Ring
        ( ring-Rational-Extension-Ring R)
        ( mul-Rational-Extension-Ring R pr qr'))) ∙
    ( ap
      ( mul-Ring'
        ( ring-Rational-Extension-Ring R)
        ( mul-Rational-Extension-Ring R pr qr'))
      ( inv (qr'×qr=1))) ∙
    ( associative-mul-Ring
      ( ring-Rational-Extension-Ring R)
      ( qr')
      ( qr)
      ( mul-Rational-Extension-Ring R pr qr')) ∙
    ( ap (mul-Rational-Extension-Ring R qr') (qr×pr×qr'=pr))
    where

    pr qr qr' : type-Rational-Extension-Ring R
    pr = map-initial-hom-Ring (ring-Rational-Extension-Ring R) p
    qr =
      map-initial-hom-Ring (ring-Rational-Extension-Ring R) (int-positive-ℤ q)
    qr' = inv-positive-integer-Rational-Extension-Ring R q

    qr'×qr=1 :
      mul-Ring (ring-Rational-Extension-Ring R) qr' qr ＝
      one-Ring (ring-Rational-Extension-Ring R)
    qr'×qr=1 =
      left-inverse-law-positive-integer-Rational-Extension-Ring R q

    qr×pr×qr'=pr :
      mul-Rational-Extension-Ring R qr (mul-Rational-Extension-Ring R pr qr') ＝
      pr
    qr×pr×qr'=pr =
      ( inv (associative-mul-Ring (ring-Rational-Extension-Ring R) qr pr qr')) ∙
      ( ap
        ( mul-Ring' (ring-Rational-Extension-Ring R) qr')
        ( is-commutative-map-initial-hom-Ring
          ( ring-Rational-Extension-Ring R)
          ( int-positive-ℤ q)
          ( p))) ∙
      ( associative-mul-Ring (ring-Rational-Extension-Ring R) pr qr qr') ∙
      ( ap
        ( mul-Rational-Extension-Ring R pr)
        ( right-inverse-law-positive-integer-Rational-Extension-Ring R q)) ∙
      ( right-unit-law-mul-Ring
        ( ring-Rational-Extension-Ring R)
        ( pr))
```

### Rational extension of the initial ring homomorphism into a rational ring

It is defined as `γ : (p/q : ℚ) ↦ (ι p)(ι q)⁻¹ = (ι q)⁻¹(ι p)` where `ι : ℤ → R`
is the initial ring homomorphism.

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  map-initial-hom-Rational-Extension-Ring : ℚ → type-Rational-Extension-Ring R
  map-initial-hom-Rational-Extension-Ring =
    map-initial-hom-fraction-Rational-Extension-Ring R ∘ fraction-ℚ

  map-initial-hom-Rational-Extension-Ring' : ℚ → type-Rational-Extension-Ring R
  map-initial-hom-Rational-Extension-Ring' =
    map-initial-hom-fraction-Rational-Extension-Ring' R ∘ fraction-ℚ

  htpy-map-initial-hom-Rational-Extension-Ring' :
    map-initial-hom-Rational-Extension-Ring ~
    map-initial-hom-Rational-Extension-Ring'
  htpy-map-initial-hom-Rational-Extension-Ring' x =
    htpy-map-initial-hom-fraction-Rational-Extension-Ring' R (fraction-ℚ x)
```

### The type of rational homomorphisms into a rational ring

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  rational-hom-Rational-Extension-Ring : UU l
  rational-hom-Rational-Extension-Ring =
    hom-Ring ring-ℚ (ring-Rational-Extension-Ring R)

  map-rational-hom-Rational-Extension-Ring :
    rational-hom-Rational-Extension-Ring → ℚ → type-Rational-Extension-Ring R
  map-rational-hom-Rational-Extension-Ring =
    map-hom-Ring ring-ℚ (ring-Rational-Extension-Ring R)
```

## Properties

### A ring is rational if and only if its opposite ring is rational

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-rational-extension-op-is-rational-extension-Ring :
    is-rational-extension-Ring R → is-rational-extension-Ring (op-Ring R)
  is-rational-extension-op-is-rational-extension-Ring H k k>0 =
    ( inv-positive-integer-Rational-Extension-Ring (R , H) (k , k>0)) ,
    ( left-inverse-law-positive-integer-Rational-Extension-Ring
      ( R , H)
      ( k , k>0)) ,
    ( right-inverse-law-positive-integer-Rational-Extension-Ring
      ( R , H)
      ( k , k>0))

  is-rational-extension-is-rational-extension-op-Ring :
    is-rational-extension-Ring (op-Ring R) → is-rational-extension-Ring R
  is-rational-extension-is-rational-extension-op-Ring H k k>0 =
    ( inv-positive-integer-Rational-Extension-Ring (op-Ring R , H) (k , k>0)) ,
    ( left-inverse-law-positive-integer-Rational-Extension-Ring
      ( op-Ring R , H)
      ( k , k>0)) ,
    ( right-inverse-law-positive-integer-Rational-Extension-Ring
      ( op-Ring R , H)
      ( k , k>0))

module _
  {l : Level}
  where

  op-Rational-Extension-Ring :
    Rational-Extension-Ring l → Rational-Extension-Ring l
  op-Rational-Extension-Ring R =
    ( op-Ring (ring-Rational-Extension-Ring R)) ,
    ( is-rational-extension-op-is-rational-extension-Ring
      ( ring-Rational-Extension-Ring R)
      ( is-rational-extension-ring-Rational-Extension-Ring R))
```

### The product of rational rings is rational

```agda
module _
  {l1 l2 : Level} (I : UU l1) (R : I → Rational-Extension-Ring l2)
  where

  is-rational-extension-ring-Π-Rational-Extension-Ring :
    is-rational-extension-Ring (Π-Ring I (ring-Rational-Extension-Ring ∘ R))
  is-rational-extension-ring-Π-Rational-Extension-Ring k k>0 =
    ( λ i → inv-positive-integer-Rational-Extension-Ring (R i) (k , k>0)) ,
    ( eq-htpy
      ( λ i →
        inv-tr
          ( λ h →
            mul-Rational-Extension-Ring
              ( R i)
              ( map-hom-Ring
                ( ℤ-Ring)
                ( Π-Ring I (ring-Rational-Extension-Ring ∘ R))
                ( h)
                ( k)
                ( i))
              ( inv-positive-integer-Rational-Extension-Ring (R i) (k , k>0)) ＝
            one-Ring (ring-Rational-Extension-Ring (R i)))
          ( eq-initial-hom-Π-Ring I (ring-Rational-Extension-Ring ∘ R))
          ( right-inverse-law-positive-integer-Rational-Extension-Ring
            ( R i)
            ( k , k>0)))) ,
    ( eq-htpy
      ( λ i →
        inv-tr
          ( λ h →
            mul-Rational-Extension-Ring
              ( R i)
              ( inv-positive-integer-Rational-Extension-Ring (R i) (k , k>0))
              ( map-hom-Ring
                ( ℤ-Ring)
                ( Π-Ring I (ring-Rational-Extension-Ring ∘ R))
                ( h)
                ( k)
                ( i)) ＝
            one-Ring (ring-Rational-Extension-Ring (R i)))
          ( eq-initial-hom-Π-Ring I (ring-Rational-Extension-Ring ∘ R))
          ( left-inverse-law-positive-integer-Rational-Extension-Ring
            ( R i)
            ( k , k>0))))

  Π-Rational-Extension-Ring : Rational-Extension-Ring (l1 ⊔ l2)
  Π-Rational-Extension-Ring =
    ( Π-Ring I (ring-Rational-Extension-Ring ∘ R)) ,
    ( is-rational-extension-ring-Π-Rational-Extension-Ring)
```

### The inverse of the image of one in a rational ring is one

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  eq-one-inv-positive-one-Rational-Extension-Ring :
    one-Ring (ring-Rational-Extension-Ring R) ＝
    inv-positive-integer-Rational-Extension-Ring R one-ℤ⁺
  eq-one-inv-positive-one-Rational-Extension-Ring =
    contraction-right-inverse-is-invertible-element-Ring
      ( ring-Rational-Extension-Ring R)
      ( one-Ring (ring-Rational-Extension-Ring R))
      ( is-invertible-element-one-Ring (ring-Rational-Extension-Ring R))
      ( inv-positive-integer-Rational-Extension-Ring R one-ℤ⁺)
      ( ( ap
          ( mul-Ring'
            ( ring-Rational-Extension-Ring R)
            ( inv-positive-integer-Rational-Extension-Ring R one-ℤ⁺))
          ( inv
            ( preserves-one-initial-hom-Ring
              ( ring-Rational-Extension-Ring R)))) ∙
        ( right-inverse-law-positive-integer-Rational-Extension-Ring R one-ℤ⁺))
```

### The inverse of a product of positive integers in a rational ring is the product of their inverses

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  eq-mul-inv-positive-integer-Rational-Extension-Ring :
    (p q : ℤ⁺) →
    inv-positive-integer-Rational-Extension-Ring R (mul-positive-ℤ p q) ＝
    mul-Rational-Extension-Ring
      ( R)
      ( inv-positive-integer-Rational-Extension-Ring R p)
      ( inv-positive-integer-Rational-Extension-Ring R q)
  eq-mul-inv-positive-integer-Rational-Extension-Ring p q =
    contraction-right-inverse-is-invertible-element-Ring
      ( ring-Rational-Extension-Ring R)
      ( map-initial-hom-integer-Rational-Extension-Ring
        ( R)
        ( int-positive-ℤ (mul-positive-ℤ p q)))
      ( is-invertible-positive-integer-Rational-Extension-Ring
        ( R)
        ( mul-positive-ℤ p q))
      ( mul-Rational-Extension-Ring
        ( R)
        ( inv-positive-integer-Rational-Extension-Ring R p)
        ( inv-positive-integer-Rational-Extension-Ring R q))
      ( is-right-inverse-mul-inv-positive-integer-Rational-Extension-Ring)
    where

    lemma-map-mul :
      ( map-initial-hom-integer-Rational-Extension-Ring
        ( R)
        ( int-positive-ℤ (mul-positive-ℤ p q))) ＝
      mul-Rational-Extension-Ring
        ( R)
        ( map-initial-hom-integer-Rational-Extension-Ring R (int-positive-ℤ p))
        ( map-initial-hom-integer-Rational-Extension-Ring R (int-positive-ℤ q))
    lemma-map-mul =
      preserves-mul-initial-hom-Ring
        ( ring-Rational-Extension-Ring R)
        ( int-positive-ℤ p)
        ( int-positive-ℤ q)

    is-right-inverse-mul-inv-positive-integer-Rational-Extension-Ring :
      mul-Rational-Extension-Ring
        ( R)
        ( map-initial-hom-integer-Rational-Extension-Ring
          ( R)
          ( int-positive-ℤ (mul-positive-ℤ p q)))
        ( mul-Rational-Extension-Ring
          ( R)
          ( inv-positive-integer-Rational-Extension-Ring R p)
          ( inv-positive-integer-Rational-Extension-Ring R q)) ＝
      one-Ring (ring-Rational-Extension-Ring R)
    is-right-inverse-mul-inv-positive-integer-Rational-Extension-Ring =
      ( inv
        ( associative-mul-Ring
          ( ring-Rational-Extension-Ring R)
          ( map-initial-hom-integer-Rational-Extension-Ring
            ( R)
            ( int-positive-ℤ (mul-positive-ℤ p q)))
          ( inv-positive-integer-Rational-Extension-Ring R p)
          ( inv-positive-integer-Rational-Extension-Ring R q))) ∙
      ( ap
        ( mul-Ring'
          ( ring-Rational-Extension-Ring R)
          ( inv-positive-integer-Rational-Extension-Ring R q))
        ( ( htpy-map-initial-hom-fraction-Rational-Extension-Ring'
            ( R)
            ( int-positive-ℤ (mul-positive-ℤ p q) , p)) ∙
          ( ap
            ( mul-Rational-Extension-Ring
              ( R)
              ( inv-positive-integer-Rational-Extension-Ring R p))
            ( lemma-map-mul)) ∙
          ( inv
            ( associative-mul-Ring
              ( ring-Rational-Extension-Ring R)
              ( inv-positive-integer-Rational-Extension-Ring R p)
              ( map-initial-hom-integer-Rational-Extension-Ring
                ( R)
                ( int-positive-ℤ p))
              ( map-initial-hom-integer-Rational-Extension-Ring
                ( R)
                ( int-positive-ℤ q)))) ∙
            ( ap
              ( mul-Ring'
                ( ring-Rational-Extension-Ring R)
                ( map-initial-hom-integer-Rational-Extension-Ring
                  ( R)
                  ( int-positive-ℤ q)))
              ( left-inverse-law-positive-integer-Rational-Extension-Ring
                ( R)
                ( p))) ∙
            ( left-unit-law-mul-Ring
              ( ring-Rational-Extension-Ring R)
              ( map-initial-hom-integer-Rational-Extension-Ring
                ( R)
                ( int-positive-ℤ q))))) ∙
      ( right-inverse-law-positive-integer-Rational-Extension-Ring R q)
```

### A ring `R` that admits a ring homomorphism `ℚ → R` is rational

```agda
module _
  {l : Level} (R : Ring l)
  where

  is-rational-extension-has-rational-hom-Ring :
    hom-Ring ring-ℚ R → is-rational-extension-Ring R
  is-rational-extension-has-rational-hom-Ring f =
    inv-tr
      ( inverts-subset-hom-Ring
        ( ℤ-Ring)
        ( R)
        ( subtype-positive-ℤ))
      ( contraction-initial-hom-Ring
        ( R)
        ( comp-hom-Ring ℤ-Ring ring-ℚ R f hom-ring-rational-ℤ))
      ( inverts-positive-integers-rational-hom-Ring R f)

  rational-ring-has-rational-hom-Ring :
    hom-Ring ring-ℚ R → Rational-Extension-Ring l
  rational-ring-has-rational-hom-Ring f =
    ( R , is-rational-extension-has-rational-hom-Ring f)

  inv-positive-integer-has-rational-hom-Ring :
    hom-Ring ring-ℚ R → (k : ℤ⁺) → type-Ring R
  inv-positive-integer-has-rational-hom-Ring =
    inv-positive-integer-Rational-Extension-Ring ∘
    rational-ring-has-rational-hom-Ring
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
  {l : Level} (R : Rational-Extension-Ring l)
  (f : rational-hom-Rational-Extension-Ring R)
  where

  htpy-map-integer-rational-hom-Rational-Extension-Ring :
    ( map-rational-hom-Rational-Extension-Ring R f ∘ rational-ℤ) ~
    ( map-initial-hom-integer-Rational-Extension-Ring R)
  htpy-map-integer-rational-hom-Rational-Extension-Ring =
    htpy-map-integer-rational-hom-Ring (ring-Rational-Extension-Ring R) f
```

### A ring homomorphism `ℚ → R` preserves reciprocals of positive integers

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  (f : rational-hom-Rational-Extension-Ring R)
  where

  htpy-map-reciprocal-rational-hom-Rational-Extension-Ring :
    map-rational-hom-Rational-Extension-Ring R f ∘ reciprocal-rational-ℤ⁺ ~
    inv-positive-integer-Rational-Extension-Ring R
  htpy-map-reciprocal-rational-hom-Rational-Extension-Ring k =
    inv
      ( contraction-right-inverse-is-invertible-element-Ring
        ( ring-Rational-Extension-Ring R)
        ( map-initial-hom-integer-Rational-Extension-Ring R (int-positive-ℤ k))
        ( is-invertible-positive-integer-Rational-Extension-Ring R k)
        ( map-rational-hom-Rational-Extension-Ring
          ( R)
          ( f)
          ( reciprocal-rational-ℤ⁺ k))
        ( is-right-inverse-map-reciprocal))
    where

    is-right-inverse-map-reciprocal :
      is-right-inverse-element-Ring
        ( ring-Rational-Extension-Ring R)
        ( map-initial-hom-integer-Rational-Extension-Ring R (int-positive-ℤ k))
        ( map-rational-hom-Rational-Extension-Ring
          ( R)
          ( f)
          ( reciprocal-rational-ℤ⁺ k))
    is-right-inverse-map-reciprocal =
      ( ap
        ( mul-Ring'
          ( ring-Rational-Extension-Ring R)
          ( map-hom-Ring
            ( ring-ℚ)
            ( ring-Rational-Extension-Ring R)
            ( f)
            ( reciprocal-rational-ℤ⁺ k)))
        ( inv
          ( htpy-map-integer-rational-hom-Rational-Extension-Ring
            ( R)
            ( f)
            ( int-positive-ℤ k)))) ∙
      ( inv
        ( preserves-mul-hom-Ring
          ( ring-ℚ)
          ( ring-Rational-Extension-Ring R)
          ( f))) ∙
      ( ap
        ( map-hom-Ring ring-ℚ (ring-Rational-Extension-Ring R) f)
        ( right-inverse-law-reciprocal-rational-ℤ⁺
          k)) ∙
      ( preserves-one-hom-Ring ring-ℚ (ring-Rational-Extension-Ring R) f)

module _
  {l : Level} (R : Ring l) (f : hom-Ring ring-ℚ R)
  where

  htpy-map-reciprocal-rational-hom-Ring :
    map-hom-Ring ring-ℚ R f ∘ reciprocal-rational-ℤ⁺ ~
    inv-positive-integer-has-rational-hom-Ring R f
  htpy-map-reciprocal-rational-hom-Ring =
    htpy-map-reciprocal-rational-hom-Rational-Extension-Ring
      ( rational-ring-has-rational-hom-Ring R f)
      ( f)
```

### Any ring homomorphism `ℚ → R` is homotopic to the rational initial ring homomorphism

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  (f : rational-hom-Rational-Extension-Ring R)
  where

  htpy-map-initial-hom-Rational-Extension-Ring :
    ( map-rational-hom-Rational-Extension-Ring R f) ~
    ( map-initial-hom-Rational-Extension-Ring R)
  htpy-map-initial-hom-Rational-Extension-Ring x =
    ( ap
      ( map-rational-hom-Rational-Extension-Ring R f)
      ( inv (eq-mul-numerator-reciprocal-denominator-ℚ x))) ∙
    ( preserves-mul-hom-Ring
      ( ring-ℚ)
      ( ring-Rational-Extension-Ring R)
      ( f)) ∙
    ( ap-binary
      ( mul-Ring (ring-Rational-Extension-Ring R))
      ( htpy-map-integer-rational-hom-Rational-Extension-Ring
        ( R)
        ( f)
        ( numerator-ℚ x))
      ( htpy-map-reciprocal-rational-hom-Rational-Extension-Ring
        ( R)
        ( f)
        ( positive-denominator-ℚ x)))

module _
  {l : Level} (R : Ring l) (f : hom-Ring ring-ℚ R)
  where

  htpy-map-rational-hom-Ring :
    ( map-hom-Ring ring-ℚ R f) ~
    ( map-initial-hom-Rational-Extension-Ring
      ( rational-ring-has-rational-hom-Ring R f))
  htpy-map-rational-hom-Ring =
    htpy-map-initial-hom-Rational-Extension-Ring
      ( rational-ring-has-rational-hom-Ring R f)
      ( f)
```

### All ring homomorphisms `ℚ → R` into a rational ring are equal

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  all-htpy-rational-hom-Rational-Extension-Ring :
    (f g : rational-hom-Rational-Extension-Ring R) →
    map-rational-hom-Rational-Extension-Ring R f ~
    map-rational-hom-Rational-Extension-Ring R g
  all-htpy-rational-hom-Rational-Extension-Ring f g x =
    ( htpy-map-initial-hom-Rational-Extension-Ring R f x) ∙
    ( inv (htpy-map-initial-hom-Rational-Extension-Ring R g x))

  all-eq-rational-hom-Rational-Extension-Ring :
    (f g : rational-hom-Rational-Extension-Ring R) →
    f ＝ g
  all-eq-rational-hom-Rational-Extension-Ring f g =
    eq-htpy-hom-Ring
      ( ring-ℚ)
      ( ring-Rational-Extension-Ring R)
      ( f)
      ( g)
      ( all-htpy-rational-hom-Rational-Extension-Ring f g)

  is-prop-has-rational-hom-Rational-Extension-Ring :
    is-prop (rational-hom-Rational-Extension-Ring R)
  is-prop-has-rational-hom-Rational-Extension-Ring =
    is-prop-all-elements-equal all-eq-rational-hom-Rational-Extension-Ring

  has-rational-hom-prop-Rational-Extension-Ring : Prop l
  has-rational-hom-prop-Rational-Extension-Ring =
    ( rational-hom-Rational-Extension-Ring R ,
      is-prop-has-rational-hom-Rational-Extension-Ring)
```

### All ring homomorphisms `ℚ → R` into a ring are equal

```agda
module _
  {l : Level} (R : Ring l)
  where

  all-htpy-rational-hom-Ring : (f g : hom-Ring ring-ℚ R) →
    map-hom-Ring ring-ℚ R f ~ map-hom-Ring ring-ℚ R g
  all-htpy-rational-hom-Ring f =
    all-htpy-rational-hom-Rational-Extension-Ring
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

### `ℚ` is a rational extension of itself

```agda
rational-extension-ring-ℚ : Rational-Extension-Ring lzero
rational-extension-ring-ℚ =
  ( ring-ℚ) ,
  ( inv-tr
    ( inverts-subset-hom-Ring
      ( ℤ-Ring)
      ( ring-ℚ)
      ( subtype-positive-ℤ))
      ( eq-initial-hom-ring-rational-ℤ)
      ( inverts-positive-integers-rational-ℤ))
```

### The fractional initial map into a ring extension of `ℚ` extends the initial ring homomorphism

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  htpy-map-integer-fraction-map-initial-Rational-Extension-Ring :
    map-initial-hom-fraction-Rational-Extension-Ring R ∘ in-fraction-ℤ ~
    map-initial-hom-integer-Rational-Extension-Ring R
  htpy-map-integer-fraction-map-initial-Rational-Extension-Ring k =
    ( ap
      ( mul-Rational-Extension-Ring R
        ( map-initial-hom-integer-Rational-Extension-Ring R k))
      ( inv (eq-one-inv-positive-one-Rational-Extension-Ring R))) ∙
    ( right-unit-law-mul-Ring
      ( ring-Rational-Extension-Ring R)
      ( map-initial-hom-integer-Rational-Extension-Ring R k))
```

### The fractional initial map maps similar fractions to identical elements

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  abstract
    eq-map-sim-fraction-map-initial-Rational-Extension-Ring :
      {x y : fraction-ℤ} →
      sim-fraction-ℤ x y →
      map-initial-hom-fraction-Rational-Extension-Ring R x ＝
      map-initial-hom-fraction-Rational-Extension-Ring R y
    eq-map-sim-fraction-map-initial-Rational-Extension-Ring
      {x@(nx , dx)} {y@(ny , dy)} x~y =
      (inv lemma-x) ∙ lemma-y
      where
        _*R_ :
          type-Rational-Extension-Ring R →
          type-Rational-Extension-Ring R →
          type-Rational-Extension-Ring R
        _*R_ = mul-Rational-Extension-Ring R

        rnx rdx rdx' rny rdy rdy' rz : type-Rational-Extension-Ring R

        rnx = map-initial-hom-integer-Rational-Extension-Ring R nx
        rdx =
          map-initial-hom-integer-Rational-Extension-Ring
            ( R)
            ( int-positive-ℤ dx)
        rdx' = inv-positive-integer-Rational-Extension-Ring R dx

        rny = map-initial-hom-integer-Rational-Extension-Ring R ny
        rdy =
          map-initial-hom-integer-Rational-Extension-Ring
            ( R)
            ( int-positive-ℤ dy)
        rdy' = inv-positive-integer-Rational-Extension-Ring R dy

        rz = (rnx *R rdy) *R (rdx' *R rdy')

        commutative-rdxy : (rdx' *R rdy') ＝ (rdy' *R rdx')
        commutative-rdxy =
          ( inv (eq-mul-inv-positive-integer-Rational-Extension-Ring R dx dy)) ∙
          ( ap
            ( inv-positive-integer-Rational-Extension-Ring R)
            ( eq-type-subtype
              ( subtype-positive-ℤ)
              ( commutative-mul-ℤ (int-positive-ℤ dx) (int-positive-ℤ dy)))) ∙
          ( eq-mul-inv-positive-integer-Rational-Extension-Ring R dy dx)

        lemma-rnd : (rnx *R rdy) ＝ (rny *R rdx)
        lemma-rnd =
          ( inv
            ( preserves-mul-initial-hom-Ring
              ( ring-Rational-Extension-Ring R)
              ( nx)
              ( int-positive-ℤ dy))) ∙
          ( ap
            ( map-initial-hom-Ring (ring-Rational-Extension-Ring R))
            ( x~y)) ∙
          ( preserves-mul-initial-hom-Ring
            ( ring-Rational-Extension-Ring R)
            ( ny)
            ( int-positive-ℤ dx))

        lemma-x :
          rz ＝ map-initial-hom-fraction-Rational-Extension-Ring R x
        lemma-x =
          equational-reasoning
            ( rnx *R rdy) *R (rdx' *R rdy')
            ＝ ( rnx *R rdy) *R (rdy' *R rdx')
              by
                ap
                  ( mul-Rational-Extension-Ring R (rnx *R rdy))
                  ( commutative-rdxy)
            ＝ ( (rnx *R rdy) *R rdy') *R rdx'
              by
                inv
                  ( associative-mul-Ring
                    ( ring-Rational-Extension-Ring R)
                    ( rnx *R rdy)
                    ( rdy')
                    ( rdx'))
            ＝ ( rnx *R (rdy *R rdy')) *R rdx'
              by
                ap
                  ( mul-Ring' (ring-Rational-Extension-Ring R) rdx')
                  ( associative-mul-Ring
                    ( ring-Rational-Extension-Ring R)
                    ( rnx)
                    ( rdy)
                    ( rdy'))
            ＝ ( rnx *R (one-Ring (ring-Rational-Extension-Ring R))) *R rdx'
              by
                ap
                  ( λ z → (rnx *R z) *R rdx')
                  ( right-inverse-law-positive-integer-Rational-Extension-Ring
                    ( R)
                    ( dy))
            ＝ map-initial-hom-fraction-Rational-Extension-Ring R x
              by
                ap
                  ( mul-Ring' (ring-Rational-Extension-Ring R) rdx')
                  ( right-unit-law-mul-Ring
                    ( ring-Rational-Extension-Ring R)
                    ( rnx))

        lemma-y :
          rz ＝ map-initial-hom-fraction-Rational-Extension-Ring R y
        lemma-y =
          equational-reasoning
            ( rnx *R rdy) *R (rdx' *R rdy')
            ＝ ( rny *R rdx) *R (rdx' *R rdy')
              by
                ap
                  ( mul-Ring' (ring-Rational-Extension-Ring R) (rdx' *R rdy'))
                  ( lemma-rnd)
            ＝ ( (rny *R rdx) *R rdx') *R rdy'
              by
                inv
                  ( associative-mul-Ring
                    ( ring-Rational-Extension-Ring R)
                    ( rny *R rdx)
                    ( rdx')
                    ( rdy'))
            ＝ ( rny *R (rdx *R rdx')) *R rdy'
              by
                ap
                  ( mul-Ring' (ring-Rational-Extension-Ring R) (rdy'))
                  ( associative-mul-Ring
                    ( ring-Rational-Extension-Ring R)
                    ( rny)
                    ( rdx)
                    ( rdx'))
            ＝ ( rny *R (one-Ring (ring-Rational-Extension-Ring R))) *R rdy'
              by
                ap
                  ( λ z → (rny *R z) *R rdy')
                  ( right-inverse-law-positive-integer-Rational-Extension-Ring
                    ( R)
                    ( dx))
            ＝ map-initial-hom-fraction-Rational-Extension-Ring R y
              by
                ap
                  ( mul-Ring' (ring-Rational-Extension-Ring R) rdy')
                  ( right-unit-law-mul-Ring
                    ( ring-Rational-Extension-Ring R)
                    ( rny))
```

### The fractional initial map preserves addition

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  abstract
    preserves-add-map-initial-hom-fraction-Rational-Extension-Ring :
      {x y : fraction-ℤ} →
      map-initial-hom-fraction-Rational-Extension-Ring
        ( R)
        ( add-fraction-ℤ x y) ＝
      add-Rational-Extension-Ring
        ( R)
        ( map-initial-hom-fraction-Rational-Extension-Ring R x)
        ( map-initial-hom-fraction-Rational-Extension-Ring R y)
    preserves-add-map-initial-hom-fraction-Rational-Extension-Ring
      {x@(nx , dx)} {y@(ny , dy)} =
      ( ap
        ( mul-Ring'
          ( ring-Rational-Extension-Ring R)
          ( inv-positive-integer-Rational-Extension-Ring
            ( R)
            ( mul-positive-ℤ dx dy)))
        ( lemma-add-numerator)) ∙
      ( right-distributive-mul-add-Ring
        ( ring-Rational-Extension-Ring R)
        ( map-initial-hom-integer-Rational-Extension-Ring
          ( R)
          ( int-mul-positive-ℤ' dy nx))
        ( map-initial-hom-integer-Rational-Extension-Ring
          ( R)
          ( int-mul-positive-ℤ' dx ny))
        ( inv-positive-integer-Rational-Extension-Ring
          ( R)
          ( mul-positive-ℤ dx dy))) ∙
      ( ap-binary
        ( add-Rational-Extension-Ring R)
        ( lemma-x)
        ( lemma-y))
      where

      _*R_ :
        type-Rational-Extension-Ring R →
        type-Rational-Extension-Ring R →
        type-Rational-Extension-Ring R
      _*R_ = mul-Rational-Extension-Ring R

      rnx rdx rdx' rny rdy rdy' : type-Rational-Extension-Ring R
      rnx = map-initial-hom-integer-Rational-Extension-Ring R nx
      rdx =
        map-initial-hom-integer-Rational-Extension-Ring R (int-positive-ℤ dx)
      rdx' = inv-positive-integer-Rational-Extension-Ring R dx
      rny = map-initial-hom-integer-Rational-Extension-Ring R ny
      rdy =
        map-initial-hom-integer-Rational-Extension-Ring R (int-positive-ℤ dy)
      rdy' = inv-positive-integer-Rational-Extension-Ring R dy

      lemma-add-numerator :
        map-initial-hom-integer-Rational-Extension-Ring
          ( R)
          ( ( int-mul-positive-ℤ' dy nx) +ℤ (int-mul-positive-ℤ' dx ny)) ＝
        add-Rational-Extension-Ring
          ( R)
          ( map-initial-hom-integer-Rational-Extension-Ring
            ( R)
            ( int-mul-positive-ℤ' dy nx))
          ( map-initial-hom-integer-Rational-Extension-Ring
            ( R)
            ( int-mul-positive-ℤ' dx ny))
      lemma-add-numerator =
        preserves-add-initial-hom-Ring
          ( ring-Rational-Extension-Ring R)
          ( int-mul-positive-ℤ' dy nx)
          ( int-mul-positive-ℤ' dx ny)

      lemma-add-denominator :
        inv-positive-integer-Rational-Extension-Ring
          ( R)
          ( mul-positive-ℤ dx dy) ＝
        mul-Rational-Extension-Ring
          ( R)
          ( inv-positive-integer-Rational-Extension-Ring R dx)
          ( inv-positive-integer-Rational-Extension-Ring R dy)
      lemma-add-denominator =
        eq-mul-inv-positive-integer-Rational-Extension-Ring R dx dy

      lemma-nxdy :
        map-initial-hom-integer-Rational-Extension-Ring
          ( R)
          ( int-mul-positive-ℤ' dy nx) ＝
        mul-Rational-Extension-Ring
          ( R)
          ( map-initial-hom-integer-Rational-Extension-Ring R nx)
          ( map-initial-hom-integer-Rational-Extension-Ring
            ( R)
            ( int-positive-ℤ dy))
      lemma-nxdy =
        preserves-mul-initial-hom-Ring
          ( ring-Rational-Extension-Ring R)
          ( nx)
          ( int-positive-ℤ dy)

      lemma-nydx :
        map-initial-hom-integer-Rational-Extension-Ring
          ( R)
          ( int-mul-positive-ℤ' dx ny) ＝
        mul-Rational-Extension-Ring
          ( R)
          ( map-initial-hom-integer-Rational-Extension-Ring R ny)
          ( map-initial-hom-integer-Rational-Extension-Ring
            ( R)
            ( int-positive-ℤ dx))
      lemma-nydx =
        preserves-mul-initial-hom-Ring
          ( ring-Rational-Extension-Ring R)
          ( ny)
          ( int-positive-ℤ dx)

      lemma-add-denominator' :
        inv-positive-integer-Rational-Extension-Ring
          ( R)
          ( mul-positive-ℤ dx dy) ＝
        mul-Rational-Extension-Ring
          ( R)
          ( inv-positive-integer-Rational-Extension-Ring R dy)
          ( inv-positive-integer-Rational-Extension-Ring R dx)
      lemma-add-denominator' =
        ( ap
          ( inv-positive-integer-Rational-Extension-Ring R)
          ( eq-type-subtype
            ( subtype-positive-ℤ)
            ( commutative-mul-ℤ (int-positive-ℤ dx) (int-positive-ℤ dy)))) ∙
        ( eq-mul-inv-positive-integer-Rational-Extension-Ring R dy dx)

      lemma-x :
        map-initial-hom-fraction-Rational-Extension-Ring
          ( R)
          ( int-mul-positive-ℤ' dy nx , mul-positive-ℤ dx dy) ＝
        map-initial-hom-fraction-Rational-Extension-Ring R x
      lemma-x =
        ( ap
          ( mul-Rational-Extension-Ring
            ( R)
            ( map-initial-hom-integer-Rational-Extension-Ring
              ( R)
              ( int-mul-positive-ℤ' dy nx)))
          ( ( lemma-add-denominator'))) ∙
        ( ap
          ( mul-Ring'
            ( ring-Rational-Extension-Ring R)
            ( mul-Rational-Extension-Ring R rdy' rdx'))
          ( lemma-nxdy)) ∙
        ( inv
          ( associative-mul-Ring
            ( ring-Rational-Extension-Ring R)
            ( rnx *R rdy)
            ( rdy')
            ( rdx'))) ∙
        ( ap
          ( mul-Ring'
            ( ring-Rational-Extension-Ring R)
            ( rdx'))
          ( associative-mul-Ring
            ( ring-Rational-Extension-Ring R)
            ( rnx)
            ( rdy)
            ( rdy'))) ∙
        ( ap
          ( λ z → (rnx *R z) *R rdx')
          ( right-inverse-law-positive-integer-Rational-Extension-Ring R dy)) ∙
        ( ap
          ( mul-Ring' (ring-Rational-Extension-Ring R) (rdx'))
          ( right-unit-law-mul-Ring (ring-Rational-Extension-Ring R) rnx))

      lemma-y :
        map-initial-hom-fraction-Rational-Extension-Ring
          ( R)
          ( int-mul-positive-ℤ' dx ny , mul-positive-ℤ dx dy) ＝
        map-initial-hom-fraction-Rational-Extension-Ring R y
      lemma-y =
        ( ap
          ( mul-Rational-Extension-Ring
            ( R)
            ( map-initial-hom-integer-Rational-Extension-Ring
              ( R)
              ( int-mul-positive-ℤ' dx ny)))
          ( ( lemma-add-denominator))) ∙
        ( ap
          ( mul-Ring'
            ( ring-Rational-Extension-Ring R)
            ( mul-Rational-Extension-Ring R rdx' rdy'))
          ( lemma-nydx)) ∙
        ( inv
          ( associative-mul-Ring
            ( ring-Rational-Extension-Ring R)
            ( rny *R rdx)
            ( rdx')
            ( rdy'))) ∙
        ( ap
          ( mul-Ring'
            ( ring-Rational-Extension-Ring R)
            ( rdy'))
          ( associative-mul-Ring
            ( ring-Rational-Extension-Ring R)
            ( rny)
            ( rdx)
            ( rdx'))) ∙
        ( ap
          ( λ z → (rny *R z) *R rdy')
          ( right-inverse-law-positive-integer-Rational-Extension-Ring R dx)) ∙
        ( ap
          ( mul-Ring' (ring-Rational-Extension-Ring R) (rdy'))
          ( right-unit-law-mul-Ring (ring-Rational-Extension-Ring R) rny))
```

### The fractional initial map preserves multiplication

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  abstract
    preserves-mul-map-initial-hom-fraction-Rational-Extension-Ring :
      {x y : fraction-ℤ} →
      map-initial-hom-fraction-Rational-Extension-Ring
        ( R)
        ( mul-fraction-ℤ x y) ＝
      mul-Rational-Extension-Ring
        ( R)
        ( map-initial-hom-fraction-Rational-Extension-Ring R x)
        ( map-initial-hom-fraction-Rational-Extension-Ring R y)
    preserves-mul-map-initial-hom-fraction-Rational-Extension-Ring
      {x@(nx , dx)} {y@(ny , dy)} =
      ( ap
        ( mul-Rational-Extension-Ring
          ( R)
          ( map-initial-hom-integer-Rational-Extension-Ring R (nx *ℤ ny)))
        ( eq-mul-inv-positive-integer-Rational-Extension-Ring R dx dy)) ∙
      ( inv
        ( associative-mul-Ring
          ( ring-Rational-Extension-Ring R)
          ( map-initial-hom-integer-Rational-Extension-Ring R (nx *ℤ ny))
          ( rdx')
          ( rdy'))) ∙
      ( ap
        ( mul-Ring' (ring-Rational-Extension-Ring R) (rdy'))
        ( ( htpy-map-initial-hom-fraction-Rational-Extension-Ring'
            ( R)
            ( (nx *ℤ ny) , dx)) ∙
          ( ap
            ( mul-Ring (ring-Rational-Extension-Ring R) rdx')
            ( preserves-mul-initial-hom-Ring
              ( ring-Rational-Extension-Ring R)
              ( nx)
              ( ny))) ∙
          ( inv
            ( associative-mul-Ring
              ( ring-Rational-Extension-Ring R)
              ( rdx')
              ( rnx)
              ( rny))))) ∙
      ( associative-mul-Ring
        ( ring-Rational-Extension-Ring R)
        ( rdx' *R rnx)
        ( rny)
        ( rdy')) ∙
      ( ap
        ( mul-Ring' (ring-Rational-Extension-Ring R) (rny *R rdy'))
        ( inv
          ( htpy-map-initial-hom-fraction-Rational-Extension-Ring'
            ( R)
            ( x))))
      where

      _*R_ :
        type-Rational-Extension-Ring R →
        type-Rational-Extension-Ring R →
        type-Rational-Extension-Ring R
      _*R_ = mul-Rational-Extension-Ring R

      rnx rdx rdx' rny rdy rdy' : type-Rational-Extension-Ring R
      rnx = map-initial-hom-integer-Rational-Extension-Ring R nx
      rdx =
        map-initial-hom-integer-Rational-Extension-Ring R (int-positive-ℤ dx)
      rdx' = inv-positive-integer-Rational-Extension-Ring R dx
      rny = map-initial-hom-integer-Rational-Extension-Ring R ny
      rdy =
        map-initial-hom-integer-Rational-Extension-Ring R (int-positive-ℤ dy)
      rdy' = inv-positive-integer-Rational-Extension-Ring R dy
```

### The rational initial ring map extends the initial ring homomorphism

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  htpy-integer-map-initial-hom-Rational-Extension-Ring :
    map-initial-hom-Rational-Extension-Ring R ∘ rational-ℤ ~
    map-initial-hom-integer-Rational-Extension-Ring R
  htpy-integer-map-initial-hom-Rational-Extension-Ring k =
    ( ap
      ( mul-Rational-Extension-Ring
        ( R)
        ( map-initial-hom-integer-Rational-Extension-Ring R k))
      ( inv (eq-one-inv-positive-one-Rational-Extension-Ring R))) ∙
    ( right-unit-law-mul-Ring
      ( ring-Rational-Extension-Ring R)
      ( map-initial-hom-integer-Rational-Extension-Ring R k))
```

### The rational initial ring map preserves one

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  preserves-one-initial-hom-Rational-Extension-Ring :
    map-initial-hom-Rational-Extension-Ring R one-ℚ ＝
    one-Ring (ring-Rational-Extension-Ring R)
  preserves-one-initial-hom-Rational-Extension-Ring =
    is-right-inverse-inv-is-invertible-element-Ring
      ( ring-Rational-Extension-Ring R)
      ( is-invertible-positive-integer-Rational-Extension-Ring R one-ℤ⁺)
```

### The rational initial ring map is a ring homomorphism

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  opaque
    unfolding add-ℚ
    unfolding mul-ℚ
    unfolding rational-fraction-ℤ

    preserves-add-initial-hom-Rational-Extension-Ring :
      {x y : ℚ} →
      map-initial-hom-Rational-Extension-Ring R (x +ℚ y) ＝
      add-Ring
        ( ring-Rational-Extension-Ring R)
        ( map-initial-hom-Rational-Extension-Ring R x)
        ( map-initial-hom-Rational-Extension-Ring R y)
    preserves-add-initial-hom-Rational-Extension-Ring {x} {y} =
      equational-reasoning
        map-initial-hom-Rational-Extension-Ring R (x +ℚ y)
        ＝ map-initial-hom-fraction-Rational-Extension-Ring
          ( R)
          ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
          by
            eq-map-sim-fraction-map-initial-Rational-Extension-Ring
              ( R)
              ( symmetric-sim-fraction-ℤ
                ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
                ( reduce-fraction-ℤ
                  ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)))
                ( sim-reduced-fraction-ℤ
                  ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))))
        ＝ add-Ring
          ( ring-Rational-Extension-Ring R)
          ( map-initial-hom-Rational-Extension-Ring R x)
          ( map-initial-hom-Rational-Extension-Ring R y)
          by (preserves-add-map-initial-hom-fraction-Rational-Extension-Ring R)

    preserves-mul-initial-hom-Rational-Extension-Ring :
      {x y : ℚ} →
      map-initial-hom-Rational-Extension-Ring R (x *ℚ y) ＝
      mul-Ring
        ( ring-Rational-Extension-Ring R)
        ( map-initial-hom-Rational-Extension-Ring R x)
        ( map-initial-hom-Rational-Extension-Ring R y)
    preserves-mul-initial-hom-Rational-Extension-Ring {x} {y} =
      equational-reasoning
        map-initial-hom-Rational-Extension-Ring R (x *ℚ y)
        ＝ map-initial-hom-fraction-Rational-Extension-Ring
          ( R)
          ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
          by
            eq-map-sim-fraction-map-initial-Rational-Extension-Ring
              ( R)
              ( symmetric-sim-fraction-ℤ
                ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
                ( reduce-fraction-ℤ
                  ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)))
                ( sim-reduced-fraction-ℤ
                  ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))))
        ＝ mul-Ring
          ( ring-Rational-Extension-Ring R)
          ( map-initial-hom-Rational-Extension-Ring R x)
          ( map-initial-hom-Rational-Extension-Ring R y)
          by (preserves-mul-map-initial-hom-fraction-Rational-Extension-Ring R)

  initial-hom-Rational-Extension-Ring : rational-hom-Rational-Extension-Ring R
  pr1 initial-hom-Rational-Extension-Ring =
    ( map-initial-hom-Rational-Extension-Ring R ,
      preserves-add-initial-hom-Rational-Extension-Ring)
  pr2 initial-hom-Rational-Extension-Ring =
    ( preserves-mul-initial-hom-Rational-Extension-Ring ,
      preserves-one-initial-hom-Rational-Extension-Ring R)
```

### The type of ring homomorphisms from `ℚ` to a ring extension of `ℚ` is contractible

```agda
module _
  {l : Level} (R : Rational-Extension-Ring l)
  where

  is-contr-rational-hom-Rational-Extension-Ring :
    is-contr (rational-hom-Rational-Extension-Ring R)
  is-contr-rational-hom-Rational-Extension-Ring =
    ( initial-hom-Rational-Extension-Ring R) ,
    ( λ g →
      eq-htpy-hom-Ring
        ( ring-ℚ)
        ( ring-Rational-Extension-Ring R)
        ( initial-hom-Rational-Extension-Ring R)
        ( g)
        ( inv ∘ htpy-map-initial-hom-Rational-Extension-Ring R g))

  is-prop-rational-hom-Rational-Extension-Ring :
    is-prop (rational-hom-Rational-Extension-Ring R)
  is-prop-rational-hom-Rational-Extension-Ring =
    is-prop-is-contr is-contr-rational-hom-Rational-Extension-Ring
```

### The ring of rational numbers is the initial ring extension of `ℚ`

```agda
module _
  {l : Level}
  where

  is-initial-rational-ring-ℚ :
    (R : Rational-Extension-Ring l) →
    is-contr (hom-Rational-Extension-Ring rational-extension-ring-ℚ R)
  is-initial-rational-ring-ℚ R =
    is-contr-rational-hom-Rational-Extension-Ring R
```

### A ring `R` is a ring extension of `ℚ` if and only if there exists a ring homomorphism `ℚ → R`

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-rational-hom-is-rational-extension-Ring :
    is-rational-extension-Ring R → hom-Ring ring-ℚ R
  has-rational-hom-is-rational-extension-Ring =
    initial-hom-Rational-Extension-Ring ∘ pair R

  iff-is-rational-extension-has-rational-hom-Ring :
    hom-Ring ring-ℚ R ↔ is-rational-extension-Ring R
  iff-is-rational-extension-has-rational-hom-Ring =
    ( is-rational-extension-has-rational-hom-Ring R ,
      has-rational-hom-is-rational-extension-Ring)
```

### A ring `R` is a ring extension of `ℚ` if and only if the type of ring homomorphisms `ℚ → R` is contractible

```agda
module _
  {l : Level} (R : Ring l)
  where

  iff-is-rational-extension-is-contr-rational-hom-Ring :
    is-contr (hom-Ring ring-ℚ R) ↔ is-rational-extension-Ring R
  iff-is-rational-extension-is-contr-rational-hom-Ring =
    ( is-rational-extension-has-rational-hom-Ring R ∘ center) ,
    ( is-contr-rational-hom-Rational-Extension-Ring ∘ pair R)
```

### The ring of rational numbers is the localization of the ring of integers at `ℤ⁺`

```agda
module _
  {l : Level}
  where

  universal-property-localization-positive-integers-rational-Ring :
    universal-property-localization-subset-Ring
      ( l)
      ( ℤ-Ring)
      ( ring-ℚ)
      ( subtype-positive-ℤ)
      ( initial-hom-Ring ring-ℚ)
      ( is-rational-extension-ring-Rational-Extension-Ring
        rational-extension-ring-ℚ)
  universal-property-localization-positive-integers-rational-Ring T =
    is-equiv-has-converse-is-prop
      ( is-prop-has-rational-hom-Ring T)
      ( is-prop-type-subtype
        ( inverts-subset-prop-hom-Ring ℤ-Ring T subtype-positive-ℤ)
        ( is-prop-is-contr (is-initial-ℤ-Ring T)))
      ( λ (f , H) →
        initial-hom-Rational-Extension-Ring
          ( ( T) ,
            ( inv-tr
              ( inverts-subset-hom-Ring ℤ-Ring T subtype-positive-ℤ)
              ( contraction-initial-hom-Ring T f)
              ( H))))
```
