# Fractional extension of the initial ring homomorphism intp a ring extension of the rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module ring-theory.fractional-extension-initial-hom-ring-extensions-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integer-fractions
open import elementary-number-theory.addition-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.multiplication-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.ring-of-integers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.subtypes
open import foundation.universe-levels

open import ring-theory.homomorphisms-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.ring-extensions-rational-numbers
open import ring-theory.rings
```

</details>

## Idea

The [initial ring homomorphism](elementary-number-theory.ring-of-integers.md)
`ι : ℤ → R` in a
[ring extension of `ℚ`](ring-theory.ring-extensions-rational-numbers.md) extends
to an [additive](elementary-number-theory.addition-integer-fractions.md),
[multiplicative](elementary-number-theory.multiplication-integer-fractions.md)
and similarity-preserving map from
[`fraction-ℤ`](elementary-number-theory.integer-fractions.md) to `R` by:

```text
(p/q : ℚ) ↦ (ι p)(ι q)⁻¹ = (ι q)⁻¹(ι p)
```

## Definitions

### Fractional extension of the initial ring homomorphism into a ring extension of `ℚ`

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

## Properties

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

### The inverse of a product of positive integers in a ring extension of `ℚ` is the product of their inverses

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

## See also

- [`rational-extension-initial-hom-ring-extensions-rational-numbers`](ring-theory.rational-extension-initial-hom-ring-extensions-rational-numbers.md):
  the initial ring homomorphism from `ℚ` into a rational extension of `ℚ`.
