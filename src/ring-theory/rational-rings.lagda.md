# Rational rings

```agda
{-# OPTIONS --lossy-unification #-}

module ring-theory.rational-rings where
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

A {{#concept "rational ring" Agda=Rational-Ring}} is a
[ring](ring-theory.rings.md) where the images of
[positive integers](elementary-number-theory.positive-integers.md) by the
[initial ring homomorphism](elementary-number-theory.ring-of-integers.md)) are
[invertible](ring-theory.invertible-elements-rings.md). The
[ring of rational numbers](elementary-number-theory.ring-of-rational-numbers.md)
is rational; for any ring `R`, if there exists a
[ring homomorphism](ring-theory.homomorphisms-rings.md) `f : ℚ → R`, then `R` is
**rational** and `f` is [homotopic](foundation.homotopies.md) to the extension
of the [initial ring homomorphism](elementary-number-theory.ring-of-integers.md)
`ι : ℤ → R` defined by `γ : (p/q : ℚ) ↦ (ι p)(ι q)⁻¹`. In other words, a ring
`R` is **rational** if and only if `hom-Ring ℚ R` is
[contractible](foundation.contractible-types.md) so `ℚ` is the
[initial](ring-theory.initial-rings.md) rational ring. It follows that `ℚ` is
the [localization](ring-theory.localizations-rings.md) of `ℤ` at
[ℤ⁺](elementary-number-theory.positive-integers.md).

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
```

### The initial ring homomorphism into a rational ring

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  integer-initial-hom-Rational-Ring : hom-Ring ℤ-Ring (ring-Rational-Ring R)
  integer-initial-hom-Rational-Ring =
    initial-hom-Ring (ring-Rational-Ring R)

  map-integer-initial-hom-Rational-Ring : ℤ → type-Rational-Ring R
  map-integer-initial-hom-Rational-Ring =
    map-initial-hom-Ring (ring-Rational-Ring R)
```

### Fractional extension of the initial ring homomorphism into a rational ring

It is defined as `φ : (p/q : fraction-ℤ) ↦ (ι p)(ι q)⁻¹ = (ι q)⁻¹(ι p)` where
`ι : ℤ → R` is the initial ring homomorphism.

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  map-fraction-initial-hom-Rational-Ring : fraction-ℤ → type-Rational-Ring R
  map-fraction-initial-hom-Rational-Ring (p , q) =
    mul-Rational-Ring
      ( R)
      ( map-integer-initial-hom-Rational-Ring R p)
      ( inv-positive-integer-Rational-Ring R q)

  map-fraction-initial-hom-Rational-Ring' : fraction-ℤ → type-Rational-Ring R
  map-fraction-initial-hom-Rational-Ring' (p , q) =
    mul-Rational-Ring
      ( R)
      ( inv-positive-integer-Rational-Ring R q)
      ( map-integer-initial-hom-Rational-Ring R p)

  htpy-map-fraction-initial-hom-Rational-Ring' :
    map-fraction-initial-hom-Rational-Ring ~
    map-fraction-initial-hom-Rational-Ring'
  htpy-map-fraction-initial-hom-Rational-Ring' (p , q) =
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

  map-rational-initial-hom-Rational-Ring : ℚ → type-Rational-Ring R
  map-rational-initial-hom-Rational-Ring =
    map-fraction-initial-hom-Rational-Ring R ∘ fraction-ℚ

  map-rational-initial-hom-Rational-Ring' : ℚ → type-Rational-Ring R
  map-rational-initial-hom-Rational-Ring' =
    map-fraction-initial-hom-Rational-Ring' R ∘ fraction-ℚ

  htpy-map-rational-initial-hom-Rational-Ring' :
    map-rational-initial-hom-Rational-Ring ~
    map-rational-initial-hom-Rational-Ring'
  htpy-map-rational-initial-hom-Rational-Ring' x =
    htpy-map-fraction-initial-hom-Rational-Ring' R (fraction-ℚ x)
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

### `ℚ` is a rational ring

```agda
rational-ring-ℚ : Rational-Ring lzero
rational-ring-ℚ =
  ( ring-ℚ) ,
  ( inv-tr
    ( inverts-subset-hom-Ring
      ( ℤ-Ring)
      ( ring-ℚ)
      ( subtype-positive-ℤ))
      ( eq-initial-hom-ring-rational-ℤ)
      ( inverts-positive-integers-rational-ℤ))
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
      ( map-integer-initial-hom-Rational-Ring
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
      ( map-integer-initial-hom-Rational-Ring
        ( R)
        ( int-positive-ℤ (mul-positive-ℤ p q))) ＝
      mul-Rational-Ring
        ( R)
        ( map-integer-initial-hom-Rational-Ring R (int-positive-ℤ p))
        ( map-integer-initial-hom-Rational-Ring R (int-positive-ℤ q))
    lemma-map-mul =
      preserves-mul-initial-hom-Ring
        ( ring-Rational-Ring R)
        ( int-positive-ℤ p)
        ( int-positive-ℤ q)

    is-right-inverse-mul-inv-positive-integer-Rational-Ring :
      mul-Rational-Ring
        ( R)
        ( map-integer-initial-hom-Rational-Ring
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
          ( map-integer-initial-hom-Rational-Ring
            ( R)
            ( int-positive-ℤ (mul-positive-ℤ p q)))
          ( inv-positive-integer-Rational-Ring R p)
          ( inv-positive-integer-Rational-Ring R q))) ∙
      ( ap
        ( mul-Ring'
          ( ring-Rational-Ring R)
          ( inv-positive-integer-Rational-Ring R q))
        ( ( htpy-map-fraction-initial-hom-Rational-Ring'
            ( R)
            ( int-positive-ℤ (mul-positive-ℤ p q) , p)) ∙
          ( ap
            ( mul-Rational-Ring R (inv-positive-integer-Rational-Ring R p))
            ( lemma-map-mul)) ∙
          ( inv
            ( associative-mul-Ring
              ( ring-Rational-Ring R)
              ( inv-positive-integer-Rational-Ring R p)
              ( map-integer-initial-hom-Rational-Ring R (int-positive-ℤ p))
              ( map-integer-initial-hom-Rational-Ring R (int-positive-ℤ q)))) ∙
            ( ap
              ( mul-Ring'
                ( ring-Rational-Ring R)
                ( map-integer-initial-hom-Rational-Ring R (int-positive-ℤ q)))
              ( left-inverse-law-positive-integer-Rational-Ring R p)) ∙
            ( left-unit-law-mul-Ring
              ( ring-Rational-Ring R)
              ( map-integer-initial-hom-Rational-Ring R (int-positive-ℤ q))))) ∙
      ( right-inverse-law-positive-integer-Rational-Ring R q)
```

### The fractional initial map into a rational ring extends the initial ring homomorphism

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  htpy-map-integer-fraction-map-initial-Rational-Ring :
    map-fraction-initial-hom-Rational-Ring R ∘ in-fraction-ℤ ~
    map-integer-initial-hom-Rational-Ring R
  htpy-map-integer-fraction-map-initial-Rational-Ring k =
    ( ap
      ( mul-Rational-Ring R (map-integer-initial-hom-Rational-Ring R k))
      ( inv (eq-one-inv-positive-one-Rational-Ring R))) ∙
    ( right-unit-law-mul-Ring
      ( ring-Rational-Ring R)
      ( map-integer-initial-hom-Rational-Ring R k))
```

### The fractional initial map maps similar fractions to identical elements

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  eq-map-sim-fraction-map-initial-Rational-Ring :
    (x y : fraction-ℤ) →
    sim-fraction-ℤ x y →
    map-fraction-initial-hom-Rational-Ring R x ＝
    map-fraction-initial-hom-Rational-Ring R y
  eq-map-sim-fraction-map-initial-Rational-Ring x@(nx , dx) y@(ny , dy) x~y =
    (inv lemma-x) ∙ lemma-y
    where
      _*R_ : type-Rational-Ring R → type-Rational-Ring R → type-Rational-Ring R
      _*R_ = mul-Rational-Ring R

      rnx rdx rdx' rny rdy rdy' rz : type-Rational-Ring R

      rnx = map-integer-initial-hom-Rational-Ring R nx
      rdx = map-integer-initial-hom-Rational-Ring R (int-positive-ℤ dx)
      rdx' = inv-positive-integer-Rational-Ring R dx

      rny = map-integer-initial-hom-Rational-Ring R ny
      rdy = map-integer-initial-hom-Rational-Ring R (int-positive-ℤ dy)
      rdy' = inv-positive-integer-Rational-Ring R dy

      rz = (rnx *R rdy) *R (rdx' *R rdy')

      commutative-rdxy : (rdx' *R rdy') ＝ (rdy' *R rdx')
      commutative-rdxy =
        ( inv (eq-mul-inv-positive-integer-Rational-Ring R dx dy)) ∙
        ( ap
          ( inv-positive-integer-Rational-Ring R)
          ( eq-type-subtype
            ( subtype-positive-ℤ)
            ( commutative-mul-ℤ (int-positive-ℤ dx) (int-positive-ℤ dy)))) ∙
        ( eq-mul-inv-positive-integer-Rational-Ring R dy dx)

      lemma-rnd : (rnx *R rdy) ＝ (rny *R rdx)
      lemma-rnd =
        ( inv
          ( preserves-mul-initial-hom-Ring
            ( ring-Rational-Ring R)
            ( nx)
            ( int-positive-ℤ dy))) ∙
        ( ap
          ( map-initial-hom-Ring (ring-Rational-Ring R))
          ( x~y)) ∙
        ( preserves-mul-initial-hom-Ring
          ( ring-Rational-Ring R)
          ( ny)
          ( int-positive-ℤ dx))

      lemma-x :
        rz ＝ map-fraction-initial-hom-Rational-Ring R x
      lemma-x =
        equational-reasoning
          ( rnx *R rdy) *R (rdx' *R rdy')
          ＝ ( rnx *R rdy) *R (rdy' *R rdx')
            by
              ap
                ( mul-Rational-Ring R (rnx *R rdy))
                ( commutative-rdxy)
          ＝ ( (rnx *R rdy) *R rdy') *R rdx'
            by
              inv
                ( associative-mul-Ring
                  ( ring-Rational-Ring R)
                  ( rnx *R rdy)
                  ( rdy')
                  ( rdx'))
          ＝ ( rnx *R (rdy *R rdy')) *R rdx'
            by
              ap
                ( mul-Ring' (ring-Rational-Ring R) rdx')
                ( associative-mul-Ring
                  ( ring-Rational-Ring R)
                  ( rnx)
                  ( rdy)
                  ( rdy'))
          ＝ ( rnx *R (one-Ring (ring-Rational-Ring R))) *R rdx'
            by
              ap
                ( λ z → (rnx *R z) *R rdx')
                ( right-inverse-law-positive-integer-Rational-Ring R dy)
          ＝ map-fraction-initial-hom-Rational-Ring R x
            by
              ap
                ( mul-Ring' (ring-Rational-Ring R) rdx')
                ( right-unit-law-mul-Ring (ring-Rational-Ring R) rnx)

      lemma-y :
        rz ＝ map-fraction-initial-hom-Rational-Ring R y
      lemma-y =
        equational-reasoning
          ( rnx *R rdy) *R (rdx' *R rdy')
          ＝ ( rny *R rdx) *R (rdx' *R rdy')
            by
              ap
                ( mul-Ring' (ring-Rational-Ring R) (rdx' *R rdy'))
                ( lemma-rnd)
          ＝ ( (rny *R rdx) *R rdx') *R rdy'
            by
              inv
                ( associative-mul-Ring
                  ( ring-Rational-Ring R)
                  ( rny *R rdx)
                  ( rdx')
                  ( rdy'))
          ＝ ( rny *R (rdx *R rdx')) *R rdy'
            by
              ap
                ( mul-Ring' (ring-Rational-Ring R) (rdy'))
                ( associative-mul-Ring
                  ( ring-Rational-Ring R)
                  ( rny)
                  ( rdx)
                  ( rdx'))
          ＝ ( rny *R (one-Ring (ring-Rational-Ring R))) *R rdy'
            by
              ap
                ( λ z → (rny *R z) *R rdy')
                ( right-inverse-law-positive-integer-Rational-Ring R dx)
          ＝ map-fraction-initial-hom-Rational-Ring R y
            by
              ap
                ( mul-Ring' (ring-Rational-Ring R) rdy')
                ( right-unit-law-mul-Ring (ring-Rational-Ring R) rny)
```

### The fractional initial map preserves addition

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  preserves-add-map-fraction-initial-hom-Rational-Ring :
    {x y : fraction-ℤ} →
    map-fraction-initial-hom-Rational-Ring
      ( R)
      ( add-fraction-ℤ x y) ＝
    add-Rational-Ring
      ( R)
      ( map-fraction-initial-hom-Rational-Ring R x)
      ( map-fraction-initial-hom-Rational-Ring R y)
  preserves-add-map-fraction-initial-hom-Rational-Ring
    {x@(nx , dx)} {y@(ny , dy)} =
    ( ap
      ( mul-Ring'
        ( ring-Rational-Ring R)
        ( inv-positive-integer-Rational-Ring R (mul-positive-ℤ dx dy)))
      ( lemma-add-numerator)) ∙
    ( right-distributive-mul-add-Ring
      ( ring-Rational-Ring R)
      ( map-integer-initial-hom-Rational-Ring
        ( R)
        ( int-mul-positive-ℤ' dy nx))
      ( map-integer-initial-hom-Rational-Ring
        ( R)
        ( int-mul-positive-ℤ' dx ny))
      ( inv-positive-integer-Rational-Ring R (mul-positive-ℤ dx dy))) ∙
    ( ap-binary
      ( add-Rational-Ring R)
      ( lemma-x)
      ( lemma-y))
    where

    _*R_ : type-Rational-Ring R → type-Rational-Ring R → type-Rational-Ring R
    _*R_ = mul-Rational-Ring R

    rnx rdx rdx' rny rdy rdy' : type-Rational-Ring R
    rnx = map-integer-initial-hom-Rational-Ring R nx
    rdx = map-integer-initial-hom-Rational-Ring R (int-positive-ℤ dx)
    rdx' = inv-positive-integer-Rational-Ring R dx
    rny = map-integer-initial-hom-Rational-Ring R ny
    rdy = map-integer-initial-hom-Rational-Ring R (int-positive-ℤ dy)
    rdy' = inv-positive-integer-Rational-Ring R dy

    lemma-add-numerator :
      map-integer-initial-hom-Rational-Ring
        ( R)
        ( ( int-mul-positive-ℤ' dy nx) +ℤ (int-mul-positive-ℤ' dx ny)) ＝
      add-Rational-Ring
        ( R)
        ( map-integer-initial-hom-Rational-Ring R (int-mul-positive-ℤ' dy nx))
        ( map-integer-initial-hom-Rational-Ring R (int-mul-positive-ℤ' dx ny))
    lemma-add-numerator =
      preserves-add-initial-hom-Ring
        ( ring-Rational-Ring R)
        ( int-mul-positive-ℤ' dy nx)
        ( int-mul-positive-ℤ' dx ny)

    lemma-add-denominator :
      inv-positive-integer-Rational-Ring
        ( R)
        ( mul-positive-ℤ dx dy) ＝
      mul-Rational-Ring
        ( R)
        ( inv-positive-integer-Rational-Ring R dx)
        ( inv-positive-integer-Rational-Ring R dy)
    lemma-add-denominator =
      eq-mul-inv-positive-integer-Rational-Ring R dx dy

    lemma-nxdy :
      map-integer-initial-hom-Rational-Ring
        ( R)
        ( int-mul-positive-ℤ' dy nx) ＝
      mul-Rational-Ring
        ( R)
        ( map-integer-initial-hom-Rational-Ring R nx)
        ( map-integer-initial-hom-Rational-Ring R (int-positive-ℤ dy))
    lemma-nxdy =
      preserves-mul-initial-hom-Ring
        ( ring-Rational-Ring R)
        ( nx)
        ( int-positive-ℤ dy)

    lemma-nydx :
      map-integer-initial-hom-Rational-Ring
        ( R)
        ( int-mul-positive-ℤ' dx ny) ＝
      mul-Rational-Ring
        ( R)
        ( map-integer-initial-hom-Rational-Ring R ny)
        ( map-integer-initial-hom-Rational-Ring R (int-positive-ℤ dx))
    lemma-nydx =
      preserves-mul-initial-hom-Ring
        ( ring-Rational-Ring R)
        ( ny)
        ( int-positive-ℤ dx)

    lemma-add-denominator' :
      inv-positive-integer-Rational-Ring
        ( R)
        ( mul-positive-ℤ dx dy) ＝
      mul-Rational-Ring
        ( R)
        ( inv-positive-integer-Rational-Ring R dy)
        ( inv-positive-integer-Rational-Ring R dx)
    lemma-add-denominator' =
      ( ap
        ( inv-positive-integer-Rational-Ring R)
        ( eq-type-subtype
          ( subtype-positive-ℤ)
          ( commutative-mul-ℤ (int-positive-ℤ dx) (int-positive-ℤ dy)))) ∙
      ( eq-mul-inv-positive-integer-Rational-Ring R dy dx)

    lemma-x :
      map-fraction-initial-hom-Rational-Ring
        ( R)
        ( int-mul-positive-ℤ' dy nx , mul-positive-ℤ dx dy) ＝
      map-fraction-initial-hom-Rational-Ring R x
    lemma-x =
      ( ap
        ( mul-Rational-Ring
          ( R)
          ( map-integer-initial-hom-Rational-Ring
            ( R)
            ( int-mul-positive-ℤ' dy nx)))
        ( ( lemma-add-denominator'))) ∙
      ( ap
        ( mul-Ring'
          ( ring-Rational-Ring R)
          ( mul-Rational-Ring R rdy' rdx'))
        ( lemma-nxdy)) ∙
      ( inv
        ( associative-mul-Ring
          ( ring-Rational-Ring R)
          ( rnx *R rdy)
          ( rdy')
          ( rdx'))) ∙
      ( ap
        ( mul-Ring'
          ( ring-Rational-Ring R)
          ( rdx'))
        ( associative-mul-Ring
          ( ring-Rational-Ring R)
          ( rnx)
          ( rdy)
          ( rdy'))) ∙
      ( ap
        ( λ z → (rnx *R z) *R rdx')
        ( right-inverse-law-positive-integer-Rational-Ring R dy)) ∙
      ( ap
        ( mul-Ring' (ring-Rational-Ring R) (rdx'))
        ( right-unit-law-mul-Ring (ring-Rational-Ring R) rnx))

    lemma-y :
      map-fraction-initial-hom-Rational-Ring
        ( R)
        ( int-mul-positive-ℤ' dx ny , mul-positive-ℤ dx dy) ＝
      map-fraction-initial-hom-Rational-Ring R y
    lemma-y =
      ( ap
        ( mul-Rational-Ring
          ( R)
          ( map-integer-initial-hom-Rational-Ring
            ( R)
            ( int-mul-positive-ℤ' dx ny)))
        ( ( lemma-add-denominator))) ∙
      ( ap
        ( mul-Ring'
          ( ring-Rational-Ring R)
          ( mul-Rational-Ring R rdx' rdy'))
        ( lemma-nydx)) ∙
      ( inv
        ( associative-mul-Ring
          ( ring-Rational-Ring R)
          ( rny *R rdx)
          ( rdx')
          ( rdy'))) ∙
      ( ap
        ( mul-Ring'
          ( ring-Rational-Ring R)
          ( rdy'))
        ( associative-mul-Ring
          ( ring-Rational-Ring R)
          ( rny)
          ( rdx)
          ( rdx'))) ∙
      ( ap
        ( λ z → (rny *R z) *R rdy')
        ( right-inverse-law-positive-integer-Rational-Ring R dx)) ∙
      ( ap
        ( mul-Ring' (ring-Rational-Ring R) (rdy'))
        ( right-unit-law-mul-Ring (ring-Rational-Ring R) rny))
```

### The fractional initial map preserves multiplication

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  preserves-mul-map-fraction-initial-hom-Rational-Ring :
    {x y : fraction-ℤ} →
    map-fraction-initial-hom-Rational-Ring
      ( R)
      ( mul-fraction-ℤ x y) ＝
    mul-Rational-Ring
      ( R)
      ( map-fraction-initial-hom-Rational-Ring R x)
      ( map-fraction-initial-hom-Rational-Ring R y)
  preserves-mul-map-fraction-initial-hom-Rational-Ring
    {x@(nx , dx)} {y@(ny , dy)} =
    ( ap
      ( mul-Rational-Ring
        ( R)
        ( map-integer-initial-hom-Rational-Ring R (nx *ℤ ny)))
      ( eq-mul-inv-positive-integer-Rational-Ring R dx dy)) ∙
    ( inv
      ( associative-mul-Ring
        ( ring-Rational-Ring R)
        ( map-integer-initial-hom-Rational-Ring R (nx *ℤ ny))
        ( rdx')
        ( rdy'))) ∙
    ( ap
      ( mul-Ring' (ring-Rational-Ring R) (rdy'))
      ( ( htpy-map-fraction-initial-hom-Rational-Ring'
          ( R)
          ( (nx *ℤ ny) , dx)) ∙
        ( ap
          ( mul-Ring (ring-Rational-Ring R) rdx')
          ( preserves-mul-initial-hom-Ring
            ( ring-Rational-Ring R)
            ( nx)
            ( ny))) ∙
        ( inv
          ( associative-mul-Ring
            ( ring-Rational-Ring R)
            ( rdx')
            ( rnx)
            ( rny))))) ∙
    ( associative-mul-Ring
      ( ring-Rational-Ring R)
      ( rdx' *R rnx)
      ( rny)
      ( rdy')) ∙
    ( ap
      ( mul-Ring' (ring-Rational-Ring R) (rny *R rdy'))
      ( inv
        ( htpy-map-fraction-initial-hom-Rational-Ring'
          ( R)
          ( x))))
    where

    _*R_ : type-Rational-Ring R → type-Rational-Ring R → type-Rational-Ring R
    _*R_ = mul-Rational-Ring R

    rnx rdx rdx' rny rdy rdy' : type-Rational-Ring R
    rnx = map-integer-initial-hom-Rational-Ring R nx
    rdx = map-integer-initial-hom-Rational-Ring R (int-positive-ℤ dx)
    rdx' = inv-positive-integer-Rational-Ring R dx
    rny = map-integer-initial-hom-Rational-Ring R ny
    rdy = map-integer-initial-hom-Rational-Ring R (int-positive-ℤ dy)
    rdy' = inv-positive-integer-Rational-Ring R dy
```

### The rational initial ring map extends the initial ring homomorphism

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  htpy-integer-map-initial-hom-Rational-Ring :
    map-rational-initial-hom-Rational-Ring R ∘ rational-ℤ ~
    map-integer-initial-hom-Rational-Ring R
  htpy-integer-map-initial-hom-Rational-Ring k =
    ( ap
      ( mul-Rational-Ring R (map-integer-initial-hom-Rational-Ring R k))
      ( inv (eq-one-inv-positive-one-Rational-Ring R))) ∙
    ( right-unit-law-mul-Ring
      ( ring-Rational-Ring R)
      ( map-integer-initial-hom-Rational-Ring R k))
```

### The rational initial ring map preserves one

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  preserves-one-rational-initial-hom-Rational-Ring :
    map-rational-initial-hom-Rational-Ring R one-ℚ ＝
    one-Ring (ring-Rational-Ring R)
  preserves-one-rational-initial-hom-Rational-Ring =
    is-right-inverse-inv-is-invertible-element-Ring
      ( ring-Rational-Ring R)
      ( is-invertible-positive-integer-Rational-Ring R one-ℤ⁺)
```

### The initial ring map is a ring homomorphism

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  preserves-add-initial-hom-Rational-Ring :
    {x y : ℚ} →
    map-rational-initial-hom-Rational-Ring R (x +ℚ y) ＝
    add-Ring
      ( ring-Rational-Ring R)
      ( map-rational-initial-hom-Rational-Ring R x)
      ( map-rational-initial-hom-Rational-Ring R y)
  preserves-add-initial-hom-Rational-Ring {x} {y} =
    equational-reasoning
      map-rational-initial-hom-Rational-Ring R (x +ℚ y)
      ＝ map-fraction-initial-hom-Rational-Ring
        ( R)
        ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
        by
          eq-map-sim-fraction-map-initial-Rational-Ring
            ( R)
            ( reduce-fraction-ℤ
              ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)))
            ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
            ( symmetric-sim-fraction-ℤ
              ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
              ( reduce-fraction-ℤ
                ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)))
              ( sim-reduced-fraction-ℤ
                ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))))
      ＝ add-Ring
        ( ring-Rational-Ring R)
        ( map-rational-initial-hom-Rational-Ring R x)
        ( map-rational-initial-hom-Rational-Ring R y)
        by (preserves-add-map-fraction-initial-hom-Rational-Ring R)

  preserves-mul-initial-hom-Rational-Ring :
    {x y : ℚ} →
    map-rational-initial-hom-Rational-Ring R (x *ℚ y) ＝
    mul-Ring
      ( ring-Rational-Ring R)
      ( map-rational-initial-hom-Rational-Ring R x)
      ( map-rational-initial-hom-Rational-Ring R y)
  preserves-mul-initial-hom-Rational-Ring {x} {y} =
    equational-reasoning
      map-rational-initial-hom-Rational-Ring R (x *ℚ y)
      ＝ map-fraction-initial-hom-Rational-Ring
        ( R)
        ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
        by
          eq-map-sim-fraction-map-initial-Rational-Ring
            ( R)
            ( reduce-fraction-ℤ
              ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)))
            ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
            ( symmetric-sim-fraction-ℤ
              ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
              ( reduce-fraction-ℤ
                ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)))
              ( sim-reduced-fraction-ℤ
                ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))))
      ＝ mul-Ring
        ( ring-Rational-Ring R)
        ( map-rational-initial-hom-Rational-Ring R x)
        ( map-rational-initial-hom-Rational-Ring R y)
        by (preserves-mul-map-fraction-initial-hom-Rational-Ring R)

  initial-hom-Rational-Ring : rational-hom-Rational-Ring R
  pr1 initial-hom-Rational-Ring =
    ( map-rational-initial-hom-Rational-Ring R ,
      preserves-add-initial-hom-Rational-Ring)
  pr2 initial-hom-Rational-Ring =
    ( preserves-mul-initial-hom-Rational-Ring ,
      preserves-one-rational-initial-hom-Rational-Ring R)
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

  htpy-map-integer-hom-Rational-Ring :
    ( map-rational-hom-Rational-Ring R f ∘ rational-ℤ) ~
    ( map-initial-hom-Ring (ring-Rational-Ring R))
  htpy-map-integer-hom-Rational-Ring =
    htpy-map-integer-rational-hom-Ring (ring-Rational-Ring R) f
```

### A ring homomorphism `ℚ → R` preserves reciprocals of positive integers

```agda
module _
  {l : Level} (R : Rational-Ring l) (f : rational-hom-Rational-Ring R)
  where

  htpy-map-reciprocal-hom-Rational-Ring :
    map-rational-hom-Rational-Ring R f ∘ reciprocal-rational-ℤ⁺ ~
    inv-positive-integer-Rational-Ring R
  htpy-map-reciprocal-hom-Rational-Ring k =
    inv
      ( contraction-right-inverse-is-invertible-element-Ring
        ( ring-Rational-Ring R)
        ( map-integer-initial-hom-Rational-Ring R (int-positive-ℤ k))
        ( is-invertible-positive-integer-Rational-Ring R k)
        ( map-rational-hom-Rational-Ring R f (reciprocal-rational-ℤ⁺ k))
        ( is-right-inverse-map-reciprocal))
    where

    is-right-inverse-map-reciprocal :
      is-right-inverse-element-Ring
        ( ring-Rational-Ring R)
        ( map-integer-initial-hom-Rational-Ring R (int-positive-ℤ k))
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
        ( inv (htpy-map-integer-hom-Rational-Ring R f (int-positive-ℤ k)))) ∙
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
    htpy-map-reciprocal-hom-Rational-Ring
      ( rational-ring-has-rational-hom-Ring R f)
      ( f)
```

### Any homomorphism `ℚ → R` is homotopic to the rational initial ring homomorphism

```agda
module _
  {l : Level} (R : Rational-Ring l) (f : rational-hom-Rational-Ring R)
  where

  htpy-map-rational-initial-hom-Rational-Ring :
    ( map-rational-hom-Rational-Ring R f) ~
    ( map-rational-initial-hom-Rational-Ring R)
  htpy-map-rational-initial-hom-Rational-Ring x =
    ( ap
      ( map-rational-hom-Rational-Ring R f)
      ( inv (eq-mul-numerator-reciprocal-denominator-ℚ x))) ∙
    ( preserves-mul-hom-Ring
      ( ring-ℚ)
      ( ring-Rational-Ring R)
      ( f)) ∙
    ( ap-binary
      ( mul-Ring (ring-Rational-Ring R))
      ( htpy-map-integer-hom-Rational-Ring R f (numerator-ℚ x))
      ( htpy-map-reciprocal-hom-Rational-Ring R f (positive-denominator-ℚ x)))

module _
  {l : Level} (R : Ring l) (f : hom-Ring ring-ℚ R)
  where

  htpy-map-rational-hom-Ring :
    ( map-hom-Ring ring-ℚ R f) ~
    ( map-rational-initial-hom-Rational-Ring
      ( rational-ring-has-rational-hom-Ring R f))
  htpy-map-rational-hom-Ring =
    htpy-map-rational-initial-hom-Rational-Ring
      ( rational-ring-has-rational-hom-Ring R f)
      ( f)
```

### The type of ring homomorphisms from `ℚ` to a rational ring is contractible

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  is-contr-rational-hom-Rational-Ring :
    is-contr (rational-hom-Rational-Ring R)
  is-contr-rational-hom-Rational-Ring =
    ( initial-hom-Rational-Ring R) ,
    ( λ g →
      eq-htpy-hom-Ring
        ( ring-ℚ)
        ( ring-Rational-Ring R)
        ( initial-hom-Rational-Ring R)
        ( g)
        ( inv ∘ htpy-map-rational-initial-hom-Rational-Ring R g))

  is-prop-rational-hom-Rational-Ring :
    is-prop (rational-hom-Rational-Ring R)
  is-prop-rational-hom-Rational-Ring =
    is-prop-is-contr is-contr-rational-hom-Rational-Ring
```

### All ring homomorphisms `ℚ → R` are equal

```agda
module _
  {l : Level} (R : Ring l)
  where

  all-eq-rational-hom-Ring : (f g : hom-Ring ring-ℚ R) → f ＝ g
  all-eq-rational-hom-Ring f g =
    eq-is-prop
      ( is-prop-rational-hom-Rational-Ring
        ( rational-ring-has-rational-hom-Ring R f))

  is-prop-has-rational-hom-Ring : is-prop (hom-Ring ring-ℚ R)
  is-prop-has-rational-hom-Ring =
    is-prop-all-elements-equal all-eq-rational-hom-Ring

  has-rational-hom-prop-Ring : Prop l
  has-rational-hom-prop-Ring =
    hom-Ring ring-ℚ R , is-prop-has-rational-hom-Ring
```

### A ring `R` is rational if and only if there exists a ring homomorphism `ℚ → R`

```agda
module _
  {l : Level} (R : Ring l)
  where

  has-rational-hom-is-rational-Ring : is-rational-Ring R → hom-Ring ring-ℚ R
  has-rational-hom-is-rational-Ring =
    initial-hom-Rational-Ring ∘ pair R

  iff-is-rational-has-rational-hom-Ring : hom-Ring ring-ℚ R ↔ is-rational-Ring R
  iff-is-rational-has-rational-hom-Ring =
    ( is-rational-has-rational-hom-Ring R , has-rational-hom-is-rational-Ring)
```

### A ring `R` is rational if and only if the type of ring homomorphisms `ℚ → R` is contractible

```agda
module _
  {l : Level} (R : Ring l)
  where

  iff-is-rational-is-contr-rational-hom-Ring :
    is-contr (hom-Ring ring-ℚ R) ↔ is-rational-Ring R
  iff-is-rational-is-contr-rational-hom-Ring =
    ( is-rational-has-rational-hom-Ring R ∘ center) ,
    ( is-contr-rational-hom-Rational-Ring ∘ pair R)
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
      ( is-rational-ring-Rational-Ring rational-ring-ℚ)
  universal-property-localization-positive-integers-rational-Ring T =
    is-equiv-has-converse-is-prop
      ( is-prop-has-rational-hom-Ring T)
      ( is-prop-type-subtype
        ( inverts-subset-prop-hom-Ring ℤ-Ring T subtype-positive-ℤ)
        ( is-prop-is-contr (is-initial-ℤ-Ring T)))
      ( λ (f , H) →
        initial-hom-Rational-Ring
          ( ( T) ,
            ( inv-tr
              ( inverts-subset-hom-Ring ℤ-Ring T subtype-positive-ℤ)
              ( contraction-initial-hom-Ring T f)
              ( H))))
```

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
