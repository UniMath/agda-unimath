# The rational ring of rational numbers

```agda
{-# OPTIONS --lossy-unification #-}

module elementary-number-theory.rational-ring-of-rational-numbers where
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
open import ring-theory.rational-rings
open import ring-theory.rings
```

</details>

## Idea

The [reciprocal](elementary-number-theory.unit-fractions-rational-numbers.md) of
a [positive integers](elementary-number-theory.positive-integers.md) is its
[inverse](ring-theory.invertible-elements-rings.md) in the
[ring of rational numbers](elementary-number-theory.ring-of-rational-numbers.md)
so `ℚ` is a [rational ring](ring-theory.rational-rings.md); this is the
{{#concept "rational ring of rationa numbers" Agda=rational-ring-ℚ}}.

Furthermore, the rational extension of the initial ring map `ι : ℤ → R` into a
rational ring, `γ : (p/q : ℚ) ↦ (ι p)(ι q)⁻¹`, is a
[ring homomorphism](ring-theory.homomorphisms-rings.md) so `ℚ` is the
**initial** rational ring, i.e., the type of ring homomorphisms between `ℚ` and
any rational ring is [contractible](foundation.contractible-types.md).

## Definitions

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

## Properties

### The fractional initial map into a rational ring extends the initial ring homomorphism

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  htpy-map-integer-fraction-map-initial-Rational-Ring :
    map-initial-hom-fraction-Rational-Ring R ∘ in-fraction-ℤ ~
    map-initial-hom-integer-Rational-Ring R
  htpy-map-integer-fraction-map-initial-Rational-Ring k =
    ( ap
      ( mul-Rational-Ring R (map-initial-hom-integer-Rational-Ring R k))
      ( inv (eq-one-inv-positive-one-Rational-Ring R))) ∙
    ( right-unit-law-mul-Ring
      ( ring-Rational-Ring R)
      ( map-initial-hom-integer-Rational-Ring R k))
```

### The fractional initial map maps similar fractions to identical elements

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  eq-map-sim-fraction-map-initial-Rational-Ring :
    {x y : fraction-ℤ} →
    sim-fraction-ℤ x y →
    map-initial-hom-fraction-Rational-Ring R x ＝
    map-initial-hom-fraction-Rational-Ring R y
  eq-map-sim-fraction-map-initial-Rational-Ring
    {x@(nx , dx)} {y@(ny , dy)} x~y =
    (inv lemma-x) ∙ lemma-y
    where
      _*R_ : type-Rational-Ring R → type-Rational-Ring R → type-Rational-Ring R
      _*R_ = mul-Rational-Ring R

      rnx rdx rdx' rny rdy rdy' rz : type-Rational-Ring R

      rnx = map-initial-hom-integer-Rational-Ring R nx
      rdx = map-initial-hom-integer-Rational-Ring R (int-positive-ℤ dx)
      rdx' = inv-positive-integer-Rational-Ring R dx

      rny = map-initial-hom-integer-Rational-Ring R ny
      rdy = map-initial-hom-integer-Rational-Ring R (int-positive-ℤ dy)
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
        rz ＝ map-initial-hom-fraction-Rational-Ring R x
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
          ＝ map-initial-hom-fraction-Rational-Ring R x
            by
              ap
                ( mul-Ring' (ring-Rational-Ring R) rdx')
                ( right-unit-law-mul-Ring (ring-Rational-Ring R) rnx)

      lemma-y :
        rz ＝ map-initial-hom-fraction-Rational-Ring R y
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
          ＝ map-initial-hom-fraction-Rational-Ring R y
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

  preserves-add-map-initial-hom-fraction-Rational-Ring :
    {x y : fraction-ℤ} →
    map-initial-hom-fraction-Rational-Ring
      ( R)
      ( add-fraction-ℤ x y) ＝
    add-Rational-Ring
      ( R)
      ( map-initial-hom-fraction-Rational-Ring R x)
      ( map-initial-hom-fraction-Rational-Ring R y)
  preserves-add-map-initial-hom-fraction-Rational-Ring
    {x@(nx , dx)} {y@(ny , dy)} =
    ( ap
      ( mul-Ring'
        ( ring-Rational-Ring R)
        ( inv-positive-integer-Rational-Ring R (mul-positive-ℤ dx dy)))
      ( lemma-add-numerator)) ∙
    ( right-distributive-mul-add-Ring
      ( ring-Rational-Ring R)
      ( map-initial-hom-integer-Rational-Ring
        ( R)
        ( int-mul-positive-ℤ' dy nx))
      ( map-initial-hom-integer-Rational-Ring
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
    rnx = map-initial-hom-integer-Rational-Ring R nx
    rdx = map-initial-hom-integer-Rational-Ring R (int-positive-ℤ dx)
    rdx' = inv-positive-integer-Rational-Ring R dx
    rny = map-initial-hom-integer-Rational-Ring R ny
    rdy = map-initial-hom-integer-Rational-Ring R (int-positive-ℤ dy)
    rdy' = inv-positive-integer-Rational-Ring R dy

    lemma-add-numerator :
      map-initial-hom-integer-Rational-Ring
        ( R)
        ( ( int-mul-positive-ℤ' dy nx) +ℤ (int-mul-positive-ℤ' dx ny)) ＝
      add-Rational-Ring
        ( R)
        ( map-initial-hom-integer-Rational-Ring R (int-mul-positive-ℤ' dy nx))
        ( map-initial-hom-integer-Rational-Ring R (int-mul-positive-ℤ' dx ny))
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
      map-initial-hom-integer-Rational-Ring
        ( R)
        ( int-mul-positive-ℤ' dy nx) ＝
      mul-Rational-Ring
        ( R)
        ( map-initial-hom-integer-Rational-Ring R nx)
        ( map-initial-hom-integer-Rational-Ring R (int-positive-ℤ dy))
    lemma-nxdy =
      preserves-mul-initial-hom-Ring
        ( ring-Rational-Ring R)
        ( nx)
        ( int-positive-ℤ dy)

    lemma-nydx :
      map-initial-hom-integer-Rational-Ring
        ( R)
        ( int-mul-positive-ℤ' dx ny) ＝
      mul-Rational-Ring
        ( R)
        ( map-initial-hom-integer-Rational-Ring R ny)
        ( map-initial-hom-integer-Rational-Ring R (int-positive-ℤ dx))
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
      map-initial-hom-fraction-Rational-Ring
        ( R)
        ( int-mul-positive-ℤ' dy nx , mul-positive-ℤ dx dy) ＝
      map-initial-hom-fraction-Rational-Ring R x
    lemma-x =
      ( ap
        ( mul-Rational-Ring
          ( R)
          ( map-initial-hom-integer-Rational-Ring
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
      map-initial-hom-fraction-Rational-Ring
        ( R)
        ( int-mul-positive-ℤ' dx ny , mul-positive-ℤ dx dy) ＝
      map-initial-hom-fraction-Rational-Ring R y
    lemma-y =
      ( ap
        ( mul-Rational-Ring
          ( R)
          ( map-initial-hom-integer-Rational-Ring
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

  preserves-mul-map-initial-hom-fraction-Rational-Ring :
    {x y : fraction-ℤ} →
    map-initial-hom-fraction-Rational-Ring
      ( R)
      ( mul-fraction-ℤ x y) ＝
    mul-Rational-Ring
      ( R)
      ( map-initial-hom-fraction-Rational-Ring R x)
      ( map-initial-hom-fraction-Rational-Ring R y)
  preserves-mul-map-initial-hom-fraction-Rational-Ring
    {x@(nx , dx)} {y@(ny , dy)} =
    ( ap
      ( mul-Rational-Ring
        ( R)
        ( map-initial-hom-integer-Rational-Ring R (nx *ℤ ny)))
      ( eq-mul-inv-positive-integer-Rational-Ring R dx dy)) ∙
    ( inv
      ( associative-mul-Ring
        ( ring-Rational-Ring R)
        ( map-initial-hom-integer-Rational-Ring R (nx *ℤ ny))
        ( rdx')
        ( rdy'))) ∙
    ( ap
      ( mul-Ring' (ring-Rational-Ring R) (rdy'))
      ( ( htpy-map-initial-hom-fraction-Rational-Ring'
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
        ( htpy-map-initial-hom-fraction-Rational-Ring'
          ( R)
          ( x))))
    where

    _*R_ : type-Rational-Ring R → type-Rational-Ring R → type-Rational-Ring R
    _*R_ = mul-Rational-Ring R

    rnx rdx rdx' rny rdy rdy' : type-Rational-Ring R
    rnx = map-initial-hom-integer-Rational-Ring R nx
    rdx = map-initial-hom-integer-Rational-Ring R (int-positive-ℤ dx)
    rdx' = inv-positive-integer-Rational-Ring R dx
    rny = map-initial-hom-integer-Rational-Ring R ny
    rdy = map-initial-hom-integer-Rational-Ring R (int-positive-ℤ dy)
    rdy' = inv-positive-integer-Rational-Ring R dy
```

### The rational initial ring map extends the initial ring homomorphism

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  htpy-integer-map-initial-hom-Rational-Ring :
    map-initial-hom-Rational-Ring R ∘ rational-ℤ ~
    map-initial-hom-integer-Rational-Ring R
  htpy-integer-map-initial-hom-Rational-Ring k =
    ( ap
      ( mul-Rational-Ring R (map-initial-hom-integer-Rational-Ring R k))
      ( inv (eq-one-inv-positive-one-Rational-Ring R))) ∙
    ( right-unit-law-mul-Ring
      ( ring-Rational-Ring R)
      ( map-initial-hom-integer-Rational-Ring R k))
```

### The rational initial ring map preserves one

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  preserves-one-rational-initial-hom-Rational-Ring :
    map-initial-hom-Rational-Ring R one-ℚ ＝
    one-Ring (ring-Rational-Ring R)
  preserves-one-rational-initial-hom-Rational-Ring =
    is-right-inverse-inv-is-invertible-element-Ring
      ( ring-Rational-Ring R)
      ( is-invertible-positive-integer-Rational-Ring R one-ℤ⁺)
```

### The rational initial ring map is a ring homomorphism

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  preserves-add-initial-hom-Rational-Ring :
    {x y : ℚ} →
    map-initial-hom-Rational-Ring R (x +ℚ y) ＝
    add-Ring
      ( ring-Rational-Ring R)
      ( map-initial-hom-Rational-Ring R x)
      ( map-initial-hom-Rational-Ring R y)
  preserves-add-initial-hom-Rational-Ring {x} {y} =
    equational-reasoning
      map-initial-hom-Rational-Ring R (x +ℚ y)
      ＝ map-initial-hom-fraction-Rational-Ring
        ( R)
        ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
        by
          eq-map-sim-fraction-map-initial-Rational-Ring
            ( R)
            ( symmetric-sim-fraction-ℤ
              ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
              ( reduce-fraction-ℤ
                ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)))
              ( sim-reduced-fraction-ℤ
                ( add-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))))
      ＝ add-Ring
        ( ring-Rational-Ring R)
        ( map-initial-hom-Rational-Ring R x)
        ( map-initial-hom-Rational-Ring R y)
        by (preserves-add-map-initial-hom-fraction-Rational-Ring R)

  preserves-mul-initial-hom-Rational-Ring :
    {x y : ℚ} →
    map-initial-hom-Rational-Ring R (x *ℚ y) ＝
    mul-Ring
      ( ring-Rational-Ring R)
      ( map-initial-hom-Rational-Ring R x)
      ( map-initial-hom-Rational-Ring R y)
  preserves-mul-initial-hom-Rational-Ring {x} {y} =
    equational-reasoning
      map-initial-hom-Rational-Ring R (x *ℚ y)
      ＝ map-initial-hom-fraction-Rational-Ring
        ( R)
        ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
        by
          eq-map-sim-fraction-map-initial-Rational-Ring
            ( R)
            ( symmetric-sim-fraction-ℤ
              ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
              ( reduce-fraction-ℤ
                ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)))
              ( sim-reduced-fraction-ℤ
                ( mul-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))))
      ＝ mul-Ring
        ( ring-Rational-Ring R)
        ( map-initial-hom-Rational-Ring R x)
        ( map-initial-hom-Rational-Ring R y)
        by (preserves-mul-map-initial-hom-fraction-Rational-Ring R)

  initial-hom-Rational-Ring : rational-hom-Rational-Ring R
  pr1 initial-hom-Rational-Ring =
    ( map-initial-hom-Rational-Ring R ,
      preserves-add-initial-hom-Rational-Ring)
  pr2 initial-hom-Rational-Ring =
    ( preserves-mul-initial-hom-Rational-Ring ,
      preserves-one-rational-initial-hom-Rational-Ring R)
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
        ( inv ∘ htpy-map-initial-hom-Rational-Ring R g))

  is-prop-rational-hom-Rational-Ring :
    is-prop (rational-hom-Rational-Ring R)
  is-prop-rational-hom-Rational-Ring =
    is-prop-is-contr is-contr-rational-hom-Rational-Ring
```

### The ring of rational numbers is the initial rational ring

```agda
module _
  {l : Level}
  where

  is-initial-rational-ring-ℚ :
    (R : Rational-Ring l) →
    is-contr (hom-Rational-Ring rational-ring-ℚ R)
  is-initial-rational-ring-ℚ R =
    is-contr-rational-hom-Rational-Ring R
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
