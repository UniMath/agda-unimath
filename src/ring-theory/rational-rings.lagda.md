# Rational rings

```agda
{-# OPTIONS --lossy-unification #-}

module ring-theory.rational-rings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-integers
open import elementary-number-theory.addition-rational-numbers
open import elementary-number-theory.integers
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.multiplication-rational-numbers
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
open import foundation.propositions
open import foundation.sets
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import group-theory.groups
open import group-theory.homomorphisms-abelian-groups

open import ring-theory.groups-of-units-rings
open import ring-theory.homomorphisms-rings
open import ring-theory.invertible-elements-rings
open import ring-theory.localizations-rings
open import ring-theory.rings
```

</details>

## Idea

A {{#concept "rational ring" Agda=Rational-Ring}} is a
[ring](ring-theory.rings.md) where the
[positive integers](elementary-number-theory.positive-integers.md) are
[invertible](ring-theory.invertible-elements-rings.md) (modulo the
[initial ring homomorphism](elementary-number-theory.ring-of-integers.md)).

The
[ring of rational numbers](elementary-number-theory.ring-of-rational-numbers.md)
is rational; moreover, for any rational ring `R`, the
[initial ring homomorphism](elementary-number-theory.ring-of-integers)
`ι : ℤ → R` extends to a [ring homomorphism](ring-theory.homomorphisms-rings.md)
`ℚ → R` by `p/q ↦ (ι p)(ι q)⁻¹` and this is the unique ring homomorphism
`ℚ → R`. In other words, for any rational ring `R`, `hom-Ring ℚ R` is
[contractible](foundation.contractible-types.md) so `ℚ` is the
[initial](ring-theory.initial-rings.md) rational ring.

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

  inv-positive-integer-has-rational-hom-Ring :
    hom-Ring ring-ℚ R → (k : ℤ⁺) → type-Ring R
  inv-positive-integer-has-rational-hom-Ring f =
    inv-positive-integer-Rational-Ring
      ( R , is-rational-has-rational-hom-Ring f)
```

### For any ring homomorphism `f : ℚ → R` and `k : ℤ`, `f k ＝ ι k` where `ι : ℤ → R` is the initial ring homomorphism in `R`

```agda
module _
  {l : Level}
  where

  eq-map-integer-rational-hom-Ring :
    ( R : Ring l) →
    ( f : hom-Ring ring-ℚ R) →
    ( k : ℤ) →
    ( map-hom-Ring ring-ℚ R f (rational-ℤ k)) ＝
    ( map-initial-hom-Ring R k)
  eq-map-integer-rational-hom-Ring R f k =
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

  eq-map-integer-hom-Rational-Ring :
    ( R : Rational-Ring l) →
    ( f : rational-hom-Rational-Ring R) →
    ( k : ℤ) →
    ( map-rational-hom-Rational-Ring R f (rational-ℤ k)) ＝
    ( map-initial-hom-Ring (ring-Rational-Ring R) k)
  eq-map-integer-hom-Rational-Ring R =
    eq-map-integer-rational-hom-Ring (ring-Rational-Ring R)
```

### For any ring homomorphism `f : ℚ → R` and `k : ℤ⁺`, `f (1/k) ＝ (ι k)⁻¹` where `ι : ℤ → R` is the initial ring homomorphism in `R`

```agda
module _
  {l : Level}
  where

  eq-map-reciprocal-hom-Rational-Ring :
    ( R : Rational-Ring l) →
    ( f : rational-hom-Rational-Ring R) →
    ( k : ℤ⁺) →
    ( map-rational-hom-Rational-Ring
      ( R)
      ( f)
      ( reciprocal-rational-ℤ⁺ k)) ＝
    ( inv-positive-integer-Rational-Ring R k)
  eq-map-reciprocal-hom-Rational-Ring R f k =
    ap pr1 eq-right-inverse-map-reciprocal
    where

    right-inverse-map-reciprocal :
      is-right-invertible-element-Ring
        ( ring-Rational-Ring R)
        ( map-initial-hom-Ring (ring-Rational-Ring R) (int-positive-ℤ k))
    pr1 right-inverse-map-reciprocal =
      ( map-hom-Ring
        ( ring-ℚ)
        ( ring-Rational-Ring R)
        ( f)
        ( reciprocal-rational-ℤ⁺ k))
    pr2 right-inverse-map-reciprocal =
      ( ap
        ( mul-Ring'
          ( ring-Rational-Ring R)
          ( map-hom-Ring
            ( ring-ℚ)
            ( ring-Rational-Ring R)
            ( f)
            ( reciprocal-rational-ℤ⁺ k)))
        ( inv (eq-map-integer-hom-Rational-Ring R f (int-positive-ℤ k)))) ∙
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

    eq-right-inverse-map-reciprocal :
      ( right-inverse-map-reciprocal) ＝
      ( is-right-invertible-is-invertible-element-Ring
        ( ring-Rational-Ring R)
        ( map-initial-hom-Ring (ring-Rational-Ring R) (int-positive-ℤ k))
        ( is-invertible-positive-integer-Rational-Ring
          ( R)
          ( k)))
    eq-right-inverse-map-reciprocal =
      eq-is-contr
        ( is-contr-is-right-invertible-element-Ring
          ( ring-Rational-Ring R)
          ( map-initial-hom-Ring (ring-Rational-Ring R) (int-positive-ℤ k))
          ( is-invertible-positive-integer-Rational-Ring R k))

  eq-map-reciprocal-rational-hom-Ring :
    ( R : Ring l) →
    ( f : hom-Ring ring-ℚ R) →
    ( k : ℤ⁺) →
    ( map-hom-Ring
      ( ring-ℚ)
      ( R)
      ( f)
      ( reciprocal-rational-ℤ⁺ k)) ＝
    ( inv-positive-integer-has-rational-hom-Ring R f k)
  eq-map-reciprocal-rational-hom-Ring R f =
    eq-map-reciprocal-hom-Rational-Ring
      ( R , is-rational-has-rational-hom-Ring R f)
      ( f)
```

### For any ring homomorphism `f : ℚ → R` and `p/q : ℚ`, `f (p/q) ＝ (ι p)(ι q)⁻¹` where `ι : ℤ → R` is the initial ring homomorphism in `R`

```agda
module _
  {l : Level}
  where

  eq-map-numerator-inv-denominator-hom-Rational-Ring :
    ( R : Rational-Ring l) →
    ( f : rational-hom-Rational-Ring R) →
    ( x : ℚ) →
    ( map-rational-hom-Rational-Ring R f x) ＝
    ( mul-Ring
      ( ring-Rational-Ring R)
      ( map-initial-hom-Ring (ring-Rational-Ring R) (numerator-ℚ x))
      ( inv-positive-integer-Rational-Ring R (positive-denominator-ℚ x)))
  eq-map-numerator-inv-denominator-hom-Rational-Ring R f x =
    ( ap
      ( map-rational-hom-Rational-Ring R f)
      ( inv (eq-mul-numerator-reciprocal-denominator-ℚ x))) ∙
    ( preserves-mul-hom-Ring
      ( ring-ℚ)
      ( ring-Rational-Ring R)
      ( f)) ∙
    ( ap-binary
      ( mul-Ring (ring-Rational-Ring R))
      ( eq-map-integer-hom-Rational-Ring R f (numerator-ℚ x))
      ( eq-map-reciprocal-hom-Rational-Ring R f (positive-denominator-ℚ x)))

  eq-map-numerator-inv-denominator-rational-hom-Ring :
    ( R : Ring l) →
    ( f : hom-Ring ring-ℚ R) →
    ( x : ℚ) →
    ( map-hom-Ring ring-ℚ R f x) ＝
    ( mul-Ring
      ( R)
      ( map-initial-hom-Ring R (numerator-ℚ x))
      ( inv-positive-integer-has-rational-hom-Ring
        ( R)
        ( f)
        ( positive-denominator-ℚ x)))
  eq-map-numerator-inv-denominator-rational-hom-Ring R f =
    eq-map-numerator-inv-denominator-hom-Rational-Ring
      ( R , is-rational-has-rational-hom-Ring R f)
      ( f)
```

### All ring homomorphisms `ℚ → R` are equal

```agda
module _
  {l : Level}
  where

  all-eq-rational-hom-Rational-Ring :
    ( R : Rational-Ring l) →
    ( f g : rational-hom-Rational-Ring R) →
    f ＝ g
  all-eq-rational-hom-Rational-Ring R f g =
    eq-htpy-hom-Ring
      ( ring-ℚ)
      ( ring-Rational-Ring R)
      ( f)
      ( g)
      ( λ x →
        ( eq-map-numerator-inv-denominator-hom-Rational-Ring R f x) ∙
        ( inv (eq-map-numerator-inv-denominator-hom-Rational-Ring R g x)))

  is-prop-rational-hom-Rational-Ring :
    ( R : Rational-Ring l) →
    is-prop (rational-hom-Rational-Ring R)
  is-prop-rational-hom-Rational-Ring R =
    is-prop-all-elements-equal (all-eq-rational-hom-Rational-Ring R)

  all-eq-rational-hom-Ring :
    ( R : Ring l) →
    ( f g : hom-Ring ring-ℚ R) →
    f ＝ g
  all-eq-rational-hom-Ring R f =
    all-eq-rational-hom-Rational-Ring
      ( R , is-rational-has-rational-hom-Ring R f)
      ( f)

  is-prop-rational-hom-Ring :
    ( R : Ring l) →
    is-prop (hom-Ring ring-ℚ R)
  is-prop-rational-hom-Ring R =
    is-prop-all-elements-equal (all-eq-rational-hom-Ring R)
```

### The type of ring endomorphisms of `ℚ` is contractible

```agda
is-contr-endo-hom-ring-ℚ : is-contr (hom-Ring ring-ℚ ring-ℚ)
is-contr-endo-hom-ring-ℚ =
  ( id-hom-Ring ring-ℚ) ,
  ( all-eq-rational-hom-Ring ring-ℚ (id-hom-Ring ring-ℚ))
```

### The initial ring map `ℚ → R` into a rational ring: `p/q ↦ (ι p)(ι q)⁻¹` where `ι : ℤ → R` is the initial ring homomorphism in `R`

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  map-initial-hom-Rational-Ring : ℚ → type-Rational-Ring R
  map-initial-hom-Rational-Ring x =
    mul-Ring
      ( ring-Rational-Ring R)
      ( map-initial-hom-Ring (ring-Rational-Ring R) (numerator-ℚ x))
      ( inv-positive-integer-Rational-Ring R (positive-denominator-ℚ x))

  integer-map-initial-hom-Rational-Ring : ℤ → type-Rational-Ring R
  integer-map-initial-hom-Rational-Ring k =
    map-initial-hom-Rational-Ring (rational-ℤ k)
```

### The initial ring map `ℚ → R` preserves one

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  preserves-one-initial-hom-Rational-Ring :
    map-initial-hom-Rational-Ring R one-ℚ ＝ one-Ring (ring-Rational-Ring R)
  preserves-one-initial-hom-Rational-Ring =
    is-right-inverse-inv-is-invertible-element-Ring
      ( ring-Rational-Ring R)
      ( is-invertible-positive-integer-Rational-Ring R one-ℤ⁺)
```

### The initial ring map `ℚ → R` coincides with the initial ring map `ℤ → R` on the integers

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  lemma-inv-positive-one-Rational-Ring :
    inv-positive-integer-Rational-Ring R one-ℤ⁺ ＝
    one-Ring (ring-Rational-Ring R)
  lemma-inv-positive-one-Rational-Ring =
    equational-reasoning
      inv-positive-integer-Rational-Ring R one-ℤ⁺
      ＝
        mul-Ring
          ( ring-Rational-Ring R)
          ( one-Ring (ring-Rational-Ring R))
          ( inv-positive-integer-Rational-Ring R one-ℤ⁺)
        by
          ( inv
            ( left-unit-law-mul-Ring
              ( ring-Rational-Ring R)
              ( inv-positive-integer-Rational-Ring R one-ℤ⁺)))
      ＝
        mul-Ring
          ( ring-Rational-Ring R)
          ( map-initial-hom-Ring (ring-Rational-Ring R) one-ℤ)
          ( inv-positive-integer-Rational-Ring R one-ℤ⁺)
        by
          ( ap
            ( mul-Ring'
              ( ring-Rational-Ring R)
              ( inv-positive-integer-Rational-Ring R one-ℤ⁺))
            ( inv (preserves-one-initial-hom-Ring (ring-Rational-Ring R))))
      ＝ one-Ring (ring-Rational-Ring R)
        by (preserves-one-initial-hom-Rational-Ring R)

  htpy-integer-map-initial-hom-Rational-Ring :
    integer-map-initial-hom-Rational-Ring R ~
    map-initial-hom-Ring (ring-Rational-Ring R)
  htpy-integer-map-initial-hom-Rational-Ring k =
    ( ap
      ( mul-Ring
        ( ring-Rational-Ring R)
        ( map-initial-hom-Ring (ring-Rational-Ring R) k))
      ( lemma-inv-positive-one-Rational-Ring)) ∙
    ( right-unit-law-mul-Ring
      ( ring-Rational-Ring R)
      ( map-initial-hom-Ring (ring-Rational-Ring R) k))

  eq-integer-map-initial-hom-Rational-Ring :
    integer-map-initial-hom-Rational-Ring R ＝
    map-initial-hom-Ring (ring-Rational-Ring R)
  eq-integer-map-initial-hom-Rational-Ring =
    eq-htpy htpy-integer-map-initial-hom-Rational-Ring
```

### The initial ring map `ℚ → R` preserves addition and multiplication on `ℤ`

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  preserves-add-integer-map-initial-hom-Rational-Ring :
    {k k' : ℤ} →
    integer-map-initial-hom-Rational-Ring R (k +ℤ k') ＝
    add-Ring
      ( ring-Rational-Ring R)
      ( integer-map-initial-hom-Rational-Ring R k)
      ( integer-map-initial-hom-Rational-Ring R k')
  preserves-add-integer-map-initial-hom-Rational-Ring {k} {k'} =
    inv-tr
      ( λ f →
        f (k +ℤ k') ＝
        add-Ring
          ( ring-Rational-Ring R)
          ( f k)
          ( f k'))
      ( eq-integer-map-initial-hom-Rational-Ring R)
      ( preserves-add-initial-hom-Ring
        ( ring-Rational-Ring R)
        ( k)
        ( k'))

  preserves-mul-integer-map-initial-hom-Rational-Ring :
    {k k' : ℤ} →
    integer-map-initial-hom-Rational-Ring R (k *ℤ k') ＝
    mul-Ring
      ( ring-Rational-Ring R)
      ( integer-map-initial-hom-Rational-Ring R k)
      ( integer-map-initial-hom-Rational-Ring R k')
  preserves-mul-integer-map-initial-hom-Rational-Ring {k} {k'} =
    inv-tr
      ( λ f →
        f (k *ℤ k') ＝
        mul-Ring
          ( ring-Rational-Ring R)
          ( f k)
          ( f k'))
      ( eq-integer-map-initial-hom-Rational-Ring R)
      ( preserves-mul-initial-hom-Ring
        ( ring-Rational-Ring R)
        ( k)
        ( k'))
```

### The initial ring map `ℚ → R` preserves reciprocals

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  lemma-reciprocal-map-initial-hom-Rational-Ring :
    (k : ℤ⁺) →
    map-initial-hom-Rational-Ring R (reciprocal-rational-ℤ⁺ k) ＝
    inv-positive-integer-Rational-Ring R k
  lemma-reciprocal-map-initial-hom-Rational-Ring k =
    ( ap-binary
      ( λ x y →
        mul-Ring
          ( ring-Rational-Ring R)
          ( map-initial-hom-Ring (ring-Rational-Ring R) x)
          ( inv-positive-integer-Rational-Ring R y))
      ( eq-numerator-reciprocal-rational-ℤ⁺ k)
      ( eq-positive-denominator-reciprocal-rational-ℤ⁺ k)) ∙
    ( ap
      ( mul-Ring'
        ( ring-Rational-Ring R)
        ( inv-positive-integer-Rational-Ring R k))
      ( preserves-one-initial-hom-Ring (ring-Rational-Ring R))) ∙
    ( left-unit-law-mul-Ring
      ( ring-Rational-Ring R)
      ( inv-positive-integer-Rational-Ring R k))
```

### The initial ring map `ℚ → R` is a ring homomorphism (TODO)

```agda
module _
  {l : Level} (R : Rational-Ring l)
  where

  postulate
    preserves-add-initial-hom-Rational-Ring :
      {x x' : ℚ} →
      map-initial-hom-Rational-Ring R (x +ℚ x') ＝
      add-Ring
        ( ring-Rational-Ring R)
        ( map-initial-hom-Rational-Ring R x)
        ( map-initial-hom-Rational-Ring R x')
  -- preserves-add-initial-hom-Rational-Ring {x} {x'} = {!!}
  --   where

  --   n = numerator-ℚ x
  --   d = denominator-ℚ x
  --   n' = numerator-ℚ x'
  --   d' = denominator-ℚ x'

  --   α :
  --     ( x +ℚ x') *ℚ (rational-ℤ d *ℚ rational-ℤ d') ＝
  --     (rational-ℤ n *ℚ rational-ℤ d') +ℚ (rational-ℤ n' *ℚ rational-ℤ d)
  --   α =
  --     ( right-distributive-mul-add-ℚ x x' (rational-ℤ d *ℚ rational-ℤ d')) ∙
  --     ( ap-binary
  --       ( add-ℚ)
  --       ( ( inv (associative-mul-ℚ x (rational-ℤ d) (rational-ℤ d'))) ∙
  --         ( ap (mul-ℚ' (rational-ℤ d')) (eq-numerator-mul-denominator-ℚ x)))
  --       ( ( ap (mul-ℚ x') (commutative-mul-ℚ (rational-ℤ d) (rational-ℤ d'))) ∙
  --         ( inv (associative-mul-ℚ x' (rational-ℤ d') (rational-ℤ d))) ∙
  --         ( ap (mul-ℚ' (rational-ℤ d)) (eq-numerator-mul-denominator-ℚ x'))))

  postulate
    preserves-mul-initial-hom-Rational-Ring :
      {x y : ℚ} →
      map-initial-hom-Rational-Ring R (x *ℚ y) ＝
      mul-Ring
        ( ring-Rational-Ring R)
        ( map-initial-hom-Rational-Ring R x)
        ( map-initial-hom-Rational-Ring R y)
    -- preserves-mul-initial-hom-Rational-Ring {x} {y} = {!!}

  initial-hom-Rational-Ring : rational-hom-Rational-Ring R
  pr1 initial-hom-Rational-Ring =
    ( map-initial-hom-Rational-Ring R ,
      preserves-add-initial-hom-Rational-Ring)
  pr2 initial-hom-Rational-Ring =
    ( preserves-mul-initial-hom-Rational-Ring ,
      preserves-one-initial-hom-Rational-Ring R)
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
    ( all-eq-rational-hom-Rational-Ring R (initial-hom-Rational-Ring R))
```
