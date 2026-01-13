# Magnitude of complex numbers

```agda
{-# OPTIONS --lossy-unification #-}

module complex-numbers.magnitude-complex-numbers where
```

<details><summary>Imports</summary>

```agda
open import complex-numbers.addition-complex-numbers
open import complex-numbers.complex-numbers
open import complex-numbers.conjugation-complex-numbers
open import complex-numbers.equivalence-complex-numbers-two-dimensional-vector-space-real-numbers
open import complex-numbers.multiplication-complex-numbers
open import complex-numbers.raising-universe-levels-complex-numbers
open import complex-numbers.similarity-complex-numbers
open import complex-numbers.zero-complex-numbers

open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.standard-euclidean-inner-product-spaces

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-nonnegative-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.multiplication-nonnegative-real-numbers
open import real-numbers.multiplication-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
open import real-numbers.sums-of-finite-sequences-of-real-numbers
open import real-numbers.zero-real-numbers
```

</details>

## Idea

The
{{#concept "magnitude" WD="magnitude of a complex number" WDID=Q3317982 Agda=magnitude-ℂ}}
of a [complex number](complex-numbers.complex-numbers.md) $a + bi$ is defined as
$\sqrt{a^2 + b^2}$.

## Definition

```agda
nonnegative-squared-magnitude-ℂ : {l : Level} → ℂ l → ℝ⁰⁺ l
nonnegative-squared-magnitude-ℂ (a +iℂ b) =
  nonnegative-square-ℝ a +ℝ⁰⁺ nonnegative-square-ℝ b

squared-magnitude-ℂ : {l : Level} → ℂ l → ℝ l
squared-magnitude-ℂ z = real-ℝ⁰⁺ (nonnegative-squared-magnitude-ℂ z)

nonnegative-magnitude-ℂ : {l : Level} → ℂ l → ℝ⁰⁺ l
nonnegative-magnitude-ℂ z = sqrt-ℝ⁰⁺ (nonnegative-squared-magnitude-ℂ z)

magnitude-ℂ : {l : Level} → ℂ l → ℝ l
magnitude-ℂ z = real-ℝ⁰⁺ (nonnegative-magnitude-ℂ z)
```

## Properties

### The square of the magnitude of `z` is the product of `z` and the conjugate of `z`

```agda
abstract
  eq-squared-magnitude-mul-conjugate-ℂ :
    {l : Level} (z : ℂ l) →
    z *ℂ conjugate-ℂ z ＝ complex-ℝ (squared-magnitude-ℂ z)
  eq-squared-magnitude-mul-conjugate-ℂ (a +iℂ b) =
    eq-ℂ
      ( equational-reasoning
        square-ℝ a -ℝ (b *ℝ neg-ℝ b)
        ＝ square-ℝ a -ℝ (neg-ℝ (square-ℝ b))
          by ap-diff-ℝ refl (right-negative-law-mul-ℝ _ _)
        ＝ square-ℝ a +ℝ square-ℝ b
          by ap-add-ℝ refl (neg-neg-ℝ _))
      ( eq-sim-ℝ
        ( similarity-reasoning-ℝ
          a *ℝ neg-ℝ b +ℝ b *ℝ a
          ~ℝ neg-ℝ (a *ℝ b) +ℝ a *ℝ b
            by
              sim-eq-ℝ
                ( ap-add-ℝ
                  ( right-negative-law-mul-ℝ a b)
                  ( commutative-mul-ℝ b a))
          ~ℝ zero-ℝ
            by left-inverse-law-add-ℝ (a *ℝ b)
          ~ℝ raise-ℝ _ zero-ℝ
            by sim-raise-ℝ _ _))
```

### The magnitude of `-z` is the magnitude of `z`

```agda
abstract
  squared-magnitude-neg-ℂ :
    {l : Level} (z : ℂ l) →
    squared-magnitude-ℂ (neg-ℂ z) ＝ squared-magnitude-ℂ z
  squared-magnitude-neg-ℂ (a +iℂ b) = ap-add-ℝ (square-neg-ℝ a) (square-neg-ℝ b)

  magnitude-neg-ℂ :
    {l : Level} (z : ℂ l) → magnitude-ℂ (neg-ℂ z) ＝ magnitude-ℂ z
  magnitude-neg-ℂ z =
    ap real-sqrt-ℝ⁰⁺ (eq-ℝ⁰⁺ _ _ (squared-magnitude-neg-ℂ z))
```

### The square of the magnitude of `zw` is the product of the squares of the magnitudes of `z` and `w`

```agda
abstract
  distributive-squared-magnitude-mul-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) →
    squared-magnitude-ℂ (z *ℂ w) ＝
    squared-magnitude-ℂ z *ℝ squared-magnitude-ℂ w
  distributive-squared-magnitude-mul-ℂ (a +iℂ b) (c +iℂ d) =
    equational-reasoning
      square-ℝ (a *ℝ c -ℝ b *ℝ d) +ℝ square-ℝ (a *ℝ d +ℝ b *ℝ c)
      ＝
        ( square-ℝ (a *ℝ c) +ℝ
          neg-ℝ (real-ℕ 2 *ℝ ((a *ℝ c) *ℝ (b *ℝ d))) +ℝ
          square-ℝ (b *ℝ d)) +ℝ
        ( square-ℝ (a *ℝ d) +ℝ
          real-ℕ 2 *ℝ ((a *ℝ d) *ℝ (b *ℝ c)) +ℝ
          square-ℝ (b *ℝ c))
        by
          ap-add-ℝ
            ( square-diff-ℝ _ _)
            ( square-add-ℝ _ _)
      ＝
        ( square-ℝ (a *ℝ c) +ℝ square-ℝ (b *ℝ d) +ℝ
          neg-ℝ (real-ℕ 2 *ℝ (a *ℝ c *ℝ (b *ℝ d)))) +ℝ
        ( square-ℝ (a *ℝ d) +ℝ square-ℝ (b *ℝ c) +ℝ
          real-ℕ 2 *ℝ ((a *ℝ d) *ℝ (b *ℝ c)))
        by
          ap-add-ℝ
            ( right-swap-add-ℝ _ _ _)
            ( right-swap-add-ℝ _ _ _)
      ＝
        ( ( square-ℝ (a *ℝ c) +ℝ square-ℝ (b *ℝ d)) +ℝ
          ( square-ℝ (a *ℝ d) +ℝ square-ℝ (b *ℝ c))) +ℝ
        ( neg-ℝ (real-ℕ 2 *ℝ ((a *ℝ c) *ℝ (b *ℝ d))) +ℝ
          real-ℕ 2 *ℝ ((a *ℝ d) *ℝ (b *ℝ c)))
        by interchange-law-add-add-ℝ _ _ _ _
      ＝
        ( ( square-ℝ (a *ℝ c) +ℝ square-ℝ (b *ℝ d)) +ℝ
          ( square-ℝ (a *ℝ d) +ℝ square-ℝ (b *ℝ c))) +ℝ
        ( neg-ℝ (real-ℕ 2 *ℝ (a *ℝ c *ℝ (b *ℝ d))) +ℝ
          real-ℕ 2 *ℝ (a *ℝ d *ℝ (c *ℝ b)))
        by
          ap-add-ℝ
            ( refl)
            ( ap-add-ℝ
              ( refl)
              ( ap-mul-ℝ refl (ap-mul-ℝ refl (commutative-mul-ℝ b c))))
      ＝
        ( ( square-ℝ (a *ℝ c) +ℝ square-ℝ (b *ℝ d)) +ℝ
          ( square-ℝ (a *ℝ d) +ℝ square-ℝ (b *ℝ c))) +ℝ
        ( neg-ℝ (real-ℕ 2 *ℝ (a *ℝ c *ℝ (b *ℝ d))) +ℝ
          real-ℕ 2 *ℝ (a *ℝ c *ℝ (d *ℝ b)))
        by
          ap-add-ℝ
            ( refl)
            ( ap-add-ℝ refl (ap-mul-ℝ refl (interchange-law-mul-mul-ℝ _ _ _ _)))
      ＝
        ( ( square-ℝ (a *ℝ c) +ℝ square-ℝ (b *ℝ d)) +ℝ
          ( square-ℝ (a *ℝ d) +ℝ square-ℝ (b *ℝ c))) +ℝ
        ( neg-ℝ (real-ℕ 2 *ℝ (a *ℝ c *ℝ (b *ℝ d))) +ℝ
          real-ℕ 2 *ℝ (a *ℝ c *ℝ (b *ℝ d)))
        by
          ap-add-ℝ
            ( refl)
            ( ap-add-ℝ
              ( refl)
              ( ap-mul-ℝ refl (ap-mul-ℝ refl (commutative-mul-ℝ d b))))
      ＝
        ( ( square-ℝ (a *ℝ c) +ℝ square-ℝ (b *ℝ d)) +ℝ
          ( square-ℝ (a *ℝ d) +ℝ square-ℝ (b *ℝ c))) +ℝ
        zero-ℝ
        by eq-sim-ℝ (preserves-sim-left-add-ℝ _ _ _ (left-inverse-law-add-ℝ _))
      ＝
        ( square-ℝ (a *ℝ c) +ℝ square-ℝ (b *ℝ d)) +ℝ
        ( square-ℝ (a *ℝ d) +ℝ square-ℝ (b *ℝ c))
        by right-unit-law-add-ℝ _
      ＝
        ( square-ℝ (a *ℝ c) +ℝ square-ℝ (a *ℝ d)) +ℝ
        ( square-ℝ (b *ℝ d) +ℝ square-ℝ (b *ℝ c))
        by interchange-law-add-add-ℝ _ _ _ _
      ＝
        ( square-ℝ a *ℝ square-ℝ c +ℝ square-ℝ a *ℝ square-ℝ d) +ℝ
        ( square-ℝ b *ℝ square-ℝ d +ℝ square-ℝ b *ℝ square-ℝ c)
        by
          ap-add-ℝ
            ( ap-add-ℝ
              ( distributive-square-mul-ℝ a c)
              ( distributive-square-mul-ℝ a d))
            ( ap-add-ℝ
              ( distributive-square-mul-ℝ b d)
              ( distributive-square-mul-ℝ b c))
      ＝
        square-ℝ a *ℝ (square-ℝ c +ℝ square-ℝ d) +ℝ
        square-ℝ b *ℝ (square-ℝ d +ℝ square-ℝ c)
        by
          inv
            ( ap-add-ℝ
              ( left-distributive-mul-add-ℝ _ _ _)
              ( left-distributive-mul-add-ℝ _ _ _))
      ＝
        square-ℝ a *ℝ (square-ℝ c +ℝ square-ℝ d) +ℝ
        square-ℝ b *ℝ (square-ℝ c +ℝ square-ℝ d)
        by ap-add-ℝ refl (ap-mul-ℝ refl (commutative-add-ℝ _ _))
      ＝
        (square-ℝ a +ℝ square-ℝ b) *ℝ (square-ℝ c +ℝ square-ℝ d)
        by
          inv
            ( right-distributive-mul-add-ℝ
              ( square-ℝ a)
              ( square-ℝ b)
              ( square-ℝ c +ℝ square-ℝ d))
```

### The magnitude of a real number as a complex number is its absolute value

```agda
abstract
  squared-magnitude-complex-ℝ :
    {l : Level} (x : ℝ l) → squared-magnitude-ℂ (complex-ℝ x) ＝ square-ℝ x
  squared-magnitude-complex-ℝ {l} x =
    equational-reasoning
      square-ℝ x +ℝ square-ℝ (raise-zero-ℝ l)
      ＝ square-ℝ x +ℝ raise-zero-ℝ l
        by ap-add-ℝ refl (square-raise-zero-ℝ l)
      ＝ square-ℝ x
        by right-raise-zero-law-add-ℝ (square-ℝ x)

  magnitude-complex-ℝ :
    {l : Level} (x : ℝ l) → magnitude-ℂ (complex-ℝ x) ＝ abs-ℝ x
  magnitude-complex-ℝ {l} x =
    ( ap real-sqrt-ℝ⁰⁺ (eq-ℝ⁰⁺ _ _ (squared-magnitude-complex-ℝ x))) ∙
    ( inv (eq-abs-sqrt-square-ℝ x))
```

### The magnitude of `zw` is the product of the magnitudes of `z` and `w`

```agda
abstract
  distributive-magnitude-mul-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) →
    magnitude-ℂ (z *ℂ w) ＝ magnitude-ℂ z *ℝ magnitude-ℂ w
  distributive-magnitude-mul-ℂ z w =
    equational-reasoning
      real-sqrt-ℝ⁰⁺ (nonnegative-squared-magnitude-ℂ (z *ℂ w))
      ＝
        real-sqrt-ℝ⁰⁺
          ( nonnegative-squared-magnitude-ℂ z *ℝ⁰⁺
            nonnegative-squared-magnitude-ℂ w)
        by
          ap
            ( real-sqrt-ℝ⁰⁺)
            ( eq-ℝ⁰⁺ _ _ (distributive-squared-magnitude-mul-ℂ z w))
      ＝ magnitude-ℂ z *ℝ magnitude-ℂ w
        by ap real-ℝ⁰⁺ (distributive-sqrt-mul-ℝ⁰⁺ _ _)
```

### The magnitude of a complex number multiplied on the left by a real number as a complex number

```agda
abstract
  magnitude-left-mul-complex-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (z : ℂ l2) →
    magnitude-ℂ (complex-ℝ x *ℂ z) ＝ abs-ℝ x *ℝ magnitude-ℂ z
  magnitude-left-mul-complex-ℝ x z =
    distributive-magnitude-mul-ℂ _ z ∙ ap-mul-ℝ (magnitude-complex-ℝ x) refl

  magnitude-left-mul-complex-ℝ⁺ :
    {l1 l2 : Level} (x : ℝ⁺ l1) (z : ℂ l2) →
    magnitude-ℂ (complex-ℝ⁺ x *ℂ z) ＝ real-ℝ⁺ x *ℝ magnitude-ℂ z
  magnitude-left-mul-complex-ℝ⁺ x⁺@(x , _) z =
    magnitude-left-mul-complex-ℝ x z ∙ ap-mul-ℝ (abs-real-ℝ⁺ x⁺) refl
```

### Similar complex numbers have similar magnitudes

```agda
abstract
  preserves-sim-squared-magnitude-ℂ :
    {l1 l2 : Level} {z : ℂ l1} {w : ℂ l2} →
    sim-ℂ z w → sim-ℝ (squared-magnitude-ℂ z) (squared-magnitude-ℂ w)
  preserves-sim-squared-magnitude-ℂ (a~c , b~d) =
    preserves-sim-add-ℝ
      ( preserves-sim-square-ℝ a~c)
      ( preserves-sim-square-ℝ b~d)

  preserves-sim-magnitude-ℂ :
    {l1 l2 : Level} {z : ℂ l1} {w : ℂ l2} →
    sim-ℂ z w → sim-ℝ (magnitude-ℂ z) (magnitude-ℂ w)
  preserves-sim-magnitude-ℂ z~w =
    preserves-sim-sqrt-ℝ⁰⁺ _ _ (preserves-sim-squared-magnitude-ℂ z~w)

  squared-magnitude-raise-ℂ :
    {l0 : Level} (l : Level) (z : ℂ l0) →
    squared-magnitude-ℂ (raise-ℂ l z) ＝ raise-ℝ l (squared-magnitude-ℂ z)
  squared-magnitude-raise-ℂ l z =
    eq-sim-ℝ
      ( similarity-reasoning-ℝ
        squared-magnitude-ℂ (raise-ℂ l z)
        ~ℝ squared-magnitude-ℂ z
          by preserves-sim-squared-magnitude-ℂ (sim-raise-ℂ' l z)
        ~ℝ raise-ℝ l (squared-magnitude-ℂ z)
          by sim-raise-ℝ l _)

  magnitude-raise-ℂ :
    {l0 : Level} (l : Level) (z : ℂ l0) →
    magnitude-ℂ (raise-ℂ l z) ＝ raise-ℝ l (magnitude-ℂ z)
  magnitude-raise-ℂ l z =
    eq-sim-ℝ
      ( similarity-reasoning-ℝ
        magnitude-ℂ (raise-ℂ l z)
        ~ℝ magnitude-ℂ z
          by preserves-sim-magnitude-ℂ (sim-raise-ℂ' l z)
        ~ℝ raise-ℝ l (magnitude-ℂ z)
          by sim-raise-ℝ l _)
```

### The magnitude of `one-ℂ` is `one-ℝ`

```agda
abstract
  squared-magnitude-one-ℂ : squared-magnitude-ℂ one-ℂ ＝ one-ℝ
  squared-magnitude-one-ℂ =
    equational-reasoning
      squared-magnitude-ℂ one-ℂ
      ＝ squared-magnitude-ℂ (complex-ℝ one-ℝ)
        by ap squared-magnitude-ℂ (inv eq-complex-one-ℝ)
      ＝ square-ℝ one-ℝ
        by squared-magnitude-complex-ℝ one-ℝ
      ＝ one-ℝ
        by right-unit-law-mul-ℝ one-ℝ

  magnitude-one-ℂ : magnitude-ℂ one-ℂ ＝ one-ℝ
  magnitude-one-ℂ =
    equational-reasoning
      magnitude-ℂ one-ℂ
      ＝ magnitude-ℂ (complex-ℝ one-ℝ)
        by ap magnitude-ℂ (inv eq-complex-one-ℝ)
      ＝ abs-ℝ one-ℝ
        by magnitude-complex-ℝ one-ℝ
      ＝ one-ℝ
        by abs-real-ℝ⁺ one-ℝ⁺
```

### The magnitude of `zero-ℂ` is `zero-ℝ`

```agda
abstract
  magnitude-zero-ℂ : magnitude-ℂ zero-ℂ ＝ zero-ℝ
  magnitude-zero-ℂ =
    ( ap magnitude-ℂ (inv eq-complex-zero-ℝ)) ∙
    ( magnitude-complex-ℝ zero-ℝ) ∙
    ( abs-zero-ℝ)
```

### The magnitude of `z` equals the Euclidean norm of the corresponding vector in `ℝ²`

```agda
abstract
  magnitude-complex-ℝ² :
    {l : Level} (z : ℂ l) →
    magnitude-ℂ z ＝ euclidean-norm-ℝ-Fin (complex-ℝ² z)
  magnitude-complex-ℝ² {l} z =
    ap real-sqrt-ℝ⁰⁺ (inv (eq-ℝ⁰⁺ _ _ (compute-sum-two-ℝ _)))
```

### The triangle inequality of magnitudes in `ℂ`

```agda
abstract
  triangular-level-magnitude-ℂ :
    (l : Level) (z w : ℂ l) →
    leq-ℝ (magnitude-ℂ (z +ℂ w)) (magnitude-ℂ z +ℝ magnitude-ℂ w)
  triangular-level-magnitude-ℂ l z w =
    binary-tr
      ( leq-ℝ)
      ( ( ap euclidean-norm-ℝ-Fin (inv (add-complex-ℝ² z w))) ∙
        ( inv (magnitude-complex-ℝ² _)))
      ( inv
        ( ap-add-ℝ
          ( magnitude-complex-ℝ² z)
          ( magnitude-complex-ℝ² w)))
      ( triangular-euclidean-norm-ℝ-Fin 2 (complex-ℝ² z) (complex-ℝ² w))

  triangular-magnitude-ℂ :
    {l1 l2 : Level} (z : ℂ l1) (w : ℂ l2) →
    leq-ℝ (magnitude-ℂ (z +ℂ w)) (magnitude-ℂ z +ℝ magnitude-ℂ w)
  triangular-magnitude-ℂ {l1} {l2} z w =
    preserves-leq-sim-ℝ
      ( preserves-sim-magnitude-ℂ
        ( preserves-sim-add-ℂ (sim-raise-ℂ' l2 z) (sim-raise-ℂ' l1 w)))
      ( preserves-sim-add-ℝ
        ( preserves-sim-magnitude-ℂ (sim-raise-ℂ' l2 z))
        ( preserves-sim-magnitude-ℂ (sim-raise-ℂ' l1 w)))
      ( triangular-level-magnitude-ℂ
        ( l1 ⊔ l2)
        ( raise-ℂ l2 z)
        ( raise-ℂ l1 w))
```

### If `|z| = 0`, `z = 0`

```agda
abstract
  is-extensional-magnitude-ℂ :
    {l : Level} (z : ℂ l) → is-zero-ℝ (magnitude-ℂ z) → is-zero-ℂ z
  is-extensional-magnitude-ℂ z |z|=0 =
    is-zero-eq-raise-zero-ℂ
      ( ( inv (is-retraction-inv-complex-ℝ² z)) ∙
        ( ap
          ( inv-complex-ℝ²)
          ( is-extensional-euclidean-norm-ℝ-Fin 2
            ( complex-ℝ² z)
            ( tr is-zero-ℝ (magnitude-complex-ℝ² z) |z|=0))))
```

### The magnitude of `-z` is equal to the magnitude of `z`

```agda
abstract
  squared-magnitude-neg-ℂ :
    {l : Level} (z : ℂ l) →
    squared-magnitude-ℂ (neg-ℂ z) ＝ squared-magnitude-ℂ z
  squared-magnitude-neg-ℂ (a +iℂ b) = ap-add-ℝ (square-neg-ℝ a) (square-neg-ℝ b)

  magnitude-neg-ℂ :
    {l : Level} (z : ℂ l) → magnitude-ℂ (neg-ℂ z) ＝ magnitude-ℂ z
  magnitude-neg-ℂ z = ap real-sqrt-ℝ⁰⁺ (eq-ℝ⁰⁺ _ _ (squared-magnitude-neg-ℂ z))
```

## See also

- [Distances between complex numbers](complex-numbers.distance-complex-numbers.md)
- [Absolute values of real numbers](real-numbers.absolute-value-real-numbers.md)

## External links

- [Absolute values of complex numbers](https://en.wikipedia.org/wiki/Absolute_value#Complex_numbers)
  on Wikipedia
