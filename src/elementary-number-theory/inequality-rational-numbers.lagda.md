# Inequality on the rational numbers

```agda
module elementary-number-theory.inequality-rational-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.cross-multiplication-difference-integer-fractions
open import elementary-number-theory.difference-integers
open import elementary-number-theory.inequality-integer-fractions
open import elementary-number-theory.inequality-integers
open import elementary-number-theory.integer-fractions
open import elementary-number-theory.integers
open import elementary-number-theory.mediant-integer-fractions
open import elementary-number-theory.multiplication-integers
open import elementary-number-theory.nonnegative-integers
open import elementary-number-theory.nonpositive-integers
open import elementary-number-theory.positive-and-negative-integers
open import elementary-number-theory.positive-integers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.reduced-integer-fractions
open import elementary-number-theory.strict-inequality-integers

open import foundation.binary-relations
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-propositions
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.posets
open import order-theory.preorders
```

</details>

## Idea

A rational number `x` is less (or equal) to a rational number `y` if and only if
the underlying fraction of `x` is less (or equal) than the underlying fraction
of `y`.

## Definition

### Inequality on the rational numbers

```agda
leq-ℚ-Prop : ℚ → ℚ → Prop lzero
leq-ℚ-Prop (x , px) (y , py) = leq-fraction-ℤ-Prop x y

leq-ℚ : ℚ → ℚ → UU lzero
leq-ℚ x y = type-Prop (leq-ℚ-Prop x y)

is-prop-leq-ℚ : (x y : ℚ) → is-prop (leq-ℚ x y)
is-prop-leq-ℚ x y = is-prop-type-Prop (leq-ℚ-Prop x y)

infix 30 _≤-ℚ_
_≤-ℚ_ = leq-ℚ
```

### Strict inequality on the rational numbers

```agda
le-ℚ-Prop : ℚ → ℚ → Prop lzero
le-ℚ-Prop (x , px) (y , py) = le-fraction-ℤ-Prop x y

le-ℚ : ℚ → ℚ → UU lzero
le-ℚ x y = type-Prop (le-ℚ-Prop x y)

is-prop-le-ℚ : (x y : ℚ) → is-prop (le-ℚ x y)
is-prop-le-ℚ x y = is-prop-type-Prop (le-ℚ-Prop x y)
```

## Properties

### Inequality of rational numbers is decidable

```agda
is-decidable-leq-ℚ : (x y : ℚ) → (leq-ℚ x y) + ¬ (leq-ℚ x y)
is-decidable-leq-ℚ x y =
  is-decidable-leq-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)

leq-ℚ-Decidable-Prop : (x y : ℚ) → Decidable-Prop lzero
leq-ℚ-Decidable-Prop x y =
  ( leq-ℚ x y ,
    is-prop-leq-ℚ x y ,
    is-decidable-leq-ℚ x y)
```

### Strict inequality of rational numbers is decidable

```agda
is-decidable-le-ℚ : (x y : ℚ) → (le-ℚ x y) + ¬ (le-ℚ x y)
is-decidable-le-ℚ x y =
  is-decidable-le-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)

le-ℚ-Decidable-Prop : (x y : ℚ) → Decidable-Prop lzero
le-ℚ-Decidable-Prop x y =
  ( le-ℚ x y ,
    is-prop-le-ℚ x y ,
    is-decidable-le-ℚ x y)
```

### Strict inequality on rationals implies inequality

```agda
leq-le-ℚ : {x y : ℚ} → le-ℚ x y → leq-ℚ x y
leq-le-ℚ {x} {y} = leq-le-fraction-ℤ {fraction-ℚ x} {fraction-ℚ y}
```

### Inequality on rational numbers is reflexive

```agda
refl-leq-ℚ : (x : ℚ) → leq-ℚ x x
refl-leq-ℚ x =
  refl-leq-ℤ (numerator-ℚ x *ℤ denominator-ℚ x)
```

### Inequality on rational numbers is antisymmetric

```agda
antisymmetric-leq-ℚ : (x y : ℚ) → leq-ℚ x y → leq-ℚ y x → x ＝ y
antisymmetric-leq-ℚ x y H H' =
  ( inv (in-fraction-fraction-ℚ x)) ∙
  ( eq-ℚ-sim-fractions-ℤ
    ( fraction-ℚ x)
    ( fraction-ℚ y)
    ( is-sim-antisymmetric-leq-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( H)
      ( H'))) ∙
  ( in-fraction-fraction-ℚ y)
```

### The ordering of the rational numbers is linear

```agda
linear-leq-ℚ : (x y : ℚ) → (leq-ℚ x y) + (leq-ℚ y x)
linear-leq-ℚ x y =
  map-coproduct
    ( id)
    ( is-nonnegative-eq-ℤ
      (distributive-neg-diff-ℤ
        ( numerator-ℚ y *ℤ denominator-ℚ x)
        ( numerator-ℚ x *ℤ denominator-ℚ y)))
    ( decide-is-nonnegative-is-nonnegative-neg-ℤ
      { cross-mul-diff-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y)})
```

### Strict inequality on rationals is asymmetric

```agda
asymmetric-le-ℚ : (x y : ℚ) → le-ℚ x y → ¬ (le-ℚ y x)
asymmetric-le-ℚ x y =
  asymmetric-le-fraction-ℤ
    ( fraction-ℚ x)
    ( fraction-ℚ y)

irreflexive-le-ℚ : (x : ℚ) → ¬ (le-ℚ x x)
irreflexive-le-ℚ =
  is-irreflexive-is-asymmetric le-ℚ asymmetric-le-ℚ
```

### Transitivity properties

```agda
module _
  (x y z : ℚ)
  where

  transitive-leq-ℚ : leq-ℚ y z → leq-ℚ x y → leq-ℚ x z
  transitive-leq-ℚ =
    transitive-leq-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( fraction-ℚ z)

  transitive-le-ℚ : le-ℚ y z → le-ℚ x y → le-ℚ x z
  transitive-le-ℚ =
    transitive-le-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( fraction-ℚ z)

  concatenate-le-leq-ℚ : le-ℚ x y → leq-ℚ y z → le-ℚ x z
  concatenate-le-leq-ℚ =
    concatenate-le-leq-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( fraction-ℚ z)

  concatenate-leq-le-ℚ : leq-ℚ x y → le-ℚ y z → le-ℚ x z
  concatenate-leq-le-ℚ =
    concatenate-leq-le-fraction-ℤ
      ( fraction-ℚ x)
      ( fraction-ℚ y)
      ( fraction-ℚ z)
```

### Strict inequality on the rational numbers reflects strict inequality on the underlying fractions

```agda
module _
  (x : ℚ) (p : fraction-ℤ)
  where

  right-le-ℚ-in-fraction-ℤ-le-fraction-ℤ :
    le-fraction-ℤ (fraction-ℚ x) p →
    le-ℚ x (in-fraction-ℤ p)
  right-le-ℚ-in-fraction-ℤ-le-fraction-ℤ H =
    concatenate-le-sim-fraction-ℤ
      ( fraction-ℚ x)
      ( p)
      ( fraction-ℚ ( in-fraction-ℤ p))
      ( H)
      ( sim-reduced-fraction-ℤ p)

  left-le-ℚ-in-fraction-ℤ-le-fraction-ℤ :
    le-fraction-ℤ p (fraction-ℚ x) →
    le-ℚ (in-fraction-ℤ p) x
  left-le-ℚ-in-fraction-ℤ-le-fraction-ℤ =
    concatenate-sim-le-fraction-ℤ
      ( fraction-ℚ ( in-fraction-ℤ p))
      ( p)
      ( fraction-ℚ x)
      ( symmetric-sim-fraction-ℤ
        ( p)
        ( fraction-ℚ ( in-fraction-ℤ p))
        ( sim-reduced-fraction-ℤ p))
```

### The rational numbers have no lower or upper bound

```agda
module _
  (x : ℚ)
  where

  left-∃-le-ℚ : ∃ ℚ (λ q → le-ℚ q x)
  left-∃-le-ℚ = intro-∃
    ( in-fraction-ℤ frac)
    ( left-le-ℚ-in-fraction-ℤ-le-fraction-ℤ x frac
      ( le-fraction-le-numerator-fraction-ℤ
        ( frac)
        ( fraction-ℚ x)
        ( refl)
        ( le-pred-ℤ (numerator-ℚ x))))
    where
    frac : fraction-ℤ
    frac = pred-ℤ (numerator-ℚ x) , positive-denominator-ℚ x

  right-∃-le-ℚ : ∃ ℚ (λ r → le-ℚ x r)
  right-∃-le-ℚ = intro-∃
    ( in-fraction-ℤ frac)
    ( right-le-ℚ-in-fraction-ℤ-le-fraction-ℤ x frac
      ( le-fraction-le-numerator-fraction-ℤ
        ( fraction-ℚ x)
        ( frac)
        ( refl)
        ( le-succ-ℤ (numerator-ℚ x))))
    where
    frac : fraction-ℤ
    frac = succ-ℤ (numerator-ℚ x) , positive-denominator-ℚ x
```

### Decidability of strict inequality on the rationals

```agda
decide-le-leq-ℚ : (x y : ℚ) → le-ℚ x y + leq-ℚ y x
decide-le-leq-ℚ x y =
  map-coproduct
    ( id)
    ( λ H →
      is-nonnegative-eq-ℤ
        ( skew-commutative-cross-mul-diff-fraction-ℤ
          ( fraction-ℚ x)
          ( fraction-ℚ y))
        ( is-nonnegative-neg-is-nonpositive-ℤ H))
    ( decide-is-positive-is-nonpositive-ℤ)
```

It remains to fully formalize that strict inequality is decidable.

### Trichotomy on the rationals

```agda
trichotomy-le-ℚ :
  {l : Level} {A : UU l} (x y : ℚ) →
  ( le-ℚ x y → A) →
  ( Id x y → A) →
  ( le-ℚ y x → A) →
  A
trichotomy-le-ℚ x y left eq right with decide-le-leq-ℚ x y | decide-le-leq-ℚ y x
... | inl I | _ = left I
... | inr I | inl I' = right I'
... | inr I | inr I' = eq (antisymmetric-leq-ℚ x y I' I)
```

### The mediant of two rationals is between them

```agda
module _
  (x y : ℚ) (H : le-ℚ x y)
  where

  le-left-mediant-ℚ : le-ℚ x (mediant-ℚ x y)
  le-left-mediant-ℚ =
    right-le-ℚ-in-fraction-ℤ-le-fraction-ℤ x
      ( mediant-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
      ( le-left-mediant-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y) H)

  le-right-mediant-ℚ : le-ℚ (mediant-ℚ x y) y
  le-right-mediant-ℚ =
    left-le-ℚ-in-fraction-ℤ-le-fraction-ℤ y
      ( mediant-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y))
      ( le-right-mediant-fraction-ℤ (fraction-ℚ x) (fraction-ℚ y) H)
```

### Strict inequality on the rationals is dense

```agda
module _
  (x y : ℚ) (H : le-ℚ x y)
  where

  dense-le-ℚ : ∃ ℚ (λ r → le-ℚ x r × le-ℚ r y)
  dense-le-ℚ =
    intro-∃
      ( mediant-ℚ x y)
      ( le-left-mediant-ℚ x y H , le-right-mediant-ℚ x y H)
```

### The strict order on the rationals is located

```agda
located-le-ℚ : (x y z : ℚ) → le-ℚ y z → (le-ℚ-Prop y x) ∨ (le-ℚ-Prop x z)
located-le-ℚ x y z H =
  unit-trunc-Prop
    ( map-coproduct
      ( id)
      ( λ p → concatenate-leq-le-ℚ x y z p H)
      ( decide-le-leq-ℚ y x))
```

### The partially ordered set of rational numbers

```agda
ℚ-Preorder : Preorder lzero lzero
ℚ-Preorder =
  (ℚ , leq-ℚ-Prop , refl-leq-ℚ , transitive-leq-ℚ)

ℚ-Poset : Poset lzero lzero
ℚ-Poset = (ℚ-Preorder , antisymmetric-leq-ℚ)
```

## See also

- The decidable total order on the rational numbers is defined in
  [`decidable-total-order-rational-numbers](elementary-number-theory.decidable-total-order-rational-numbers.md)
