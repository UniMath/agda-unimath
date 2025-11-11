# Nonzero real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.nonzero-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.transport-along-identifications
open import foundation.universe-levels
open import foundation.functoriality-disjunction

open import real-numbers.absolute-value-real-numbers
open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.negative-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.positive-and-negative-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.square-roots-nonnegative-real-numbers
open import real-numbers.squares-real-numbers
open import real-numbers.strict-inequalities-addition-and-subtraction-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

A [real number](real-numbers.dedekind-real-numbers.md) is
{{#concept "nonzero" Disambiguation="Dedekind real numbers" Agda=is-nonzero-ℝ}}
if it is [apart](real-numbers.apartness-real-numbers.md) from zero, or
equivalently if it is [negative](real-numbers.negative-real-numbers.md)
[or](foundation.disjunction.md)
[positive](real-numbers.positive-real-numbers.md).

## Definition

```agda
is-nonzero-prop-ℝ : {l : Level} → ℝ l → Prop l
is-nonzero-prop-ℝ x = is-negative-prop-ℝ x ∨ is-positive-prop-ℝ x

is-nonzero-ℝ : {l : Level} → ℝ l → UU l
is-nonzero-ℝ x = type-Prop (is-nonzero-prop-ℝ x)

nonzero-ℝ : (l : Level) → UU (lsuc l)
nonzero-ℝ l = type-subtype (is-nonzero-prop-ℝ {l})

real-nonzero-ℝ : {l : Level} → nonzero-ℝ l → ℝ l
real-nonzero-ℝ = inclusion-subtype is-nonzero-prop-ℝ

is-nonzero-real-nonzero-ℝ :
  {l : Level} (x : nonzero-ℝ l) → is-nonzero-ℝ (real-nonzero-ℝ x)
is-nonzero-real-nonzero-ℝ = pr2
```

## Properties

### Positive real numbers are nonzero

```agda
is-nonzero-is-positive-ℝ :
  {l : Level} {x : ℝ l} → is-positive-ℝ x → is-nonzero-ℝ x
is-nonzero-is-positive-ℝ = inr-disjunction

nonzero-ℝ⁺ : {l : Level} → ℝ⁺ l → nonzero-ℝ l
nonzero-ℝ⁺ (x , is-pos-x) = (x , inr-disjunction is-pos-x)
```

### Negative real numbers are nonzero

```agda
is-nonzero-is-negative-ℝ :
  {l : Level} {x : ℝ l} → is-negative-ℝ x → is-nonzero-ℝ x
is-nonzero-is-negative-ℝ = inl-disjunction

nonzero-ℝ⁻ : {l : Level} → ℝ⁻ l → nonzero-ℝ l
nonzero-ℝ⁻ (x , is-neg-x) = (x , inl-disjunction is-neg-x)
```

### Characterization of equality

```agda
eq-nonzero-ℝ :
  {l : Level} (x y : nonzero-ℝ l) → (real-nonzero-ℝ x ＝ real-nonzero-ℝ y) →
  x ＝ y
eq-nonzero-ℝ _ _ = eq-type-subtype is-nonzero-prop-ℝ
```

### The nonzero difference of a pair of real numbers `x` and `y` such that `x < y`

```agda
nonzero-diff-le-ℝ :
  {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → le-ℝ x y → nonzero-ℝ (l1 ⊔ l2)
nonzero-diff-le-ℝ {x = x} {y = y} x<y = nonzero-ℝ⁺ (positive-diff-le-ℝ x<y)
```

### The nonzero difference of a pair of real numbers `x` and `y` such that `|x| < y`

```agda
nonzero-diff-le-abs-ℝ :
  {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → le-ℝ (abs-ℝ x) y → nonzero-ℝ (l1 ⊔ l2)
nonzero-diff-le-abs-ℝ {x = x} {y = y} |x|<y =
  nonzero-diff-le-ℝ (concatenate-leq-le-ℝ x (abs-ℝ x) y (leq-abs-ℝ x) |x|<y)
```

### `x` is nonzero if and only if `|x|` is positive

```agda
module _
  {l : Level} (x : ℝ l)
  where

  abstract opaque
    unfolding abs-ℝ

    is-positive-abs-is-nonzero-ℝ : is-nonzero-ℝ x → is-positive-ℝ (abs-ℝ x)
    is-positive-abs-is-nonzero-ℝ =
      elim-disjunction
        ( is-positive-prop-ℝ (abs-ℝ x))
        ( λ is-neg-x →
          inv-tr
            ( is-positive-ℝ)
            ( abs-real-ℝ⁻ (x , is-neg-x))
            ( neg-is-negative-ℝ x is-neg-x))
        ( λ is-pos-x →
          inv-tr
            ( is-positive-ℝ)
            ( abs-real-ℝ⁺ (x , is-pos-x))
            ( is-pos-x))

    is-nonzero-is-positive-abs-ℝ : is-positive-ℝ (abs-ℝ x) → is-nonzero-ℝ x
    is-nonzero-is-positive-abs-ℝ 0<|x| =
      let
        open do-syntax-trunc-Prop (is-nonzero-prop-ℝ x)
      in do
        (ε , 0+ε<|x|) ← exists-positive-rational-separation-le-ℝ 0<|x|
        let
          0<|x|-ε = le-transpose-left-add-ℝ zero-ℝ (real-ℚ⁺ ε) (abs-ℝ x) 0+ε<|x|
        elim-disjunction
          ( is-nonzero-prop-ℝ x)
          ( λ |x|-ε<x →
            is-nonzero-is-positive-ℝ (transitive-le-ℝ _ _ _ |x|-ε<x 0<|x|-ε))
          ( λ |x|-ε<-x →
            is-nonzero-is-negative-ℝ
              ( binary-tr
                ( le-ℝ)
                ( neg-neg-ℝ x)
                ( neg-zero-ℝ)
                ( transitive-le-ℝ _ _ _
                  ( neg-le-ℝ 0<|x|-ε)
                  ( neg-le-ℝ |x|-ε<-x))))
          ( approximate-below-abs-ℝ x ε)
```

### `x` is nonzero if and only if `x²` is positive

```agda
module _
  {l : Level} (x : ℝ l)
  where

  abstract
    is-positive-square-is-nonzero-ℝ :
      is-nonzero-ℝ x → is-positive-ℝ (square-ℝ x)
    is-positive-square-is-nonzero-ℝ =
      elim-disjunction
        ( is-positive-prop-ℝ (square-ℝ x))
        ( λ is-neg-x → is-positive-square-ℝ⁻ (x , is-neg-x))
        ( λ is-pos-x → is-positive-square-ℝ⁺ (x , is-pos-x))

    is-nonzero-square-is-positive-ℝ :
      is-positive-ℝ (square-ℝ x) → is-nonzero-ℝ x
    is-nonzero-square-is-positive-ℝ 0<x² =
      is-nonzero-is-positive-abs-ℝ
        ( x)
        ( tr
          ( is-positive-ℝ)
          ( equational-reasoning
            real-sqrt-ℝ⁰⁺ (nonnegative-ℝ⁺ (square-ℝ x , 0<x²))
            ＝ real-sqrt-ℝ⁰⁺ (nonnegative-square-ℝ x)
              by
                ap
                  ( real-sqrt-ℝ⁰⁺)
                  ( eq-ℝ⁰⁺
                    ( nonnegative-ℝ⁺ (square-ℝ x , 0<x²))
                    ( nonnegative-square-ℝ x)
                    ( refl))
            ＝ abs-ℝ x by inv (eq-abs-sqrt-square-ℝ x))
          ( is-positive-sqrt-is-positive-ℝ⁰⁺ _ 0<x²))
```

### Being nonzero is preserved by similarity

```agda
abstract
  is-nonzero-sim-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} →
    sim-ℝ x y → is-nonzero-ℝ x → is-nonzero-ℝ y
  is-nonzero-sim-ℝ x~y =
    map-disjunction (is-negative-sim-ℝ x~y) (is-positive-sim-ℝ x~y)
```
