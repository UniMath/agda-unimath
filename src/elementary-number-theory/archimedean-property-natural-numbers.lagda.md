# The Archimedean property of the natural numbers

```agda
module elementary-number-theory.archimedean-property-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.euclidean-division-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.multiplication-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.nonzero-natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.torsorial-type-families
open import foundation.transport-along-identifications
open import foundation.uniqueness-quantification
open import foundation.universe-levels
```

</details>

## Ideas

The
{{#concept "Archimedean property" Disambiguation="natural numbers" Agda=archimedean-property-ℕ}}
of the [natural numbers](elementary-number-theory.natural-numbers.md) is that
for any nonzero natural number `x` and any natural number `y`, there is an
`n : ℕ` such that `y < n *ℕ x`.

More precisely, for any nonzero natural number `x` and any natural number `y`,
there exists a unique `n : ℕ` such that `n *ℕ x ≤ y < (n + 1) *ℕ x`; this is the
{{#concept "Archimedean modulus" Agda=center-archimedean-modulus-ℕ}} of `y` with
respect to `x`. All natural numbers greater than the Archimedean modulus are
witnesses of the Archimedean property.

## Definition

### Archimedean modulus of a natural number with respect to a nonzero natural number

```agda
module _
  (x y : ℕ) (H : is-nonzero-ℕ x)
  where

  is-archimedean-modulus-prop-ℕ : ℕ → Prop lzero
  is-archimedean-modulus-prop-ℕ n =
    product-Prop
      ( leq-ℕ-Prop (n *ℕ x) y)
      ( le-ℕ-Prop y (succ-ℕ n *ℕ x))

  is-archimedean-modulus-ℕ : ℕ → UU lzero
  is-archimedean-modulus-ℕ n =
    type-Prop (is-archimedean-modulus-prop-ℕ n)

  type-archimedean-modulus-ℕ : UU lzero
  type-archimedean-modulus-ℕ = type-subtype is-archimedean-modulus-prop-ℕ
```

## Properties

### All Archimedean moduli are equal

```agda
module _
  (x y : ℕ) (H : is-nonzero-ℕ x)
  where

  not-le-is-archimedean-modulus-ℕ :
    (m n : ℕ) →
    is-archimedean-modulus-ℕ x y H m →
    is-archimedean-modulus-ℕ x y H n →
    ¬ (le-ℕ n m)
  not-le-is-archimedean-modulus-ℕ m n Hm Hn n<m =
    contradiction-le-ℕ
      ( m *ℕ x)
      ( succ-ℕ n *ℕ x)
      ( concatenate-leq-le-ℕ
        { m *ℕ x}
        { y}
        { succ-ℕ n *ℕ x}
        ( pr1 Hm)
        ( pr2 Hn))
      ( preserves-leq-left-mul-ℕ
        ( x)
        ( succ-ℕ n)
        ( m)
        ( leq-succ-le-ℕ n m n<m))

  all-leq-is-archimidean-modulus-ℕ :
    (m n : ℕ) →
    is-archimedean-modulus-ℕ x y H m →
    is-archimedean-modulus-ℕ x y H n →
    m ≤-ℕ n
  all-leq-is-archimidean-modulus-ℕ m n Hm Hn =
    rec-coproduct
      ( ex-falso ∘ not-le-is-archimedean-modulus-ℕ m n Hm Hn)
      ( id)
      ( decide-le-leq-ℕ n m)

  all-eq-is-archimedean-modulus-ℕ :
    (m n : ℕ) →
    is-archimedean-modulus-ℕ x y H m →
    is-archimedean-modulus-ℕ x y H n →
    m ＝ n
  all-eq-is-archimedean-modulus-ℕ m n Hm Hn =
    antisymmetric-leq-ℕ
      ( m)
      ( n)
      ( all-leq-is-archimidean-modulus-ℕ m n Hm Hn)
      ( all-leq-is-archimidean-modulus-ℕ n m Hn Hm)
```

### The Euclidean quotient of `y` by `x` is the Archimedean modulus of `y` with respect to `x`

```agda
module _
  (x y : ℕ) (H : is-nonzero-ℕ x)
  where

  is-archimedean-modulus-euclidean-quotient-ℕ :
    is-archimedean-modulus-ℕ x y H (quotient-euclidean-division-ℕ x y)
  pr1 is-archimedean-modulus-euclidean-quotient-ℕ =
    tr
      ( leq-ℕ (quotient-euclidean-division-ℕ x y *ℕ x))
      ( eq-euclidean-division-ℕ x y)
      ( leq-add-ℕ
        ( quotient-euclidean-division-ℕ x y *ℕ x)
        ( remainder-euclidean-division-ℕ x y))
  pr2 is-archimedean-modulus-euclidean-quotient-ℕ =
    tr
      ( λ u → le-ℕ u ((quotient-euclidean-division-ℕ x y *ℕ x) +ℕ x))
      ( eq-euclidean-division-ℕ x y)
      ( preserves-le-left-add-ℕ
        ( quotient-euclidean-division-ℕ x y *ℕ x)
        ( remainder-euclidean-division-ℕ x y)
        ( x)
        ( strict-upper-bound-remainder-euclidean-division-ℕ x y H))
```

### The type family of Archimedean moduli is torsorial

```agda
module _
  (x y : ℕ) (H : is-nonzero-ℕ x)
  where

  is-prop-archimedean-modulus-ℕ : is-prop (type-archimedean-modulus-ℕ x y H)
  is-prop-archimedean-modulus-ℕ =
    is-prop-all-elements-equal
      ( λ u v →
        eq-type-subtype
          ( is-archimedean-modulus-prop-ℕ x y H)
          ( all-eq-is-archimedean-modulus-ℕ
            ( x)
            ( y)
            ( H)
            ( pr1 u)
            ( pr1 v)
            ( pr2 u)
            ( pr2 v)))

  archimedean-modulus-prop-ℕ : Prop lzero
  archimedean-modulus-prop-ℕ =
    (type-archimedean-modulus-ℕ x y H , is-prop-archimedean-modulus-ℕ)

  torsorial-archimedean-modulus-ℕ :
    is-torsorial (is-archimedean-modulus-ℕ x y H)
  torsorial-archimedean-modulus-ℕ =
    ( ( quotient-euclidean-division-ℕ x y) ,
      ( is-archimedean-modulus-euclidean-quotient-ℕ x y H)) ,
    ( λ x → eq-is-prop is-prop-archimedean-modulus-ℕ)
```

### The unique Archimedean modulus of a natural number with respect to a nonzero natural number

```agda
module _
  (x y : ℕ) (H : is-nonzero-ℕ x)
  where

  center-archimedean-modulus-ℕ : type-archimedean-modulus-ℕ x y H
  center-archimedean-modulus-ℕ =
    center (torsorial-archimedean-modulus-ℕ x y H)

  nat-archimedean-modulus-ℕ : ℕ
  nat-archimedean-modulus-ℕ = pr1 center-archimedean-modulus-ℕ

  is-modulus-nat-archimedean-modulus-ℕ :
    is-archimedean-modulus-ℕ x y H nat-archimedean-modulus-ℕ
  is-modulus-nat-archimedean-modulus-ℕ = pr2 center-archimedean-modulus-ℕ

  leq-left-nat-archimedean-modulus-ℕ :
    leq-ℕ (nat-archimedean-modulus-ℕ *ℕ x) y
  leq-left-nat-archimedean-modulus-ℕ = pr1 is-modulus-nat-archimedean-modulus-ℕ

  le-right-nat-archimedean-modulus-ℕ :
    le-ℕ y ((succ-ℕ nat-archimedean-modulus-ℕ) *ℕ x)
  le-right-nat-archimedean-modulus-ℕ = pr2 is-modulus-nat-archimedean-modulus-ℕ
```

### The Archimedean property of the natural numbers

```agda
abstract
  bound-archimedean-property-ℕ :
    (x y : ℕ) → is-nonzero-ℕ x → Σ ℕ (λ n → le-ℕ y (n *ℕ x))
  bound-archimedean-property-ℕ x y nonzero-x =
    ( succ-ℕ (nat-archimedean-modulus-ℕ x y nonzero-x)) ,
    ( le-right-nat-archimedean-modulus-ℕ x y nonzero-x)

  archimedean-property-ℕ :
    (x y : ℕ) → is-nonzero-ℕ x → exists ℕ (λ n → le-ℕ-Prop y (n *ℕ x))
  archimedean-property-ℕ x y nonzero-x =
    unit-trunc-Prop (bound-archimedean-property-ℕ x y nonzero-x)
```

## External links

- [Archimedean property](https://en.wikipedia.org/wiki/Archimedean_property) at
  Wikipedia
