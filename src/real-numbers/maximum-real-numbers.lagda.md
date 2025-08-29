# The maximum of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.maximum-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import metric-spaces.metric-space-of-short-functions-metric-spaces
open import metric-spaces.short-functions-metric-spaces

open import order-theory.large-join-semilattices
open import order-theory.least-upper-bounds-large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.maximum-lower-dedekind-real-numbers
open import real-numbers.maximum-upper-dedekind-real-numbers
open import real-numbers.metric-space-of-real-numbers
open import real-numbers.positive-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
open import real-numbers.upper-dedekind-real-numbers
```

</details>

## Idea

The
{{#concept "maximum" Disambiguation="binary, Dedekind real numbers" Agda=max-ℝ WD="maximum" WDID=Q10578722}}
of two [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) `x` and
`y` is the Dedekind real number `max-ℝ x y` with lower cut equal to the union of
`x` and `y`'s lower cuts, and upper cut equal to the intersection of their upper
cuts.

For any `x : ℝ`, `max-ℝ x` is a
[short function](metric-spaces.short-functions-metric-spaces.md) `ℝ → ℝ` for the
[standard real metric structure](real-numbers.metric-space-of-real-numbers.md).
Moreover, the map `x ↦ max-ℝ x` is a short function from `ℝ` into the
[metric space of short functions](metric-spaces.metric-space-of-short-functions-metric-spaces.md)
of `ℝ`.

## Definition

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  lower-real-max-ℝ : lower-ℝ (l1 ⊔ l2)
  lower-real-max-ℝ = binary-max-lower-ℝ (lower-real-ℝ x) (lower-real-ℝ y)

  upper-real-max-ℝ : upper-ℝ (l1 ⊔ l2)
  upper-real-max-ℝ = binary-max-upper-ℝ (upper-real-ℝ x) (upper-real-ℝ y)

  abstract
    is-disjoint-lower-upper-max-ℝ :
      is-disjoint-lower-upper-ℝ lower-real-max-ℝ upper-real-max-ℝ
    is-disjoint-lower-upper-max-ℝ q (q<x∨q<y , x<q , y<q) =
      elim-disjunction
        ( empty-Prop)
        ( λ q<x → is-disjoint-cut-ℝ x q (q<x , x<q))
        ( λ q<y → is-disjoint-cut-ℝ y q (q<y , y<q))
        ( q<x∨q<y)

    is-located-lower-upper-max-ℝ :
      is-located-lower-upper-ℝ lower-real-max-ℝ upper-real-max-ℝ
    is-located-lower-upper-max-ℝ p q p<q =
      elim-disjunction
        ( claim)
        ( λ p<x → inl-disjunction (inl-disjunction p<x))
        ( λ x<q →
          elim-disjunction
            ( claim)
            ( λ p<y → inl-disjunction (inr-disjunction p<y))
            ( λ y<q → inr-disjunction (x<q , y<q))
            ( is-located-lower-upper-cut-ℝ y p q p<q))
        ( is-located-lower-upper-cut-ℝ x p q p<q)
      where
        claim : Prop (l1 ⊔ l2)
        claim =
          cut-lower-ℝ lower-real-max-ℝ p ∨
          cut-upper-ℝ upper-real-max-ℝ q

  opaque
    max-ℝ : ℝ (l1 ⊔ l2)
    max-ℝ =
      real-lower-upper-ℝ
        ( lower-real-max-ℝ)
        ( upper-real-max-ℝ)
        ( is-disjoint-lower-upper-max-ℝ)
        ( is-located-lower-upper-max-ℝ)
```

## Properties

### The binary maximum is a least upper bound

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    unfolding max-ℝ

    is-least-binary-upper-bound-max-ℝ :
      is-least-binary-upper-bound-Large-Poset
        ( ℝ-Large-Poset)
        ( x)
        ( y)
        ( max-ℝ x y)
    is-least-binary-upper-bound-max-ℝ z =
      is-least-binary-upper-bound-binary-max-lower-ℝ
        ( lower-real-ℝ x)
        ( lower-real-ℝ y)
        ( lower-real-ℝ z)

    leq-max-leq-leq-ℝ :
      {l3 : Level} (z : ℝ l3) → leq-ℝ x z → leq-ℝ y z → leq-ℝ (max-ℝ x y) z
    leq-max-leq-leq-ℝ z x≤z y≤z =
      forward-implication (is-least-binary-upper-bound-max-ℝ z) (x≤z , y≤z)
```

### The binary maximum is a binary upper bound

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    leq-left-max-ℝ : leq-ℝ x (max-ℝ x y)
    leq-left-max-ℝ =
      pr1
        ( is-binary-upper-bound-is-least-binary-upper-bound-Large-Poset
          ( ℝ-Large-Poset)
          ( x)
          ( y)
          ( is-least-binary-upper-bound-max-ℝ x y))

    leq-right-max-ℝ : leq-ℝ y (max-ℝ x y)
    leq-right-max-ℝ =
      pr2
        ( is-binary-upper-bound-is-least-binary-upper-bound-Large-Poset
          ( ℝ-Large-Poset)
          ( x)
          ( y)
          ( is-least-binary-upper-bound-max-ℝ x y))
```

### The binary maximum is commutative

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    unfolding sim-ℝ

    commutative-max-ℝ : max-ℝ x y ＝ max-ℝ y x
    commutative-max-ℝ =
      eq-sim-ℝ
        ( sim-is-least-binary-upper-bound-Large-Poset
          ( ℝ-Large-Poset)
          ( x)
          ( y)
          ( is-least-binary-upper-bound-max-ℝ x y)
          ( is-binary-least-upper-bound-swap-Large-Poset
            ( ℝ-Large-Poset)
            ( y)
            ( x)
            ( max-ℝ y x)
            ( is-least-binary-upper-bound-max-ℝ y x)))
```

### The large poset of real numbers has joins

```agda
has-joins-ℝ-Large-Poset : has-joins-Large-Poset ℝ-Large-Poset
join-has-joins-Large-Poset has-joins-ℝ-Large-Poset = max-ℝ
is-least-binary-upper-bound-join-has-joins-Large-Poset
  has-joins-ℝ-Large-Poset = is-least-binary-upper-bound-max-ℝ
```

### The binary maximum preserves similarity

```agda
abstract
  preserves-sim-max-ℝ :
    {l1 l2 l3 l4 : Level} →
    (a : ℝ l1) (a' : ℝ l2) → sim-ℝ a a' →
    (b : ℝ l3) (b' : ℝ l4) → sim-ℝ b b' →
    sim-ℝ (max-ℝ a b) (max-ℝ a' b')
  preserves-sim-max-ℝ a a' a~a' b b' b~b' =
    sim-sim-leq-ℝ
      ( sim-is-least-binary-upper-bound-Large-Poset
        ( ℝ-Large-Poset)
        ( a)
        ( b)
        ( is-least-binary-upper-bound-max-ℝ a b)
        ( preserves-is-least-binary-upper-bound-sim-Large-Poset
          ( ℝ-Large-Poset)
          ( a')
          ( b')
          ( max-ℝ a' b')
          ( sim-leq-sim-ℝ (symmetric-sim-ℝ a~a'))
          ( sim-leq-sim-ℝ (symmetric-sim-ℝ b~b'))
          ( is-least-binary-upper-bound-max-ℝ a' b')))

  preserves-sim-left-max-ℝ :
    {l1 l2 l3 : Level} →
    (a : ℝ l1) (a' : ℝ l2) → sim-ℝ a a' →
    (b : ℝ l3) →
    sim-ℝ (max-ℝ a b) (max-ℝ a' b)
  preserves-sim-left-max-ℝ a a' a~a' b =
    preserves-sim-max-ℝ a a' a~a' b b (refl-sim-ℝ b)

  preserves-sim-right-max-ℝ :
    {l1 l2 l3 : Level} →
    (a : ℝ l1) →
    (b : ℝ l2) (b' : ℝ l3) → sim-ℝ b b' →
    sim-ℝ (max-ℝ a b) (max-ℝ a b')
  preserves-sim-right-max-ℝ a = preserves-sim-max-ℝ a a (refl-sim-ℝ a)
```

### The binary maximum preserves lower neighborhoods

```agda
module _
  {l1 l2 l3 : Level} (d : ℚ⁺)
  (x : ℝ l1) (y : ℝ l2) (z : ℝ l3)
  where

  preserves-lower-neighborhood-leq-left-max-ℝ :
    leq-ℝ y (z +ℝ real-ℚ (rational-ℚ⁺ d)) →
    leq-ℝ
      ( max-ℝ x y)
      ( (max-ℝ x z) +ℝ real-ℚ (rational-ℚ⁺ d))
  preserves-lower-neighborhood-leq-left-max-ℝ z≤y+d =
    leq-is-least-binary-upper-bound-Large-Poset
      ( ℝ-Large-Poset)
      ( x)
      ( y)
      ( is-least-binary-upper-bound-max-ℝ x y)
      ( (max-ℝ x z) +ℝ real-ℚ (rational-ℚ⁺ d))
      ( ( transitive-leq-ℝ
          ( x)
          ( max-ℝ x z)
          ( max-ℝ x z +ℝ real-ℚ (rational-ℚ⁺ d))
          ( leq-le-ℝ
            ( max-ℝ x z)
            ( max-ℝ x z +ℝ real-ℚ (rational-ℚ⁺ d))
            ( le-left-add-real-ℝ⁺
              ( max-ℝ x z)
              ( positive-real-ℚ⁺ d)))
          ( leq-left-max-ℝ x z)) ,
        ( transitive-leq-ℝ
          ( y)
          ( z +ℝ real-ℚ (rational-ℚ⁺ d))
          ( max-ℝ x z +ℝ real-ℚ (rational-ℚ⁺ d))
          ( preserves-leq-right-add-ℝ
            ( real-ℚ (rational-ℚ⁺ d))
            ( z)
            ( max-ℝ x z)
            ( leq-right-max-ℝ x z))
          ( z≤y+d)))

  preserves-lower-neighborhood-leq-right-max-ℝ :
    leq-ℝ y (z +ℝ real-ℚ (rational-ℚ⁺ d)) →
    leq-ℝ
      ( max-ℝ y x)
      ( (max-ℝ z x) +ℝ real-ℚ (rational-ℚ⁺ d))
  preserves-lower-neighborhood-leq-right-max-ℝ z≤y+d =
    binary-tr
      ( λ u v → leq-ℝ u (v +ℝ real-ℚ (rational-ℚ⁺ d)))
      ( commutative-max-ℝ x y)
      ( commutative-max-ℝ x z)
      ( preserves-lower-neighborhood-leq-left-max-ℝ z≤y+d)
```

### The maximum with a real number is a short function `ℝ → ℝ`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1)
  where

  is-short-function-left-max-ℝ :
    is-short-function-Metric-Space
      ( metric-space-ℝ l2)
      ( metric-space-ℝ (l1 ⊔ l2))
      ( max-ℝ x)
  is-short-function-left-max-ℝ d y z Nyz =
    neighborhood-real-bound-each-leq-ℝ
      ( d)
      ( max-ℝ x y)
      ( max-ℝ x z)
      ( preserves-lower-neighborhood-leq-left-max-ℝ d x y z
        ( left-leq-real-bound-neighborhood-ℝ d y z Nyz))
      ( preserves-lower-neighborhood-leq-left-max-ℝ d x z y
        ( right-leq-real-bound-neighborhood-ℝ d y z Nyz))

  short-left-max-ℝ :
    short-function-Metric-Space
      ( metric-space-ℝ l2)
      ( metric-space-ℝ (l1 ⊔ l2))
  short-left-max-ℝ =
    (max-ℝ x , is-short-function-left-max-ℝ)
```

### The binary maximum is a short function from `ℝ` to the metric space of short functions `ℝ → ℝ`

```agda
module _
  {l1 l2 : Level}
  where

  is-short-function-short-left-max-ℝ :
    is-short-function-Metric-Space
      ( metric-space-ℝ l1)
      ( metric-space-of-short-functions-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2)))
      ( short-left-max-ℝ)
  is-short-function-short-left-max-ℝ d x y Nxy z =
    neighborhood-real-bound-each-leq-ℝ
      ( d)
      ( max-ℝ x z)
      ( max-ℝ y z)
      ( preserves-lower-neighborhood-leq-right-max-ℝ d z x y
        ( left-leq-real-bound-neighborhood-ℝ d x y Nxy))
      ( preserves-lower-neighborhood-leq-right-max-ℝ d z y x
        ( right-leq-real-bound-neighborhood-ℝ d x y Nxy))

  short-max-ℝ :
    short-function-Metric-Space
      ( metric-space-ℝ l1)
      ( metric-space-of-short-functions-Metric-Space
        ( metric-space-ℝ l2)
        ( metric-space-ℝ (l1 ⊔ l2)))
  short-max-ℝ =
    (short-left-max-ℝ , is-short-function-short-left-max-ℝ)
```

### For any `ε : ℚ⁺`, `(max-ℝ x y - ε < x) ∨ (max-ℝ x y - ε < y)`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  approximate-below-max-ℝ :
    (ε : ℚ⁺) →
    type-disjunction-Prop
      ( le-ℝ-Prop (max-ℝ x y -ℝ real-ℚ⁺ ε) x)
      ( le-ℝ-Prop (max-ℝ x y -ℝ real-ℚ⁺ ε) y)
  approximate-below-max-ℝ ε⁺@(ε , _) =
    let
      motive =
        ( le-ℝ-Prop (max-ℝ x y -ℝ real-ℚ ε) x) ∨
        ( le-ℝ-Prop (max-ℝ x y -ℝ real-ℚ ε) y)
      open do-syntax-trunc-Prop motive
    in do
      (q , max-ε<q , q<max) ←
        dense-rational-le-ℝ
          ( max-ℝ x y -ℝ real-ℚ ε)
          ( max-ℝ x y)
          ( le-diff-real-ℝ⁺ (max-ℝ x y) (positive-real-ℚ⁺ ε⁺))
      (r , q-<ℝ-r , r<max) ← dense-rational-le-ℝ (real-ℚ q) (max-ℝ x y) q<max
      let q<r = reflects-le-real-ℚ q r q-<ℝ-r
      elim-disjunction motive
        ( λ q<x →
          inl-disjunction
            ( transitive-le-ℝ
              ( max-ℝ x y -ℝ real-ℚ ε)
              ( real-ℚ q)
              ( x)
              ( le-real-is-in-lower-cut-ℚ q x q<x)
              ( max-ε<q)))
        ( λ x<r →
          elim-disjunction motive
            ( λ q<y →
              inr-disjunction
                ( transitive-le-ℝ
                  ( max-ℝ x y -ℝ real-ℚ ε)
                  ( real-ℚ q)
                  ( y)
                  ( le-real-is-in-lower-cut-ℚ q y q<y)
                  ( max-ε<q)))
            ( λ y<r →
              ex-falso
                ( irreflexive-le-ℝ
                  ( max-ℝ x y)
                  ( concatenate-leq-le-ℝ (max-ℝ x y) (real-ℚ r) (max-ℝ x y)
                    ( leq-max-leq-leq-ℝ x y (real-ℚ r)
                      ( leq-le-ℝ x (real-ℚ r)
                        ( le-real-is-in-upper-cut-ℚ r x x<r))
                      ( leq-le-ℝ y (real-ℚ r)
                        ( le-real-is-in-upper-cut-ℚ r y y<r)))
                    ( r<max))))
            ( is-located-lower-upper-cut-ℝ y q r q<r))
        ( is-located-lower-upper-cut-ℝ x q r q<r)
```
