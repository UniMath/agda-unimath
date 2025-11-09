# The binary maximum of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.binary-maximum-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.inequality-rational-numbers
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.empty-types
open import foundation.functoriality-disjunction
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.join-semilattices
open import order-theory.large-join-semilattices
open import order-theory.least-upper-bounds-large-posets

open import real-numbers.addition-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequalities-addition-and-subtraction-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.lower-dedekind-real-numbers
open import real-numbers.maximum-lower-dedekind-real-numbers
open import real-numbers.maximum-upper-dedekind-real-numbers
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
          map-disjunction
            ( λ p<y → inr-disjunction p<y)
            ( x<q ,_)
            ( is-located-lower-upper-cut-ℝ y p<q))
        ( is-located-lower-upper-cut-ℝ x p<q)
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

ap-max-ℝ :
  {l1 l2 : Level} → {x x' : ℝ l1} → x ＝ x' →
  {y y' : ℝ l2} → y ＝ y' → max-ℝ x y ＝ max-ℝ x' y'
ap-max-ℝ = ap-binary max-ℝ
```

## Properties

### The binary maximum is a least upper bound

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  abstract opaque
    unfolding leq-ℝ max-ℝ

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
abstract opaque
  unfolding leq-ℝ sim-ℝ

  commutative-max-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → max-ℝ x y ＝ max-ℝ y x
  commutative-max-ℝ x y =
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

### The real numbers at a specific universe level are a join semilattice

```agda
ℝ-Order-Theoretic-Join-Semilattice :
  (l : Level) → Order-Theoretic-Join-Semilattice (lsuc l) l
ℝ-Order-Theoretic-Join-Semilattice l =
  ( ℝ-Poset l , λ x y → (max-ℝ x y , is-least-binary-upper-bound-max-ℝ x y))
```

### The binary maximum of real numbers is idempotent

```agda
abstract
  is-idempotent-max-ℝ : {l : Level} (x : ℝ l) → max-ℝ x x ＝ x
  is-idempotent-max-ℝ x =
    idempotent-join-Order-Theoretic-Join-Semilattice
      ( ℝ-Order-Theoretic-Join-Semilattice _)
      ( x)
```

### The maximum with a real number is idempotent

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    is-idempotent-left-max-ℝ : max-ℝ x (max-ℝ x y) ＝ max-ℝ x y
    is-idempotent-left-max-ℝ =
      antisymmetric-leq-ℝ
        ( max-ℝ x (max-ℝ x y))
        ( max-ℝ x y)
        ( leq-max-leq-leq-ℝ
          ( x)
          ( max-ℝ x y)
          ( max-ℝ x y)
          ( leq-left-max-ℝ x y)
          ( refl-leq-ℝ (max-ℝ x y)))
        ( leq-right-max-ℝ x (max-ℝ x y))

    is-idempotent-right-max-ℝ : max-ℝ (max-ℝ x y) y ＝ max-ℝ x y
    is-idempotent-right-max-ℝ =
      antisymmetric-leq-ℝ
        ( max-ℝ (max-ℝ x y) y)
        ( max-ℝ x y)
        ( leq-max-leq-leq-ℝ
          ( max-ℝ x y)
          ( y)
          ( max-ℝ x y)
          ( refl-leq-ℝ (max-ℝ x y))
          ( leq-right-max-ℝ x y))
        ( leq-left-max-ℝ (max-ℝ x y) y)
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

### If `x ≤ y`, the maximum of `x` and `y` is similar to `y`

```agda
abstract
  left-leq-right-max-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → leq-ℝ x y →
    sim-ℝ (max-ℝ x y) y
  left-leq-right-max-ℝ {x = x} {y = y} x≤y =
    sim-sim-leq-ℝ
      ( sim-is-least-binary-upper-bound-Large-Poset ℝ-Large-Poset x y
        ( is-least-binary-upper-bound-max-ℝ x y)
        ( left-leq-right-least-upper-bound-Large-Poset ℝ-Large-Poset x y x≤y))

  right-leq-left-max-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → leq-ℝ y x →
    sim-ℝ (max-ℝ x y) x
  right-leq-left-max-ℝ {x = x} {y = y} y≤x =
    sim-sim-leq-ℝ
      ( sim-is-least-binary-upper-bound-Large-Poset ℝ-Large-Poset x y
        ( is-least-binary-upper-bound-max-ℝ x y)
        ( right-leq-left-least-upper-bound-Large-Poset ℝ-Large-Poset x y y≤x))
```

### For any `ε : ℚ⁺`, `(max-ℝ x y - ε < x) ∨ (max-ℝ x y - ε < y)`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    approximate-below-max-ℝ :
      (ε : ℚ⁺) →
      disjunction-type
        ( le-ℝ (max-ℝ x y -ℝ real-ℚ⁺ ε) x)
        ( le-ℝ (max-ℝ x y -ℝ real-ℚ⁺ ε) y)
    approximate-below-max-ℝ ε⁺@(ε , _) =
      let
        motive =
          ( le-prop-ℝ (max-ℝ x y -ℝ real-ℚ ε) x) ∨
          ( le-prop-ℝ (max-ℝ x y -ℝ real-ℚ ε) y)
        open do-syntax-trunc-Prop motive
      in do
        (q , max-ε<q , q<max) ←
          dense-rational-le-ℝ
            ( max-ℝ x y -ℝ real-ℚ ε)
            ( max-ℝ x y)
            ( le-diff-real-ℝ⁺ (max-ℝ x y) (positive-real-ℚ⁺ ε⁺))
        (r , q-<ℝ-r , r<max) ← dense-rational-le-ℝ (real-ℚ q) (max-ℝ x y) q<max
        let q<r = reflects-le-real-ℚ q-<ℝ-r
        map-disjunction
          ( λ q<x →
            transitive-le-ℝ
              ( max-ℝ x y -ℝ real-ℚ ε)
              ( real-ℚ q)
              ( x)
              ( le-real-is-in-lower-cut-ℚ x q<x)
              ( max-ε<q))
          ( λ x<r →
            elim-disjunction
              ( le-prop-ℝ (max-ℝ x y -ℝ real-ℚ ε) y)
              ( λ q<y →
                transitive-le-ℝ
                  ( max-ℝ x y -ℝ real-ℚ ε)
                  ( real-ℚ q)
                  ( y)
                  ( le-real-is-in-lower-cut-ℚ y q<y)
                  ( max-ε<q))
              ( λ y<r →
                ex-falso
                  ( irreflexive-le-ℝ
                    ( max-ℝ x y)
                    ( concatenate-leq-le-ℝ (max-ℝ x y) (real-ℚ r) (max-ℝ x y)
                      ( leq-max-leq-leq-ℝ x y (real-ℚ r)
                        ( leq-le-ℝ (le-real-is-in-upper-cut-ℚ x x<r))
                        ( leq-le-ℝ (le-real-is-in-upper-cut-ℚ y y<r)))
                      ( r<max))))
              ( is-located-lower-upper-cut-ℝ y q<r))
          ( is-located-lower-upper-cut-ℝ x q<r)
```

### If `x < z` and `y < z`, then `max-ℝ x y < x`

```agda
abstract
  le-max-le-le-ℝ :
    {l1 l2 l3 : Level} {x : ℝ l1} {y : ℝ l2} {z : ℝ l3} → le-ℝ x z → le-ℝ y z →
    le-ℝ (max-ℝ x y) z
  le-max-le-le-ℝ {x = x} {y = y} {z = z} x<z y<z =
    let open do-syntax-trunc-Prop (le-prop-ℝ (max-ℝ x y) z)
    in do
      (p , x<p , p<z) ← dense-rational-le-ℝ x z x<z
      (q , y<q , q<z) ← dense-rational-le-ℝ y z y<z
      rec-coproduct
        ( λ p≤q →
          concatenate-leq-le-ℝ
            ( max-ℝ x y)
            ( real-ℚ q)
            ( z)
            ( leq-max-leq-leq-ℝ
              ( x)
              ( y)
              ( real-ℚ q)
              ( transitive-leq-ℝ
                ( x)
                ( real-ℚ p)
                ( real-ℚ q)
                ( preserves-leq-real-ℚ p≤q)
                ( leq-le-ℝ x<p))
              ( leq-le-ℝ y<q))
            ( q<z))
        ( λ q≤p →
          concatenate-leq-le-ℝ
            ( max-ℝ x y)
            ( real-ℚ p)
            ( z)
            ( leq-max-leq-leq-ℝ
              ( x)
              ( y)
              ( real-ℚ p)
              ( leq-le-ℝ x<p)
              ( transitive-leq-ℝ
                ( y)
                ( real-ℚ q)
                ( real-ℚ p)
                ( preserves-leq-real-ℚ q≤p)
                ( leq-le-ℝ y<q)))
            ( p<z))
        ( linear-leq-ℚ p q)
```
