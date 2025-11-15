# The binary minimum of real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.binary-minimum-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers

open import foundation.action-on-identifications-binary-functions
open import foundation.action-on-identifications-functions
open import foundation.binary-transport
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-meet-semilattices
open import order-theory.meet-semilattices

open import real-numbers.addition-real-numbers
open import real-numbers.binary-maximum-real-numbers
open import real-numbers.dedekind-real-numbers
open import real-numbers.difference-real-numbers
open import real-numbers.inequality-real-numbers
open import real-numbers.negation-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The
{{#concept "minimum" Disambiguation="binary, Dedekind real numbers" Agda=min-ℝ WD="minimum" WDID=Q10585806}}
of two [Dedekind real numbers](real-numbers.dedekind-real-numbers.md) `x` and
`y` is their
[greatest lower bound](order-theory.greatest-lower-bounds-large-posets.md).

## Definition

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  opaque
    min-ℝ : ℝ (l1 ⊔ l2)
    min-ℝ = neg-ℝ (max-ℝ (neg-ℝ x) (neg-ℝ y))

ap-min-ℝ :
  {l1 l2 : Level} → {x x' : ℝ l1} → x ＝ x' →
  {y y' : ℝ l2} → y ＝ y' → min-ℝ x y ＝ min-ℝ x' y'
ap-min-ℝ = ap-binary min-ℝ
```

## Properties

### The binary minimum is a greatest lower bound

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  abstract opaque
    unfolding leq-ℝ min-ℝ

    is-greatest-binary-lower-bound-min-ℝ :
      is-greatest-binary-lower-bound-Large-Poset
        ( ℝ-Large-Poset)
        ( x)
        ( y)
        ( min-ℝ x y)
    pr1 (is-greatest-binary-lower-bound-min-ℝ z) (z≤x , z≤y) =
      tr
        ( λ w → leq-ℝ w (min-ℝ x y))
        ( neg-neg-ℝ z)
        ( neg-leq-ℝ
          ( leq-max-leq-leq-ℝ _ _ (neg-ℝ z) (neg-leq-ℝ z≤x) (neg-leq-ℝ z≤y)))
    pr2 (is-greatest-binary-lower-bound-min-ℝ z) z≤min =
      let
        case :
          {l : Level} (w : ℝ l) → leq-ℝ (neg-ℝ w) (max-ℝ (neg-ℝ x) (neg-ℝ y)) →
          leq-ℝ z w
        case w -w≤max =
          transitive-leq-ℝ z (min-ℝ x y) w
            ( tr
              ( leq-ℝ (min-ℝ x y))
              ( neg-neg-ℝ _)
              ( neg-leq-ℝ -w≤max))
            ( z≤min)
      in (case x (leq-left-max-ℝ _ _) , case y (leq-right-max-ℝ _ _))

  abstract
    leq-min-leq-leq-ℝ :
      {l3 : Level} (z : ℝ l3) → leq-ℝ z x → leq-ℝ z y → leq-ℝ z (min-ℝ x y)
    leq-min-leq-leq-ℝ z x≤z y≤z =
      forward-implication (is-greatest-binary-lower-bound-min-ℝ z) (x≤z , y≤z)
```

### The binary minimum is a binary lower bound

```agda
module _
  {l1 l2 : Level}
  (x : ℝ l1) (y : ℝ l2)
  where

  abstract
    leq-left-min-ℝ : leq-ℝ (min-ℝ x y) x
    leq-left-min-ℝ =
      pr1
        ( is-binary-lower-bound-is-greatest-binary-lower-bound-Large-Poset
          ( ℝ-Large-Poset)
          ( x)
          ( y)
          ( is-greatest-binary-lower-bound-min-ℝ x y))

    leq-right-min-ℝ : leq-ℝ (min-ℝ x y) y
    leq-right-min-ℝ =
      pr2
        ( is-binary-lower-bound-is-greatest-binary-lower-bound-Large-Poset
          ( ℝ-Large-Poset)
          ( x)
          ( y)
          ( is-greatest-binary-lower-bound-min-ℝ x y))
```

### The binary minimum is commutative

```agda
abstract opaque
  unfolding min-ℝ

  commutative-min-ℝ :
    {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2) → min-ℝ x y ＝ min-ℝ y x
  commutative-min-ℝ x y =
    ap neg-ℝ (commutative-max-ℝ (neg-ℝ x) (neg-ℝ y))
```

### The large poset of real numbers has meets

```agda
has-meets-ℝ-Large-Poset : has-meets-Large-Poset ℝ-Large-Poset
meet-has-meets-Large-Poset has-meets-ℝ-Large-Poset = min-ℝ
is-greatest-binary-lower-bound-meet-has-meets-Large-Poset
  has-meets-ℝ-Large-Poset = is-greatest-binary-lower-bound-min-ℝ
```

### The real numbers at a specific universe level are a meet semilattice

```agda
ℝ-Order-Theoretic-Meet-Semilattice :
  (l : Level) → Order-Theoretic-Meet-Semilattice (lsuc l) l
ℝ-Order-Theoretic-Meet-Semilattice l =
  ( ℝ-Poset l , λ x y → (min-ℝ x y , is-greatest-binary-lower-bound-min-ℝ x y))
```

### For any `ε : ℚ⁺`, `(x < min-ℝ x y + ε) ∨ (y < min-ℝ x y + ε)`

```agda
module _
  {l1 l2 : Level} (x : ℝ l1) (y : ℝ l2)
  where

  abstract opaque
    unfolding min-ℝ

    approximate-above-min-ℝ :
      (ε : ℚ⁺) →
      type-disjunction-Prop
        ( le-prop-ℝ x (min-ℝ x y +ℝ real-ℚ⁺ ε))
        ( le-prop-ℝ y (min-ℝ x y +ℝ real-ℚ⁺ ε))
    approximate-above-min-ℝ ε =
      let
        case :
          {l : Level} → (w : ℝ l) →
          le-ℝ (max-ℝ (neg-ℝ x) (neg-ℝ y) -ℝ real-ℚ⁺ ε) (neg-ℝ w) →
          le-ℝ w (min-ℝ x y +ℝ real-ℚ⁺ ε)
        case w max-ε<-w =
          binary-tr
            ( le-ℝ)
            ( neg-neg-ℝ w)
            ( distributive-neg-diff-ℝ _ _ ∙ commutative-add-ℝ _ _)
            ( neg-le-ℝ max-ε<-w)
      in
        elim-disjunction
          ( (le-prop-ℝ x (min-ℝ x y +ℝ real-ℚ⁺ ε)) ∨
            (le-prop-ℝ y (min-ℝ x y +ℝ real-ℚ⁺ ε)))
          ( λ max-ε<-x → inl-disjunction (case x max-ε<-x))
          ( λ max-ε<-y → inr-disjunction (case y max-ε<-y))
          ( approximate-below-max-ℝ (neg-ℝ x) (neg-ℝ y) ε)
```

### If `x ≤ y`, the minimum of `x` and `y` is similar to `x`

```agda
abstract opaque
  unfolding min-ℝ

  left-leq-right-min-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → leq-ℝ x y →
    sim-ℝ (min-ℝ x y) x
  left-leq-right-min-ℝ {x = x} {y = y} x≤y =
    similarity-reasoning-ℝ
      min-ℝ x y
      ~ℝ neg-ℝ (neg-ℝ x)
        by preserves-sim-neg-ℝ (right-leq-left-max-ℝ (neg-leq-ℝ x≤y))
      ~ℝ x
        by sim-eq-ℝ (neg-neg-ℝ x)

  right-leq-left-min-ℝ :
    {l1 l2 : Level} {x : ℝ l1} {y : ℝ l2} → leq-ℝ y x →
    sim-ℝ (min-ℝ x y) y
  right-leq-left-min-ℝ {y = y} y≤x =
    tr (λ z → sim-ℝ z y) (commutative-min-ℝ _ _) (left-leq-right-min-ℝ y≤x)
```

### If `x < y` and `x < z`, then `x < min-ℝ y z`

```agda
abstract opaque
  unfolding min-ℝ

  le-min-le-le-ℝ :
    {l1 l2 l3 : Level} {x : ℝ l1} {y : ℝ l2} {z : ℝ l3} → le-ℝ x y → le-ℝ x z →
    le-ℝ x (min-ℝ y z)
  le-min-le-le-ℝ {x = x} {y = y} {z = z} x<y x<z =
    tr
      ( λ w → le-ℝ w (min-ℝ y z))
      ( neg-neg-ℝ x)
      ( neg-le-ℝ (le-max-le-le-ℝ (neg-le-ℝ x<y) (neg-le-ℝ x<z)))
```
