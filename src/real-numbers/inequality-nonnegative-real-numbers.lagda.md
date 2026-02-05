# Inequality of nonnegative real numbers

```agda
{-# OPTIONS --lossy-unification #-}

module real-numbers.inequality-nonnegative-real-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.positive-rational-numbers
open import elementary-number-theory.rational-numbers
open import elementary-number-theory.strict-inequality-rational-numbers

open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.universe-levels

open import order-theory.bottom-elements-large-posets
open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.posets

open import real-numbers.inequality-real-numbers
open import real-numbers.nonnegative-real-numbers
open import real-numbers.raising-universe-levels-real-numbers
open import real-numbers.rational-real-numbers
open import real-numbers.similarity-nonnegative-real-numbers
open import real-numbers.similarity-real-numbers
open import real-numbers.strict-inequality-real-numbers
```

</details>

## Idea

The
{{#concept "standard ordering" Disambiguation="on the nonnegative real numbers" Agda=leq-ℝ⁰⁺}}
on the [nonnegative real numbers](real-numbers.nonnegative-real-numbers.md) is
inherited from the [standard ordering](real-numbers.inequality-real-numbers.md)
on [real numbers](real-numbers.dedekind-real-numbers.md).

## Definition

```agda
module _
  {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2)
  where

  leq-prop-ℝ⁰⁺ : Prop (l1 ⊔ l2)
  leq-prop-ℝ⁰⁺ = leq-prop-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y)

  leq-ℝ⁰⁺ : UU (l1 ⊔ l2)
  leq-ℝ⁰⁺ = type-Prop leq-prop-ℝ⁰⁺
```

## Properties

### Zero is less than or equal to every nonnegative real number

```agda
leq-zero-ℝ⁰⁺ : {l : Level} (x : ℝ⁰⁺ l) → leq-ℝ⁰⁺ zero-ℝ⁰⁺ x
leq-zero-ℝ⁰⁺ = is-nonnegative-real-ℝ⁰⁺
```

### Similarity preserves inequality

```agda
module _
  {l1 l2 l3 : Level} (z : ℝ⁰⁺ l1) (x : ℝ⁰⁺ l2) (y : ℝ⁰⁺ l3) (x~y : sim-ℝ⁰⁺ x y)
  where

  abstract
    preserves-leq-left-sim-ℝ⁰⁺ : leq-ℝ⁰⁺ x z → leq-ℝ⁰⁺ y z
    preserves-leq-left-sim-ℝ⁰⁺ = preserves-leq-left-sim-ℝ x~y
```

### Inequality is reflexive

```agda
abstract
  refl-leq-ℝ⁰⁺ : {l : Level} (x : ℝ⁰⁺ l) → leq-ℝ⁰⁺ x x
  refl-leq-ℝ⁰⁺ (x , _) = refl-leq-ℝ x
```

### Inequality is transitive

```agda
module _
  {l1 l2 l3 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2) (z : ℝ⁰⁺ l3)
  where

  transitive-leq-ℝ⁰⁺ : leq-ℝ⁰⁺ y z → leq-ℝ⁰⁺ x y → leq-ℝ⁰⁺ x z
  transitive-leq-ℝ⁰⁺ = transitive-leq-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y) (real-ℝ⁰⁺ z)
```

### Inequality is antisymmetric

```agda
module _
  {l : Level} (x : ℝ⁰⁺ l) (y : ℝ⁰⁺ l)
  where

  antisymmetric-leq-ℝ⁰⁺ : leq-ℝ⁰⁺ x y → leq-ℝ⁰⁺ y x → x ＝ y
  antisymmetric-leq-ℝ⁰⁺ x≤y y≤x =
    eq-ℝ⁰⁺ x y (antisymmetric-leq-ℝ _ _ x≤y y≤x)
```

### If `x` is less than all the positive rational numbers `y` is less than, then `x ≤ y`

```agda
module _
  {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2)
  where

  abstract
    leq-le-positive-rational-ℝ⁰⁺ :
      ( (q : ℚ⁺) → le-ℝ (real-ℝ⁰⁺ y) (real-ℚ⁺ q) →
        le-ℝ (real-ℝ⁰⁺ x) (real-ℚ⁺ q)) →
      leq-ℝ⁰⁺ x y
    leq-le-positive-rational-ℝ⁰⁺ H =
      leq-le-rational-ℝ (real-ℝ⁰⁺ x) (real-ℝ⁰⁺ y)
        ( λ q y<q →
          rec-coproduct
            ( λ 0<q →
              let open do-syntax-trunc-Prop (le-prop-ℝ (real-ℝ⁰⁺ x) (real-ℚ q))
              in do
                (p , y<p , p<q) ← dense-rational-le-ℝ _ _ y<q
                transitive-le-ℝ _ (real-ℚ p) _
                  ( p<q)
                  ( H
                    ( p , is-positive-le-nonnegative-real-ℚ y p y<p)
                    ( y<p)))
            ( λ q≤0 → ex-falso (not-le-leq-zero-rational-ℝ⁰⁺ y q q≤0 y<q))
            ( decide-le-leq-ℚ zero-ℚ q))
```

### If `x` is less than or equal to all the positive rational numbers `y` is less than or equal to, then `x ≤ y`

```agda
module _
  {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2)
  where

  abstract
    leq-leq-positive-rational-ℝ⁰⁺ :
      ( (q : ℚ⁺) → leq-ℝ (real-ℝ⁰⁺ y) (real-ℚ⁺ q) →
        leq-ℝ (real-ℝ⁰⁺ x) (real-ℚ⁺ q)) →
      leq-ℝ⁰⁺ x y
    leq-leq-positive-rational-ℝ⁰⁺ H =
      leq-le-positive-rational-ℝ⁰⁺ x y
        ( λ q y<q →
          let open do-syntax-trunc-Prop (le-prop-ℝ _ _)
          in do
            (r , y<r , r<q) ← dense-rational-le-ℝ _ _ y<q
            concatenate-leq-le-ℝ _ _ _
              ( H
                ( r , is-positive-le-nonnegative-real-ℚ y r y<r)
                ( leq-le-ℝ y<r))
              ( r<q))
```

### If `x` is less than or equal to the same positive rational numbers `y` is less than or equal to, then `x` and `y` are similar

```agda
module _
  {l1 l2 : Level} (x : ℝ⁰⁺ l1) (y : ℝ⁰⁺ l2)
  where

  abstract
    sim-leq-same-positive-rational-ℝ⁰⁺ :
      ( (q : ℚ⁺) →
        leq-ℝ (real-ℝ⁰⁺ x) (real-ℚ⁺ q) ↔ leq-ℝ (real-ℝ⁰⁺ y) (real-ℚ⁺ q)) →
      sim-ℝ⁰⁺ x y
    sim-leq-same-positive-rational-ℝ⁰⁺ H =
      sim-sim-leq-ℝ
        ( leq-leq-positive-rational-ℝ⁰⁺ x y (backward-implication ∘ H) ,
          leq-leq-positive-rational-ℝ⁰⁺ y x (forward-implication ∘ H))
```

### A nonnegative real number less than or equal to zero is zero

```agda
abstract
  eq-zero-leq-zero-ℝ⁰⁺ :
    {l : Level} (x : ℝ⁰⁺ l) → leq-ℝ⁰⁺ x zero-ℝ⁰⁺ → x ＝ raise-zero-ℝ⁰⁺ l
  eq-zero-leq-zero-ℝ⁰⁺ {l} x⁰⁺@(x , 0≤x) x≤0 =
    eq-ℝ⁰⁺ _ _
      ( eq-sim-ℝ
        ( transitive-sim-ℝ _ _ _
          ( sim-raise-ℝ l zero-ℝ)
          ( sim-sim-leq-ℝ (x≤0 , 0≤x))))
```

### The large poset of nonnegative real numbers

```agda
ℝ⁰⁺-Large-Preorder : Large-Preorder lsuc (_⊔_)
ℝ⁰⁺-Large-Preorder =
  λ where
    .type-Large-Preorder → ℝ⁰⁺
    .leq-prop-Large-Preorder → leq-prop-ℝ⁰⁺
    .refl-leq-Large-Preorder → refl-leq-ℝ ∘ real-ℝ⁰⁺
    .transitive-leq-Large-Preorder → transitive-leq-ℝ⁰⁺

ℝ⁰⁺-Large-Poset : Large-Poset lsuc (_⊔_)
ℝ⁰⁺-Large-Poset =
  λ where
    .large-preorder-Large-Poset → ℝ⁰⁺-Large-Preorder
    .antisymmetric-leq-Large-Poset → antisymmetric-leq-ℝ⁰⁺
```

### The large poset of nonnegative real numbers has a bottom element

```agda
has-bottom-element-ℝ⁰⁺-Large-Poset :
  has-bottom-element-Large-Poset ℝ⁰⁺-Large-Poset
has-bottom-element-ℝ⁰⁺-Large-Poset =
  λ where
    .bottom-has-bottom-element-Large-Poset → zero-ℝ⁰⁺
    .is-bottom-element-bottom-has-bottom-element-Large-Poset → leq-zero-ℝ⁰⁺
```

### The poset of nonnegative real numbers at a universe level

```agda
ℝ⁰⁺-Poset : (l : Level) → Poset (lsuc l) l
ℝ⁰⁺-Poset = poset-Large-Poset ℝ⁰⁺-Large-Poset
```
