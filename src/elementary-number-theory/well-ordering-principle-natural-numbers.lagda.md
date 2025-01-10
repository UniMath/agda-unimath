# The well-ordering principle of the natural numbers

```agda
module elementary-number-theory.well-ordering-principle-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-types
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.lower-bounds-natural-numbers
open import elementary-number-theory.maximal-structured-natural-numbers
open import elementary-number-theory.minimal-structured-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.upper-bounds-natural-numbers

open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.hilberts-epsilon-operators
open import foundation.identity-types
open import foundation.negation
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.subtypes
open import foundation.universe-levels
```

</details>

## Idea

The
{{#concept "well-ordering principle of the natural numbers" WDID=Q2488476 WD="well-ordering principle"}}
asserts that for every family of
[decidable types](foundation.decidable-types.md) over ℕ equipped with a natural
number `n` and an element `p : P n`, we can find a least natural number `n₀`
with an element `p₀ : P n₀`.

The well-ordering principle has some useful consequences:

- For any family `P` of decidable types equipped with a natural number `n ≥ b`
  and an element `p : P n` we can find a least natural number `n₀ ≥ b` with an
  element `p₀ : P n₀`.
- For any family `P` of decidable types equipped with an element `n ≤ b` and an
  element `p : P n` we can find a largest natural number `n₁ ≤ b` with an
  element `p₁ : P n₁`.
- For any
  [strictly inflationary map](order-theory.inflationary-maps-strictly-ordered-types.md)
  `f : ℕ → ℕ` such that `f 0 ≤ b` we can find a largest natural number `n₁` such
  that `f n₁ ≤ b`.

## Theorems

### The Well-Ordering Principle

```agda
is-minimal-element-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (m : ℕ) (pm : P (succ-ℕ m))
  (is-lower-bound-m : is-lower-bound-ℕ (λ x → P (succ-ℕ x)) m) →
  ¬ (P 0) → is-lower-bound-ℕ P (succ-ℕ m)
is-minimal-element-succ-ℕ P d m pm is-lower-bound-m neg-p0 zero-ℕ p0 =
  ex-falso (neg-p0 p0)
is-minimal-element-succ-ℕ
  P d zero-ℕ pm is-lower-bound-m neg-p0 (succ-ℕ n) psuccn =
  leq-zero-ℕ n
is-minimal-element-succ-ℕ
  P d (succ-ℕ m) pm is-lower-bound-m neg-p0 (succ-ℕ n) psuccn =
  is-lower-bound-m n psuccn

well-ordering-principle-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (n : ℕ) (p : P (succ-ℕ n)) →
  is-decidable (P 0) →
  minimal-element-ℕ (λ m → P (succ-ℕ m)) → minimal-element-ℕ P
well-ordering-principle-succ-ℕ P d n p (inl p0) u =
  ( 0 , p0 , λ m q → leq-zero-ℕ m)
well-ordering-principle-succ-ℕ P d n p (inr neg-p0) (m , pm , is-min-m) =
  ( succ-ℕ m , pm , is-minimal-element-succ-ℕ P d m pm is-min-m neg-p0)

well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  Σ ℕ P → minimal-element-ℕ P
well-ordering-principle-ℕ P d (zero-ℕ , p) =
  ( 0 , p , λ m _ → leq-zero-ℕ m)
well-ordering-principle-ℕ P d (succ-ℕ n , p) =
  well-ordering-principle-succ-ℕ P d n p
    ( d 0)
    ( well-ordering-principle-ℕ (P ∘ succ-ℕ) (d ∘ succ-ℕ) (n , p))

nat-well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) (nP : Σ ℕ P) → ℕ
nat-well-ordering-principle-ℕ P d nP =
  pr1 (well-ordering-principle-ℕ P d nP)
```

## Properties

### The well-ordering principle returns `0` if `P 0` holds

```agda
is-zero-well-ordering-principle-succ-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P)
  (n : ℕ) (p : P (succ-ℕ n)) (d0 : is-decidable (P 0)) →
  (x : minimal-element-ℕ (λ m → P (succ-ℕ m))) (p0 : P 0) →
  pr1 (well-ordering-principle-succ-ℕ P d n p d0 x) ＝ 0
is-zero-well-ordering-principle-succ-ℕ P d n p (inl p0) x q0 =
  refl
is-zero-well-ordering-principle-succ-ℕ P d n p (inr np0) x q0 =
  ex-falso (np0 q0)

is-zero-well-ordering-principle-ℕ :
  {l : Level} (P : ℕ → UU l) (d : is-decidable-fam P) →
  (x : Σ ℕ P) → P 0 → is-zero-ℕ (nat-well-ordering-principle-ℕ P d x)
is-zero-well-ordering-principle-ℕ P d (zero-ℕ , p) p0 = refl
is-zero-well-ordering-principle-ℕ P d (succ-ℕ m , p) =
  is-zero-well-ordering-principle-succ-ℕ P d m p (d 0)
    ( well-ordering-principle-ℕ
      ( λ z → P (succ-ℕ z))
      ( λ x → d (succ-ℕ x))
      ( m , p))
```

### The type of minimal elements of a subtype has at most one element

```agda
module _
  {l1 : Level} (P : ℕ → Prop l1)
  where

  all-elements-equal-minimal-element-ℕ :
    all-elements-equal (minimal-element-ℕ (λ n → type-Prop (P n)))
  all-elements-equal-minimal-element-ℕ
    (x , p , l) (y , q , k) =
    eq-type-subtype
      ( λ n →
        product-Prop
          ( _  , is-prop-type-Prop (P n))
          ( is-lower-bound-ℕ-Prop (type-Prop ∘ P) n))
      ( antisymmetric-leq-ℕ x y (l y q) (k x p))

  is-prop-minimal-element-ℕ :
    is-prop (minimal-element-ℕ (λ n → type-Prop (P n)))
  is-prop-minimal-element-ℕ =
    is-prop-all-elements-equal all-elements-equal-minimal-element-ℕ

  minimal-element-ℕ-Prop : Prop l1
  pr1 minimal-element-ℕ-Prop = minimal-element-ℕ (λ n → type-Prop (P n))
  pr2 minimal-element-ℕ-Prop = is-prop-minimal-element-ℕ
```

### The ε-operator for decidable subtypes of ℕ

```agda
ε-operator-decidable-subtype-ℕ :
  {l1 : Level} (P : ℕ → Prop l1)
  (d : (x : ℕ) → is-decidable (type-Prop (P x))) →
  ε-operator-Hilbert (type-subtype P)
ε-operator-decidable-subtype-ℕ {l1} P d t =
  tot
    ( λ x → pr1)
    ( apply-universal-property-trunc-Prop t
      ( minimal-element-ℕ-Prop P)
      ( well-ordering-principle-ℕ (λ x → type-Prop (P x)) d))
```

### Every decidable type family over `ℕ` equipped with an element with an upper bound has a bounded maximal element

```agda
module _
  {l : Level} (P : ℕ → UU l) (d : (x : ℕ) → is-decidable (P x)) (b : ℕ)
  where

  upper-bound-bounded-decidable-family-ℕ :
    ℕ → UU l
  upper-bound-bounded-decidable-family-ℕ x =
    (y : ℕ) → y ≤-ℕ b → P y → y ≤-ℕ x

  is-decidable-upper-bound-bounded-decidable-family-ℕ :
    (x : ℕ) → is-decidable (upper-bound-bounded-decidable-family-ℕ x)
  is-decidable-upper-bound-bounded-decidable-family-ℕ x =
    is-decidable-bounded-Π-ℕ'
      ( λ y → P y → y ≤-ℕ x)
      ( λ y → is-decidable-function-type (d y) (is-decidable-leq-ℕ y x))
      ( b)

  instance-upper-bound-bounded-decidable-family-ℕ :
    upper-bound-bounded-decidable-family-ℕ b
  instance-upper-bound-bounded-decidable-family-ℕ y H p = H

  least-upper-bound-bounded-decidable-family-ℕ :
    minimal-element-ℕ upper-bound-bounded-decidable-family-ℕ
  least-upper-bound-bounded-decidable-family-ℕ =
    well-ordering-principle-ℕ
      ( upper-bound-bounded-decidable-family-ℕ)
      ( is-decidable-upper-bound-bounded-decidable-family-ℕ)
      ( b , instance-upper-bound-bounded-decidable-family-ℕ)

  nat-bounded-maximal-element-decidable-family-ℕ :
    ℕ
  nat-bounded-maximal-element-decidable-family-ℕ =
    pr1 least-upper-bound-bounded-decidable-family-ℕ

  upper-bound-nat-bounded-maximal-element-decidable-family-ℕ :
    nat-bounded-maximal-element-decidable-family-ℕ ≤-ℕ b
  upper-bound-nat-bounded-maximal-element-decidable-family-ℕ =
    {!!}

  structure-nat-bounded-maximal-element-decidable-family-ℕ :
    P nat-bounded-maximal-element-decidable-family-ℕ
  structure-nat-bounded-maximal-element-decidable-family-ℕ =
    {!!}

  is-upper-bound-nat-bounded-maximal-element-decidable-family-ℕ :
    is-upper-bound-ℕ P nat-bounded-maximal-element-decidable-family-ℕ
  is-upper-bound-nat-bounded-maximal-element-decidable-family-ℕ =
    {!!}

  bounded-maximal-element-decidable-family-ℕ :
    (n : ℕ) → n ≤-ℕ b → P n → bounded-maximal-element-ℕ P b
  bounded-maximal-element-decidable-family-ℕ n H p =
    ( ( nat-bounded-maximal-element-decidable-family-ℕ) ,
      ( upper-bound-nat-bounded-maximal-element-decidable-family-ℕ ,
        structure-nat-bounded-maximal-element-decidable-family-ℕ) ,
      {!!} {- is-upper-bound-nat-bounded-maximal-element-decidable-family-ℕ -})
```
