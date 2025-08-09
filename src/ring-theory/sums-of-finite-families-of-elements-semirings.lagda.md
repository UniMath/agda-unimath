# Sums of finite families of elements in semirings

```agda
module ring-theory.sums-of-finite-families-of-elements-semirings where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.type-arithmetic-cartesian-product-types
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.powers-of-elements-commutative-monoids
open import group-theory.sums-of-finite-families-of-elements-commutative-monoids

open import ring-theory.semirings
open import ring-theory.sums-of-finite-sequences-of-elements-semirings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite family of elements of a semiring" WD="sum" WDID=Q218005 Agda=sum-fin-sequence-type-Semiring}}
extends the binary addition operation on a [semiring](ring-theory.semirings.md)
`R` to any family of elements of `R` indexed by a
[finite type](univalent-combinatorics.finite-types.md).

## Definition

```agda
sum-count-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (A : UU l2) (cA : count A) →
  (A → type-Semiring R) → type-Semiring R
sum-count-Semiring R =
  sum-count-Commutative-Monoid (additive-commutative-monoid-Semiring R)

sum-finite-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (A : Finite-Type l2) →
  (type-Finite-Type A → type-Semiring R) → type-Semiring R
sum-finite-Semiring R =
  sum-finite-Commutative-Monoid (additive-commutative-monoid-Semiring R)
```

## Properties

### Sums over the unit type

```agda
module _
  {l : Level} (R : Semiring l)
  where

  sum-unit-finite-Semiring :
    (f : unit → type-Semiring R) →
    sum-finite-Semiring R unit-Finite-Type f ＝ f star
  sum-unit-finite-Semiring =
    sum-finite-unit-type-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Semiring l)
  where

  htpy-sum-finite-Semiring :
    {l2 : Level} (A : Finite-Type l2) →
    {f g : type-Finite-Type A → type-Semiring R} → (f ~ g) →
    sum-finite-Semiring R A f ＝ sum-finite-Semiring R A g
  htpy-sum-finite-Semiring =
    htpy-sum-finite-Commutative-Monoid (additive-commutative-monoid-Semiring R)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Semiring l)
  where

  abstract
    left-distributive-mul-sum-finite-Semiring :
      {l2 : Level} (A : Finite-Type l2) (x : type-Semiring R) →
      (f : type-Finite-Type A → type-Semiring R) →
      mul-Semiring R x (sum-finite-Semiring R A f) ＝
      sum-finite-Semiring R A (mul-Semiring R x ∘ f)
    left-distributive-mul-sum-finite-Semiring A x f =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Semiring R)
              ( mul-Semiring R x (sum-finite-Semiring R A f))
              ( sum-finite-Semiring R A (mul-Semiring R x ∘ f)))
      in do
        cA ← is-finite-type-Finite-Type A
        equational-reasoning
          mul-Semiring R x (sum-finite-Semiring R A f)
          ＝
            mul-Semiring
              ( R)
              ( x)
              ( sum-count-Semiring
                ( R)
                ( type-Finite-Type A)
                ( cA)
                ( f))
            by
              ap
                ( mul-Semiring R x)
                ( eq-sum-finite-sum-count-Commutative-Monoid _ A cA f)
          ＝
            sum-count-Semiring R (type-Finite-Type A) cA (mul-Semiring R x ∘ f)
            by
              left-distributive-mul-sum-fin-sequence-type-Semiring
                ( R)
                ( number-of-elements-count cA)
                ( x)
                ( f ∘ map-equiv-count cA)
          ＝ sum-finite-Semiring R A (mul-Semiring R x ∘ f)
            by inv (eq-sum-finite-sum-count-Commutative-Monoid _ A cA _)

    right-distributive-mul-sum-finite-Semiring :
      {l2 : Level} (A : Finite-Type l2) →
      (f : type-Finite-Type A → type-Semiring R) (x : type-Semiring R) →
      mul-Semiring R (sum-finite-Semiring R A f) x ＝
      sum-finite-Semiring R A (mul-Semiring' R x ∘ f)
    right-distributive-mul-sum-finite-Semiring A f x =
      let
        open
          do-syntax-trunc-Prop
            ( Id-Prop
              ( set-Semiring R)
              ( mul-Semiring R (sum-finite-Semiring R A f) x)
              ( sum-finite-Semiring R A (mul-Semiring' R x ∘ f)))
      in do
        cA ← is-finite-type-Finite-Type A
        equational-reasoning
          mul-Semiring R (sum-finite-Semiring R A f) x
          ＝
            mul-Semiring
              ( R)
              ( sum-count-Semiring R (type-Finite-Type A) cA f)
              ( x)
            by
              ap
                ( mul-Semiring' R x)
                ( eq-sum-finite-sum-count-Commutative-Monoid _ A cA f)
          ＝
            sum-count-Semiring R (type-Finite-Type A) cA (mul-Semiring' R x ∘ f)
            by
              right-distributive-mul-sum-fin-sequence-type-Semiring
                ( R)
                ( number-of-elements-count cA)
                ( f ∘ map-equiv-count cA)
                ( x)
          ＝ sum-finite-Semiring R A (mul-Semiring' R x ∘ f)
            by inv (eq-sum-finite-sum-count-Commutative-Monoid _ A cA _)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (R : Semiring l)
  where

  sum-zero-finite-Semiring :
    {l2 : Level} (A : Finite-Type l2) →
    sum-finite-Semiring R A (λ _ → zero-Semiring R) ＝ zero-Semiring R
  sum-zero-finite-Semiring =
    sum-zero-finite-Commutative-Monoid (additive-commutative-monoid-Semiring R)
```

### Sums over finite types are preserved by equivalences

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (A : Finite-Type l2) (B : Finite-Type l3)
  (H : equiv-Finite-Type A B)
  where

  sum-equiv-finite-Semiring :
    (f : type-Finite-Type A → type-Semiring R) →
    sum-finite-Semiring R A f ＝ sum-finite-Semiring R B (f ∘ map-inv-equiv H)
  sum-equiv-finite-Semiring =
    sum-equiv-finite-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( A)
      ( B)
      ( H)

module _
  {l1 l2 : Level} (R : Semiring l1) (A : Finite-Type l2)
  (H : aut-Finite-Type A)
  where

  sum-aut-finite-Semiring :
    (f : type-Finite-Type A → type-Semiring R) →
    sum-finite-Semiring R A f ＝ sum-finite-Semiring R A (f ∘ map-inv-equiv H)
  sum-aut-finite-Semiring = sum-equiv-finite-Semiring R A A H
```

### Sums over finite types distribute over coproducts

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (A : Finite-Type l2) (B : Finite-Type l3)
  where

  distributive-sum-coproduct-finite-Semiring :
    (f :
      type-Finite-Type A + type-Finite-Type B → type-Semiring R) →
    sum-finite-Semiring R (coproduct-Finite-Type A B) f ＝
    add-Semiring
      ( R)
      ( sum-finite-Semiring R A (f ∘ inl))
      ( sum-finite-Semiring R B (f ∘ inr))
  distributive-sum-coproduct-finite-Semiring =
    distributive-distributive-sum-coproduct-finite-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( A)
      ( B)
```

### Sums distribute over dependent pair types

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1)
  (A : Finite-Type l2) (B : type-Finite-Type A → Finite-Type l3)
  where

  sum-Σ-finite-Semiring :
    (f : (a : type-Finite-Type A) → type-Finite-Type (B a) → type-Semiring R) →
    sum-finite-Semiring R (Σ-Finite-Type A B) (ind-Σ f) ＝
    sum-finite-Semiring R A (λ a → sum-finite-Semiring R (B a) (f a))
  sum-Σ-finite-Semiring =
    sum-Σ-finite-Commutative-Monoid (additive-commutative-monoid-Semiring R) A B
```

### The sum over an empty type is zero

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (A : Finite-Type l2)
  (H : is-empty (type-Finite-Type A))
  where

  eq-zero-sum-finite-is-empty-Semiring :
    (f : type-Finite-Type A → type-Semiring R) →
    is-zero-Semiring R (sum-finite-Semiring R A f)
  eq-zero-sum-finite-is-empty-Semiring =
    eq-zero-sum-finite-is-empty-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( A)
      ( H)
```

### The sum over a finite type is the sum over any count for that type

```agda
eq-sum-finite-sum-count-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (A : Finite-Type l2)
  (cA : count (type-Finite-Type A))
  (f : type-Finite-Type A → type-Semiring R) →
  sum-finite-Semiring R A f ＝
  sum-count-Semiring R (type-Finite-Type A) cA f
eq-sum-finite-sum-count-Semiring R =
  eq-sum-finite-sum-count-Commutative-Monoid
    ( additive-commutative-monoid-Semiring R)
```

### Interchange law of sums and addition

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (A : Finite-Type l2)
  where

  interchange-sum-add-finite-Semiring :
    (f g : type-Finite-Type A → type-Semiring R) →
    sum-finite-Semiring R A
      (λ a → add-Semiring R (f a) (g a)) ＝
    add-Semiring R
      (sum-finite-Semiring R A f)
      (sum-finite-Semiring R A g)
  interchange-sum-add-finite-Semiring f g = equational-reasoning
    sum-finite-Semiring R A
      ( λ a → add-Semiring R (f a) (g a))
    ＝
      sum-finite-Semiring
        ( R)
        ( A)
        ( λ a → sum-fin-sequence-type-Semiring R 2 (h a))
        by
          htpy-sum-finite-Semiring
            ( R)
            ( A)
            ( λ a → inv (compute-sum-two-elements-Semiring R (h a)))
    ＝
      sum-finite-Semiring
        ( R)
        ( A)
        ( λ a →
          sum-finite-Semiring R (Fin-Finite-Type 2) (h a))
      by
        htpy-sum-finite-Semiring R A
          ( λ a →
            inv
              ( eq-sum-finite-sum-count-Semiring
                ( R)
                ( Fin-Finite-Type 2)
                ( count-Fin 2)
                ( h a)))
    ＝
      sum-finite-Semiring
        ( R)
        ( Σ-Finite-Type A (λ _ → Fin-Finite-Type 2))
        ( ind-Σ h)
      by inv (sum-Σ-finite-Semiring R A (λ _ → Fin-Finite-Type 2) h)
    ＝
      sum-finite-Semiring
        ( R)
        ( Σ-Finite-Type (Fin-Finite-Type 2) (λ _ → A))
        ( λ (i , a) → h a i)
      by
        sum-equiv-finite-Semiring R _ _
          ( commutative-product)
          ( ind-Σ h)
    ＝
      sum-finite-Semiring
        ( R)
        ( Fin-Finite-Type 2)
        ( λ i → sum-finite-Semiring R A (λ a → h a i))
      by sum-Σ-finite-Semiring R _ _ _
    ＝
      sum-fin-sequence-type-Semiring
        ( R)
        ( 2)
        ( λ i → sum-finite-Semiring R A (λ a → h a i))
      by
        eq-sum-finite-sum-count-Semiring
          ( R)
          ( Fin-Finite-Type 2)
          ( count-Fin 2)
          ( _)
    ＝
      add-Semiring
        ( R)
        ( sum-finite-Semiring R A f)
        ( sum-finite-Semiring R A g)
      by
        compute-sum-two-elements-Semiring
          ( R)
          ( λ i → sum-finite-Semiring R A (λ a → h a i))
    where
      h : type-Finite-Type A → Fin 2 → type-Semiring R
      h a (inl (inr _)) = f a
      h a (inr _) = g a
```

### Sums of constant functions

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (A : Finite-Type l2)
  where

  sum-const-finite-type-Semiring :
    (c : type-Semiring R) →
    sum-finite-Semiring R A (λ _ → c) ＝
    power-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( number-of-elements-Finite-Type A)
      ( c)
  sum-const-finite-type-Semiring = sum-const-finite-type-Commutative-Monoid _ A
```
