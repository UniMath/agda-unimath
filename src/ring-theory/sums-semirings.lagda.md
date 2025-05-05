# Sums of elements in semirings

```agda
module ring-theory.sums-semirings where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositional-truncations
open import foundation.sets
open import foundation.unit-type
open import foundation.universe-levels

open import group-theory.products-of-tuples-of-elements-commutative-monoids

open import linear-algebra.vectors
open import linear-algebra.vectors-on-semirings

open import ring-theory.semirings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of families of elements in a semiring over a standard finite type" WD="sum" WDID=Q218005 Agda=sum-Semiring}}
extends the binary addition operation on a [semiring](ring-theory.semirings.md)
`R` to any family of elements of `R` indexed by a
[standard finite type](univalent-combinatorics.standard-finite-types.md), or by
a [finite type](univalent-combinatorics.finite-types.md).

## Definition

```agda
sum-Semiring :
  {l : Level} (R : Semiring l) (n : ℕ) →
  (functional-vec-Semiring R n) → type-Semiring R
sum-Semiring R =
  mul-fin-Commutative-Monoid (additive-commutative-monoid-Semiring R)

sum-count-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (A : UU l2) (cA : count A) →
  (A → type-Semiring R) → type-Semiring R
sum-count-Semiring R =
  mul-count-Commutative-Monoid (additive-commutative-monoid-Semiring R)

sum-finite-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (A : Finite-Type l2) →
  (type-Finite-Type A → type-Semiring R) → type-Semiring R
sum-finite-Semiring R =
  mul-finite-Commutative-Monoid (additive-commutative-monoid-Semiring R)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (R : Semiring l)
  where

  sum-one-element-Semiring :
    (f : functional-vec-Semiring R 1) →
    sum-Semiring R 1 f ＝ head-functional-vec 0 f
  sum-one-element-Semiring =
    mul-one-element-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)

  sum-unit-finite-Semiring :
    (f : unit → type-Semiring R) →
    sum-finite-Semiring R unit-Finite-Type f ＝ f star
  sum-unit-finite-Semiring =
    mul-unit-finite-Commutative-Monoid (additive-commutative-monoid-Semiring R)

  sum-two-elements-Semiring :
    (f : functional-vec-Semiring R 2) →
    sum-Semiring R 2 f ＝ add-Semiring R (f (zero-Fin 1)) (f (one-Fin 1))
  sum-two-elements-Semiring =
    mul-two-elements-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Semiring l)
  where

  htpy-sum-Semiring :
    (n : ℕ) {f g : functional-vec-Semiring R n} →
    (f ~ g) → sum-Semiring R n f ＝ sum-Semiring R n g
  htpy-sum-Semiring =
    htpy-mul-fin-Commutative-Monoid (additive-commutative-monoid-Semiring R)

  htpy-sum-finite-Semiring :
    {l2 : Level} (A : Finite-Type l2) →
    {f g : type-Finite-Type A → type-Semiring R} → (f ~ g) →
    sum-finite-Semiring R A f ＝ sum-finite-Semiring R A g
  htpy-sum-finite-Semiring =
    htpy-mul-finite-Commutative-Monoid (additive-commutative-monoid-Semiring R)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (R : Semiring l)
  where

  cons-sum-Semiring :
    (n : ℕ) (f : functional-vec-Semiring R (succ-ℕ n)) →
    {x : type-Semiring R} → head-functional-vec n f ＝ x →
    sum-Semiring R (succ-ℕ n) f ＝
    add-Semiring R (sum-Semiring R n (f ∘ inl-Fin n)) x
  cons-sum-Semiring n f refl = refl

  snoc-sum-Semiring :
    (n : ℕ) (f : functional-vec-Semiring R (succ-ℕ n)) →
    {x : type-Semiring R} → f (zero-Fin n) ＝ x →
    sum-Semiring R (succ-ℕ n) f ＝
    add-Semiring R
      ( x)
      ( sum-Semiring R n (f ∘ inr-Fin n))
  snoc-sum-Semiring =
    snoc-mul-fin-Commutative-Monoid (additive-commutative-monoid-Semiring R)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Semiring l)
  where

  abstract
    left-distributive-mul-sum-Semiring :
      (n : ℕ) (x : type-Semiring R)
      (f : functional-vec-Semiring R n) →
      mul-Semiring R x (sum-Semiring R n f) ＝
      sum-Semiring R n (λ i → mul-Semiring R x (f i))
    left-distributive-mul-sum-Semiring zero-ℕ x f =
      right-zero-law-mul-Semiring R x
    left-distributive-mul-sum-Semiring (succ-ℕ n) x f =
      ( left-distributive-mul-add-Semiring R x
        ( sum-Semiring R n (f ∘ inl-Fin n))
        ( f (inr star))) ∙
      ( ap
        ( add-Semiring' R (mul-Semiring R x (f (inr star))))
        ( left-distributive-mul-sum-Semiring n x (f ∘ inl-Fin n)))

    right-distributive-mul-sum-Semiring :
      (n : ℕ) (f : functional-vec-Semiring R n)
      (x : type-Semiring R) →
      mul-Semiring R (sum-Semiring R n f) x ＝
      sum-Semiring R n (λ i → mul-Semiring R (f i) x)
    right-distributive-mul-sum-Semiring zero-ℕ f x =
      left-zero-law-mul-Semiring R x
    right-distributive-mul-sum-Semiring (succ-ℕ n) f x =
      ( right-distributive-mul-add-Semiring R
        ( sum-Semiring R n (f ∘ inl-Fin n))
        ( f (inr star))
        ( x)) ∙
      ( ap
        ( add-Semiring' R (mul-Semiring R (f (inr star)) x))
        ( right-distributive-mul-sum-Semiring n (f ∘ inl-Fin n) x))

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
              ( mul-count-Commutative-Monoid
                ( additive-commutative-monoid-Semiring R)
                ( type-Finite-Type A)
                ( cA)
                ( f))
            by
              ap
                ( mul-Semiring R x)
                ( mul-finite-count-Commutative-Monoid _ A cA f)
          ＝
            mul-count-Commutative-Monoid
              ( additive-commutative-monoid-Semiring R)
              ( type-Finite-Type A)
              ( cA)
              ( mul-Semiring R x ∘ f)
            by
              left-distributive-mul-sum-Semiring
                ( number-of-elements-count cA)
                ( x)
                ( f ∘ map-equiv-count cA)
          ＝ sum-finite-Semiring R A (mul-Semiring R x ∘ f)
            by inv (mul-finite-count-Commutative-Monoid _ A cA _)

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
              ( mul-count-Commutative-Monoid
                ( additive-commutative-monoid-Semiring R)
                ( type-Finite-Type A)
                ( cA)
                ( f))
              ( x)
            by
              ap
                ( mul-Semiring' R x)
                ( mul-finite-count-Commutative-Monoid _ A cA f)
          ＝
            mul-count-Commutative-Monoid
              ( additive-commutative-monoid-Semiring R)
              ( type-Finite-Type A)
              ( cA)
              ( mul-Semiring' R x ∘ f)
            by
              right-distributive-mul-sum-Semiring
                ( number-of-elements-count cA)
                ( f ∘ map-equiv-count cA)
                ( x)
          ＝ sum-finite-Semiring R A (mul-Semiring' R x ∘ f)
            by inv (mul-finite-count-Commutative-Monoid _ A cA _)
```

### Interchange law of sums and addition in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  interchange-add-sum-Semiring :
    (n : ℕ) (f g : functional-vec-Semiring R n) →
    add-Semiring R
      ( sum-Semiring R n f)
      ( sum-Semiring R n g) ＝
    sum-Semiring R n
      ( add-functional-vec-Semiring R n f g)
  interchange-add-sum-Semiring zero-ℕ f g =
    left-unit-law-add-Semiring R (zero-Semiring R)
  interchange-add-sum-Semiring (succ-ℕ n) f g =
    ( interchange-add-add-Semiring R
      ( sum-Semiring R n (f ∘ inl-Fin n))
      ( f (inr star))
      ( sum-Semiring R n (g ∘ inl-Fin n))
      ( g (inr star))) ∙
    ( ap
      ( add-Semiring' R
        ( add-Semiring R (f (inr star)) (g (inr star))))
      ( interchange-add-sum-Semiring n
        ( f ∘ inl-Fin n)
        ( g ∘ inl-Fin n)))
```

### Extending a sum of elements in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  extend-sum-Semiring :
    (n : ℕ) (f : functional-vec-Semiring R n) →
    sum-Semiring R
      ( succ-ℕ n)
      ( cons-functional-vec-Semiring R n (zero-Semiring R) f) ＝
    sum-Semiring R n f
  extend-sum-Semiring =
    extend-mul-fin-Commutative-Monoid (additive-commutative-monoid-Semiring R)
```

### Shifting a sum of elements in a semiring

```agda
module _
  {l : Level} (R : Semiring l)
  where

  shift-sum-Semiring :
    (n : ℕ) (f : functional-vec-Semiring R n) →
    sum-Semiring R
      ( succ-ℕ n)
      ( snoc-functional-vec-Semiring R n f
        ( zero-Semiring R)) ＝
    sum-Semiring R n f
  shift-sum-Semiring =
    shift-mul-fin-Commutative-Monoid (additive-commutative-monoid-Semiring R)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (R : Semiring l)
  where

  sum-zero-Semiring :
    (n : ℕ) →
    sum-Semiring R n (zero-functional-vec-Semiring R n) ＝ zero-Semiring R
  sum-zero-Semiring =
    mul-fin-unit-Commutative-Monoid (additive-commutative-monoid-Semiring R)

  sum-zero-finite-Semiring :
    {l2 : Level} (A : Finite-Type l2) →
    sum-finite-Semiring R A (λ _ → zero-Semiring R) ＝ zero-Semiring R
  sum-zero-finite-Semiring =
    mul-finite-unit-Commutative-Monoid (additive-commutative-monoid-Semiring R)
```

### Splitting sums

```agda
split-sum-Semiring :
  {l : Level} (R : Semiring l)
  (n m : ℕ) (f : functional-vec-Semiring R (n +ℕ m)) →
  sum-Semiring R (n +ℕ m) f ＝
  add-Semiring R
    ( sum-Semiring R n (f ∘ inl-coproduct-Fin n m))
    ( sum-Semiring R m (f ∘ inr-coproduct-Fin n m))
split-sum-Semiring R =
  split-mul-fin-Commutative-Monoid (additive-commutative-monoid-Semiring R)
```

### Permutations preserve sums

```agda
module _
  {l : Level} (R : Semiring l)
  where

  preserves-sum-permutation-Semiring :
    (n : ℕ) → (σ : Permutation n) →
    (f : functional-vec-Semiring R n) →
    sum-Semiring R n f ＝ sum-Semiring R n (f ∘ map-equiv σ)
  preserves-sum-permutation-Semiring =
    preserves-product-permutation-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
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
    mul-equiv-finite-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( A)
      ( B)
      ( H)
```

### Sums over finite types distribute over coproducts

```agda
module _
  {l1 l2 l3 : Level} (R : Semiring l1) (A : Finite-Type l2) (B : Finite-Type l3)
  where

  sum-coproduct-finite-Semiring :
    (f :
      type-Finite-Type A + type-Finite-Type B → type-Semiring R) →
    sum-finite-Semiring R (coproduct-Finite-Type A B) f ＝
    add-Semiring
      ( R)
      ( sum-finite-Semiring R A (f ∘ inl))
      ( sum-finite-Semiring R B (f ∘ inr))
  sum-coproduct-finite-Semiring =
    mul-coproduct-finite-Commutative-Monoid
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
    mul-Σ-finite-Commutative-Monoid (additive-commutative-monoid-Semiring R) A B
```

### The sum over an empty type is zero

```agda
module _
  {l1 l2 : Level} (R : Semiring l1) (A : Finite-Type l2)
  (H : is-empty (type-Finite-Type A))
  where

  sum-is-empty-finite-Semiring :
    (f : type-Finite-Type A → type-Semiring R) →
    is-zero-Semiring R (sum-finite-Semiring R A f)
  sum-is-empty-finite-Semiring =
    mul-is-empty-finite-Commutative-Monoid
      ( additive-commutative-monoid-Semiring R)
      ( A)
      ( H)
```

### The sum over a finite type is the sum over any count for that type

```agda
sum-finite-count-Semiring :
  {l1 l2 : Level} (R : Semiring l1) (A : Finite-Type l2)
  (cA : count (type-Finite-Type A))
  (f : type-Finite-Type A → type-Semiring R) →
  sum-finite-Semiring R A f ＝
  sum-count-Semiring R (type-Finite-Type A) cA f
sum-finite-count-Semiring R =
  mul-finite-count-Commutative-Monoid (additive-commutative-monoid-Semiring R)
```
