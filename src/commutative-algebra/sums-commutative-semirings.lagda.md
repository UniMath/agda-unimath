# Sums in commutative semirings

```agda
module commutative-algebra.sums-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations
open import finite-group-theory.permutations-standard-finite-types
open import finite-group-theory.transpositions
open import finite-group-theory.transpositions-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.unit-type
open import foundation.universal-property-propositional-truncation-into-sets
open import foundation.universe-levels

open import linear-algebra.vectors
open import linear-algebra.vectors-on-commutative-semirings

open import lists.lists

open import ring-theory.sums-semirings

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The **sum operation** extends the binary addition operation on a commutative
semiring `R` to any family of elements of `R` indexed by a standard finite type.

## Definition

```agda
sum-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l) (n : ℕ) →
  (functional-vec-Commutative-Semiring A n) → type-Commutative-Semiring A
sum-Commutative-Semiring A = sum-Semiring (semiring-Commutative-Semiring A)
```

## Properties

### Sums of one and two elements

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  sum-one-element-Commutative-Semiring :
    (f : functional-vec-Commutative-Semiring A 1) →
    sum-Commutative-Semiring A 1 f ＝ head-functional-vec 0 f
  sum-one-element-Commutative-Semiring =
    sum-one-element-Semiring (semiring-Commutative-Semiring A)

  sum-two-elements-Commutative-Semiring :
    (f : functional-vec-Commutative-Semiring A 2) →
    sum-Commutative-Semiring A 2 f ＝
    add-Commutative-Semiring A (f (zero-Fin 1)) (f (one-Fin 1))
  sum-two-elements-Commutative-Semiring =
    sum-two-elements-Semiring (semiring-Commutative-Semiring A)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  htpy-sum-Commutative-Semiring :
    (n : ℕ) {f g : functional-vec-Commutative-Semiring A n} →
    (f ~ g) → sum-Commutative-Semiring A n f ＝ sum-Commutative-Semiring A n g
  htpy-sum-Commutative-Semiring =
    htpy-sum-Semiring (semiring-Commutative-Semiring A)
```

### Sums are equal to the zero-th term plus the rest

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  cons-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring A (succ-ℕ n)) →
    {x : type-Commutative-Semiring A} → head-functional-vec n f ＝ x →
    sum-Commutative-Semiring A (succ-ℕ n) f ＝
    add-Commutative-Semiring A
      ( sum-Commutative-Semiring A n (tail-functional-vec n f)) x
  cons-sum-Commutative-Semiring =
    cons-sum-Semiring (semiring-Commutative-Semiring A)

  snoc-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring A (succ-ℕ n)) →
    {x : type-Commutative-Semiring A} → f (zero-Fin n) ＝ x →
    sum-Commutative-Semiring A (succ-ℕ n) f ＝
    add-Commutative-Semiring A
      ( x)
      ( sum-Commutative-Semiring A n (f ∘ inr-Fin n))
  snoc-sum-Commutative-Semiring =
    snoc-sum-Semiring (semiring-Commutative-Semiring A)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  left-distributive-mul-sum-Commutative-Semiring :
    (n : ℕ) (x : type-Commutative-Semiring A)
    (f : functional-vec-Commutative-Semiring A n) →
    mul-Commutative-Semiring A x (sum-Commutative-Semiring A n f) ＝
    sum-Commutative-Semiring A n (λ i → mul-Commutative-Semiring A x (f i))
  left-distributive-mul-sum-Commutative-Semiring =
    left-distributive-mul-sum-Semiring (semiring-Commutative-Semiring A)

  right-distributive-mul-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring A n)
    (x : type-Commutative-Semiring A) →
    mul-Commutative-Semiring A (sum-Commutative-Semiring A n f) x ＝
    sum-Commutative-Semiring A n (λ i → mul-Commutative-Semiring A (f i) x)
  right-distributive-mul-sum-Commutative-Semiring =
    right-distributive-mul-sum-Semiring (semiring-Commutative-Semiring A)
```

### Interchange law of sums and addition in a commutative semiring

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  interchange-add-sum-Commutative-Semiring :
    (n : ℕ) (f g : functional-vec-Commutative-Semiring A n) →
    add-Commutative-Semiring A
      ( sum-Commutative-Semiring A n f)
      ( sum-Commutative-Semiring A n g) ＝
    sum-Commutative-Semiring A n
      ( add-functional-vec-Commutative-Semiring A n f g)
  interchange-add-sum-Commutative-Semiring =
    interchange-add-sum-Semiring (semiring-Commutative-Semiring A)
```

### Extending a sum of elements in a commutative semiring

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  extend-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring A n) →
    sum-Commutative-Semiring A
      ( succ-ℕ n)
      ( cons-functional-vec-Commutative-Semiring A n
        ( zero-Commutative-Semiring A) f) ＝
    sum-Commutative-Semiring A n f
  extend-sum-Commutative-Semiring =
    extend-sum-Semiring (semiring-Commutative-Semiring A)
```

### Shifting a sum of elements in a commutative semiring

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  shift-sum-Commutative-Semiring :
    (n : ℕ) (f : functional-vec-Commutative-Semiring A n) →
    sum-Commutative-Semiring A
      ( succ-ℕ n)
      ( snoc-functional-vec-Commutative-Semiring A n f
        ( zero-Commutative-Semiring A)) ＝
    sum-Commutative-Semiring A n f
  shift-sum-Commutative-Semiring =
    shift-sum-Semiring (semiring-Commutative-Semiring A)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  sum-zero-Commutative-Semiring :
    (n : ℕ) →
    sum-Commutative-Semiring A n
      ( zero-functional-vec-Commutative-Semiring A n) ＝
    zero-Commutative-Semiring A
  sum-zero-Commutative-Semiring =
    sum-zero-Semiring (semiring-Commutative-Semiring A)
```

### Splitting sums

```agda
split-sum-Commutative-Semiring :
  {l : Level} (A : Commutative-Semiring l)
  (n m : ℕ) (f : functional-vec-Commutative-Semiring A (n +ℕ m)) →
  sum-Commutative-Semiring A (n +ℕ m) f ＝
  add-Commutative-Semiring A
    ( sum-Commutative-Semiring A n (f ∘ inl-coproduct-Fin n m))
    ( sum-Commutative-Semiring A m (f ∘ inr-coproduct-Fin n m))
split-sum-Commutative-Semiring A =
  split-sum-Semiring (semiring-Commutative-Semiring A)
```

### Permutations preserve sums

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  abstract
    preserves-sum-adjacent-transposition-sum-Commutative-Semiring :
      (n : ℕ) → (k : Fin n) →
      (f : functional-vec-Commutative-Semiring A (succ-ℕ n)) →
      sum-Commutative-Semiring A (succ-ℕ n) f ＝
      sum-Commutative-Semiring
        A (succ-ℕ n) (f ∘ map-adjacent-transposition-Fin n k)
    preserves-sum-adjacent-transposition-sum-Commutative-Semiring
      (succ-ℕ n) (inl x) f =
        ap-add-Commutative-Semiring
          ( A)
          ( preserves-sum-adjacent-transposition-sum-Commutative-Semiring
            ( n)
            ( x)
            ( f ∘ inl-Fin (succ-ℕ n)))
          ( refl)
    preserves-sum-adjacent-transposition-sum-Commutative-Semiring
      (succ-ℕ n) (inr star) f = right-swap-add-Commutative-Semiring A _ _ _

    preserves-sum-permutation-list-adjacent-transpositions-Commutative-Semiring :
      (n : ℕ) → (L : list (Fin n)) →
      (f : functional-vec-Commutative-Semiring A (succ-ℕ n)) →
      sum-Commutative-Semiring A (succ-ℕ n) f ＝
      sum-Commutative-Semiring
        A (succ-ℕ n) (f ∘ map-permutation-list-adjacent-transpositions n L)
    preserves-sum-permutation-list-adjacent-transpositions-Commutative-Semiring
      n nil f = refl
    preserves-sum-permutation-list-adjacent-transpositions-Commutative-Semiring
      n (cons x L) f =
        preserves-sum-adjacent-transposition-sum-Commutative-Semiring n x f ∙
        preserves-sum-permutation-list-adjacent-transpositions-Commutative-Semiring
          ( n)
          ( L)
          ( f ∘ map-adjacent-transposition-Fin n x)

    preserves-sum-transposition-Commutative-Semiring :
      (n : ℕ) (i j : Fin (succ-ℕ n)) (neq : i ≠ j) →
      (f : functional-vec-Commutative-Semiring A (succ-ℕ n)) →
      sum-Commutative-Semiring A (succ-ℕ n) f ＝
      sum-Commutative-Semiring
        A (succ-ℕ n) (f ∘ map-transposition-Fin (succ-ℕ n) i j neq)
    preserves-sum-transposition-Commutative-Semiring n i j i≠j f =
      preserves-sum-permutation-list-adjacent-transpositions-Commutative-Semiring
        ( n)
        ( list-adjacent-transpositions-transposition-Fin n i j)
        ( f) ∙
      ap
        ( λ g → sum-Commutative-Semiring A (succ-ℕ n) (f ∘ map-equiv g))
        ( eq-permutation-list-adjacent-transpositions-transposition-Fin
          ( n)
          ( i)
          ( j)
          ( i≠j))

    preserves-sum-permutation-list-standard-transpositions-Commutative-Semiring :
      (n : ℕ) → (L : list (Σ (Fin n × Fin n) ( λ (i , j) → i ≠ j))) →
      (f : functional-vec-Commutative-Semiring A n) →
      sum-Commutative-Semiring A n f ＝
      sum-Commutative-Semiring
        A n (f ∘ map-equiv (permutation-list-standard-transpositions-Fin n L))
    preserves-sum-permutation-list-standard-transpositions-Commutative-Semiring
      zero-ℕ _ _ = refl
    preserves-sum-permutation-list-standard-transpositions-Commutative-Semiring
      (succ-ℕ n) nil f = refl
    preserves-sum-permutation-list-standard-transpositions-Commutative-Semiring
      (succ-ℕ n) (cons ((i , j) , i≠j) L) f =
        preserves-sum-transposition-Commutative-Semiring n i j i≠j f ∙
        preserves-sum-permutation-list-standard-transpositions-Commutative-Semiring
          ( succ-ℕ n)
          ( L)
          ( f ∘ map-transposition-Fin (succ-ℕ n) i j i≠j)

    preserves-sum-permutation-Commutative-Semiring :
      (n : ℕ) → (σ : Permutation n) →
      (f : functional-vec-Commutative-Semiring A n) →
      sum-Commutative-Semiring A n f ＝
      sum-Commutative-Semiring A n (f ∘ map-equiv σ)
    preserves-sum-permutation-Commutative-Semiring n σ f =
      preserves-sum-permutation-list-standard-transpositions-Commutative-Semiring
        ( n)
        ( list-standard-transpositions-permutation-Fin n σ)
        ( f) ∙
      ap
        ( λ τ → sum-Commutative-Semiring A n (f ∘ map-equiv τ))
        ( eq-permutation-list-standard-transpositions-Fin n σ)
```

### Sums for a count for a type

```agda
sum-count-Commutative-Semiring :
  {l1 l2 : Level} (R : Commutative-Semiring l1) (A : UU l2) →
  count A → (A → type-Commutative-Semiring R) → type-Commutative-Semiring R
sum-count-Commutative-Semiring R A (n , Fin-n≃A) f =
  sum-Commutative-Semiring R n (f ∘ map-equiv Fin-n≃A)
```

### Two counts for the same set produce equivalent sums

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1) (A : UU l2)
  where

  abstract
    eq-sum-count-equiv-Commutative-Semiring :
      (n : ℕ) → (equiv1 equiv2 : Fin n ≃ A) →
      (f : A → type-Commutative-Semiring R) →
      sum-count-Commutative-Semiring R A (n , equiv1) f ＝
      sum-count-Commutative-Semiring R A (n , equiv2) f
    eq-sum-count-equiv-Commutative-Semiring n equiv1 equiv2 f =
      equational-reasoning
      sum-Commutative-Semiring R n (f ∘ map-equiv equiv1)
      ＝
        sum-Commutative-Semiring
          ( R)
          ( n)
          ( (f ∘ map-equiv equiv1) ∘ (map-inv-equiv equiv1 ∘ map-equiv equiv2))
        by
          preserves-sum-permutation-Commutative-Semiring
            ( R)
            ( n)
            ( inv-equiv equiv1 ∘e equiv2)
            ( f ∘ map-equiv equiv1)
      ＝
        sum-Commutative-Semiring
          ( R)
          ( n)
          ( f ∘ (map-equiv equiv1 ∘ (map-inv-equiv equiv1 ∘ map-equiv equiv2)))
        by
          ap
            ( sum-Commutative-Semiring R n)
            ( associative-comp f (map-equiv equiv1) _)
      ＝
        sum-Commutative-Semiring
          ( R)
          ( n)
          ( f ∘ ((map-equiv equiv1 ∘ map-inv-equiv equiv1) ∘ map-equiv equiv2))
        by
          ap
            ( λ g → sum-Commutative-Semiring R n (f ∘ g))
            ( inv
              ( associative-comp (map-equiv equiv1) (map-inv-equiv equiv1) _))
      ＝ sum-Commutative-Semiring R n (f ∘ map-equiv equiv2)
        by
          ap
            ( λ g → sum-Commutative-Semiring R n (f ∘ (g ∘ map-equiv equiv2)))
            ( eq-htpy (is-section-map-inv-equiv equiv1))

    eq-sum-count-Commutative-Semiring :
      (f : A → type-Commutative-Semiring R) (c1 c2 : count A) →
      sum-count-Commutative-Semiring R A c1 f ＝
      sum-count-Commutative-Semiring R A c2 f
    eq-sum-count-Commutative-Semiring f c1@(n , e1) c2@(_ , e2)
      with eq-number-of-elements-count A c1 c2
    ... | refl = eq-sum-count-equiv-Commutative-Semiring n e1 e2 f
```

### Sums over finite types

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1) (A : Finite-Type l2)
  where

  sum-finite-Commutative-Semiring :
    (f : type-Finite-Type A → type-Commutative-Semiring R) →
    type-Commutative-Semiring R
  sum-finite-Commutative-Semiring f =
    map-universal-property-set-quotient-trunc-Prop
      ( set-Commutative-Semiring R)
      ( λ c → sum-count-Commutative-Semiring R (type-Finite-Type A) c f)
      ( eq-sum-count-Commutative-Semiring R (type-Finite-Type A) f)
      ( is-finite-type-Finite-Type A)
```
