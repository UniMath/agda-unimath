# Sums of finite families of elements in commutative semirings

```agda
module commutative-algebra.sums-of-finite-families-of-elements-commutative-semirings where
```

<details><summary>Imports</summary>

```agda
open import commutative-algebra.commutative-semirings
open import commutative-algebra.sums-of-finite-sequences-of-elements-commutative-semirings

open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.automorphisms
open import foundation.coproduct-types
open import foundation.decidable-subtypes
open import foundation.empty-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negation
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.finite-sequences-in-commutative-semirings

open import lists.finite-sequences

open import ring-theory.sums-of-finite-families-of-elements-semirings

open import univalent-combinatorics.complements-decidable-subtypes
open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.decidable-subtypes
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite family of elements of a commutative semiring" WD="sum" WDID=Q218005 Agda=sum-finite-Commutative-Semiring}}
extends the binary addition operation on a
[commutative semiring](commutative-algebra.commutative-semirings.md) `R` to any
[finite sequence](lists.finite-sequences.md) of elements of `R`.

## Definition

```agda
sum-count-Commutative-Semiring :
  {l1 l2 : Level} (R : Commutative-Semiring l1) (A : UU l2) → count A →
  (A → type-Commutative-Semiring R) → type-Commutative-Semiring R
sum-count-Commutative-Semiring R =
  sum-count-Semiring (semiring-Commutative-Semiring R)

sum-finite-Commutative-Semiring :
  {l1 l2 : Level} (R : Commutative-Semiring l1) (A : Finite-Type l2) →
  (type-Finite-Type A → type-Commutative-Semiring R) →
  type-Commutative-Semiring R
sum-finite-Commutative-Semiring R =
  sum-finite-Semiring (semiring-Commutative-Semiring R)
```

## Properties

### Sums over the unit type

```agda
module _
  {l : Level} (A : Commutative-Semiring l)
  where

  sum-unit-finite-Commutative-Semiring :
    (f : unit → type-Commutative-Semiring A) →
    sum-finite-Commutative-Semiring A unit-Finite-Type f ＝ f star
  sum-unit-finite-Commutative-Semiring =
    sum-unit-finite-Semiring (semiring-Commutative-Semiring A)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  htpy-sum-finite-Commutative-Semiring :
    {l2 : Level} (A : Finite-Type l2) →
    {f g : type-Finite-Type A → type-Commutative-Semiring R} → (f ~ g) →
    sum-finite-Commutative-Semiring R A f ＝
    sum-finite-Commutative-Semiring R A g
  htpy-sum-finite-Commutative-Semiring =
    htpy-sum-finite-Semiring (semiring-Commutative-Semiring R)
```

### Multiplication distributes over sums

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  left-distributive-mul-sum-finite-Commutative-Semiring :
    {l2 : Level} (A : Finite-Type l2) (x : type-Commutative-Semiring R) →
    (f : type-Finite-Type A → type-Commutative-Semiring R) →
    mul-Commutative-Semiring R x (sum-finite-Commutative-Semiring R A f) ＝
    sum-finite-Commutative-Semiring R A (mul-Commutative-Semiring R x ∘ f)
  left-distributive-mul-sum-finite-Commutative-Semiring =
    left-distributive-mul-sum-finite-Semiring (semiring-Commutative-Semiring R)

  right-distributive-mul-sum-finite-Commutative-Semiring :
    {l2 : Level} (A : Finite-Type l2) →
    (f : type-Finite-Type A → type-Commutative-Semiring R) →
    (x : type-Commutative-Semiring R) →
    mul-Commutative-Semiring R (sum-finite-Commutative-Semiring R A f) x ＝
    sum-finite-Commutative-Semiring R A (mul-Commutative-Semiring' R x ∘ f)
  right-distributive-mul-sum-finite-Commutative-Semiring =
    right-distributive-mul-sum-finite-Semiring (semiring-Commutative-Semiring R)
```

### Sums over finite types are preserved by equivalences

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Semiring l1)
  (A : Finite-Type l2) (B : Finite-Type l3) (H : equiv-Finite-Type A B)
  where

  sum-equiv-finite-Commutative-Semiring :
    (f : type-Finite-Type A → type-Commutative-Semiring R) →
    sum-finite-Commutative-Semiring R A f ＝
    sum-finite-Commutative-Semiring R B (f ∘ map-inv-equiv H)
  sum-equiv-finite-Commutative-Semiring =
    sum-equiv-finite-Semiring (semiring-Commutative-Semiring R) A B H

module _
  {l1 l2 : Level} (R : Commutative-Semiring l1)
  (A : Finite-Type l2) (σ : Aut (type-Finite-Type A))
  where

  sum-aut-finite-Commutative-Semiring :
    (f : type-Finite-Type A → type-Commutative-Semiring R) →
    sum-finite-Commutative-Semiring R A f ＝
    sum-finite-Commutative-Semiring R A (f ∘ map-equiv σ)
  sum-aut-finite-Commutative-Semiring =
    sum-equiv-finite-Commutative-Semiring R A A (inv-equiv σ)
```

### Sums over finite types distribute over coproducts

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Semiring l1)
  (A : Finite-Type l2) (B : Finite-Type l3)
  where

  distributive-sum-coproduct-finite-Commutative-Semiring :
    (f :
      type-Finite-Type A + type-Finite-Type B → type-Commutative-Semiring R) →
    sum-finite-Commutative-Semiring R (coproduct-Finite-Type A B) f ＝
    add-Commutative-Semiring
      ( R)
      ( sum-finite-Commutative-Semiring R A (f ∘ inl))
      ( sum-finite-Commutative-Semiring R B (f ∘ inr))
  distributive-sum-coproduct-finite-Commutative-Semiring =
    distributive-sum-coproduct-finite-Semiring
      ( semiring-Commutative-Semiring R)
      ( A)
      ( B)
```

### Sums distribute over dependent pair types

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Semiring l1)
  (A : Finite-Type l2) (B : type-Finite-Type A → Finite-Type l3)
  where

  sum-Σ-finite-Commutative-Semiring :
    (f :
      (a : type-Finite-Type A) →
      type-Finite-Type (B a) →
      type-Commutative-Semiring R) →
    sum-finite-Commutative-Semiring R (Σ-Finite-Type A B) (ind-Σ f) ＝
    sum-finite-Commutative-Semiring
      R A (λ a → sum-finite-Commutative-Semiring R (B a) (f a))
  sum-Σ-finite-Commutative-Semiring =
    sum-Σ-finite-Semiring (semiring-Commutative-Semiring R) A B
```

### The sum over an empty type is zero

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1) (A : Finite-Type l2)
  (H : is-empty (type-Finite-Type A))
  where

  eq-zero-sum-finite-is-empty-Commutative-Semiring :
    (f : type-Finite-Type A → type-Commutative-Semiring R) →
    is-zero-Commutative-Semiring R (sum-finite-Commutative-Semiring R A f)
  eq-zero-sum-finite-is-empty-Commutative-Semiring =
    eq-zero-sum-finite-is-empty-Semiring (semiring-Commutative-Semiring R) A H
```

### The sum over a finite type is the sum over any count for that type

```agda
eq-sum-finite-sum-count-Commutative-Semiring :
  {l1 l2 : Level} (R : Commutative-Semiring l1) (A : Finite-Type l2)
  (cA : count (type-Finite-Type A))
  (f : type-Finite-Type A → type-Commutative-Semiring R) →
  sum-finite-Commutative-Semiring R A f ＝
  sum-count-Commutative-Semiring R (type-Finite-Type A) cA f
eq-sum-finite-sum-count-Commutative-Semiring R =
  eq-sum-finite-sum-count-Semiring (semiring-Commutative-Semiring R)
```

### Interchange law of sums and addition

```agda
module _
  {l1 l2 : Level} (R : Commutative-Semiring l1) (A : Finite-Type l2)
  where

  interchange-sum-add-finite-Commutative-Semiring :
    (f g : type-Finite-Type A → type-Commutative-Semiring R) →
    sum-finite-Commutative-Semiring R A
      (λ a → add-Commutative-Semiring R (f a) (g a)) ＝
    add-Commutative-Semiring R
      (sum-finite-Commutative-Semiring R A f)
      (sum-finite-Commutative-Semiring R A g)
  interchange-sum-add-finite-Commutative-Semiring =
    interchange-sum-add-finite-Semiring (semiring-Commutative-Semiring R) A
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (R : Commutative-Semiring l)
  where

  sum-zero-finite-Commutative-Semiring :
    {l2 : Level} (A : Finite-Type l2) →
    sum-finite-Commutative-Semiring R A (λ _ → zero-Commutative-Semiring R) ＝
    zero-Commutative-Semiring R
  sum-zero-finite-Commutative-Semiring =
    sum-zero-finite-Semiring (semiring-Commutative-Semiring R)
```

### Decomposing sums via decidable subtypes

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Semiring l1) (A : Finite-Type l2)
  (P : subset-Finite-Type l3 A)
  where

  abstract
    decompose-sum-decidable-subset-finite-Commutative-Semiring :
      (f : type-Finite-Type A → type-Commutative-Semiring R) →
      sum-finite-Commutative-Semiring R A f ＝
      add-Commutative-Semiring R
        ( sum-finite-Commutative-Semiring R
          ( finite-type-subset-Finite-Type A P)
          ( f ∘ inclusion-subset-Finite-Type A P))
        ( sum-finite-Commutative-Semiring R
          ( finite-type-complement-subset-Finite-Type A P)
          ( f ∘ inclusion-complement-subset-Finite-Type A P))
    decompose-sum-decidable-subset-finite-Commutative-Semiring =
      decompose-sum-decidable-subset-finite-Semiring
        ( semiring-Commutative-Semiring R)
        ( A)
        ( P)
```

### Sums that vanish on a decidable subtype

```agda
module _
  {l1 l2 l3 : Level} (R : Commutative-Semiring l1) (A : Finite-Type l2)
  (P : subset-Finite-Type l3 A)
  where

  abstract
    vanish-sum-decidable-subset-finite-Commutative-Semiring :
      (f : type-Finite-Type A → type-Commutative-Semiring R) →
      ( (a : type-Finite-Type A) → is-in-decidable-subtype P a →
        is-zero-Commutative-Semiring R (f a)) →
      sum-finite-Commutative-Semiring R A f ＝
      sum-finite-Commutative-Semiring R
        ( finite-type-complement-subset-Finite-Type A P)
        ( f ∘ inclusion-complement-subset-Finite-Type A P)
    vanish-sum-decidable-subset-finite-Commutative-Semiring =
      vanish-sum-decidable-subset-finite-Semiring
        ( semiring-Commutative-Semiring R)
        ( A)
        ( P)

    vanish-sum-complement-decidable-subset-finite-Commutative-Semiring :
      (f : type-Finite-Type A → type-Commutative-Semiring R) →
      ( (a : type-Finite-Type A) → ¬ (is-in-decidable-subtype P a) →
        is-zero-Commutative-Semiring R (f a)) →
      sum-finite-Commutative-Semiring R A f ＝
      sum-finite-Commutative-Semiring R
        ( finite-type-subset-Finite-Type A P)
        ( f ∘ inclusion-subset-Finite-Type A P)
    vanish-sum-complement-decidable-subset-finite-Commutative-Semiring =
      vanish-sum-complement-decidable-subset-finite-Semiring
        ( semiring-Commutative-Semiring R)
        ( A)
        ( P)
```
