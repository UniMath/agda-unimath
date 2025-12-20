# Sums of finite families of elements in abelian groups

```agda
module group-theory.sums-of-finite-families-of-elements-abelian-groups where
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

open import group-theory.abelian-groups
open import group-theory.products-of-finite-families-of-elements-commutative-monoids
open import group-theory.sums-of-finite-sequences-of-elements-abelian-groups

open import univalent-combinatorics.coproduct-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.dependent-pair-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The
{{#concept "sum operation" Disambiguation="of a finite family of elements of a abelian group" WD="sum" WDID=Q218005 Agda=sum-finite-Ab}}
extends the binary addition operation on a
[abelian group](ring-theory.semirings.md) `G` to any family of elements of `G`
indexed by a [finite type](univalent-combinatorics.finite-types.md).

## Definition

```agda
sum-count-Ab :
  {l1 l2 : Level} (G : Ab l1) (A : UU l2) (cA : count A) →
  (A → type-Ab G) → type-Ab G
sum-count-Ab G =
  product-count-Commutative-Monoid (commutative-monoid-Ab G)

sum-finite-Ab :
  {l1 l2 : Level} (G : Ab l1) (A : Finite-Type l2) →
  (type-Finite-Type A → type-Ab G) → type-Ab G
sum-finite-Ab G =
  product-finite-Commutative-Monoid (commutative-monoid-Ab G)
```

## Properties

### Sums over the unit type

```agda
module _
  {l : Level} (G : Ab l)
  where

  abstract
    sum-unit-finite-type-Ab :
      (f : unit → type-Ab G) →
      sum-finite-Ab G unit-Finite-Type f ＝ f star
    sum-unit-finite-type-Ab =
      product-finite-unit-type-Commutative-Monoid (commutative-monoid-Ab G)
```

### Sums are homotopy invariant

```agda
module _
  {l : Level} (G : Ab l)
  where

  abstract
    htpy-sum-finite-Ab :
      {l2 : Level} (A : Finite-Type l2) →
      {f g : type-Finite-Type A → type-Ab G} → (f ~ g) →
      sum-finite-Ab G A f ＝ sum-finite-Ab G A g
    htpy-sum-finite-Ab =
      htpy-product-finite-Commutative-Monoid (commutative-monoid-Ab G)
```

### A sum of zeroes is zero

```agda
module _
  {l : Level} (G : Ab l)
  where

  abstract
    sum-zero-finite-Ab :
      {l2 : Level} (A : Finite-Type l2) →
      sum-finite-Ab G A (λ _ → zero-Ab G) ＝ zero-Ab G
    sum-zero-finite-Ab =
      product-unit-finite-Commutative-Monoid (commutative-monoid-Ab G)
```

### Sums over finite types are preserved by equivalences

```agda
module _
  {l1 l2 l3 : Level} (G : Ab l1) (A : Finite-Type l2) (B : Finite-Type l3)
  (H : equiv-Finite-Type A B)
  where

  abstract
    sum-equiv-finite-Ab :
      (f : type-Finite-Type A → type-Ab G) →
      sum-finite-Ab G A f ＝ sum-finite-Ab G B (f ∘ map-inv-equiv H)
    sum-equiv-finite-Ab =
      product-equiv-finite-Commutative-Monoid
        ( commutative-monoid-Ab G)
        ( A)
        ( B)
        ( H)
```

### Sums over finite types distribute over coproducts

```agda
module _
  {l1 l2 l3 : Level} (G : Ab l1) (A : Finite-Type l2) (B : Finite-Type l3)
  where

  abstract
    distributive-sum-coproduct-finite-Ab :
      (f :
        type-Finite-Type A + type-Finite-Type B → type-Ab G) →
      sum-finite-Ab G (coproduct-Finite-Type A B) f ＝
      add-Ab
        ( G)
        ( sum-finite-Ab G A (f ∘ inl))
        ( sum-finite-Ab G B (f ∘ inr))
    distributive-sum-coproduct-finite-Ab =
      distributive-product-coproduct-finite-Commutative-Monoid
        ( commutative-monoid-Ab G)
        ( A)
        ( B)
```

### Sums distribute over dependent pair types

```agda
module _
  {l1 l2 l3 : Level} (G : Ab l1)
  (A : Finite-Type l2) (B : type-Finite-Type A → Finite-Type l3)
  where

  abstract
    sum-Σ-finite-Ab :
      (f : (a : type-Finite-Type A) → type-Finite-Type (B a) → type-Ab G) →
      sum-finite-Ab G (Σ-Finite-Type A B) (ind-Σ f) ＝
      sum-finite-Ab G A (λ a → sum-finite-Ab G (B a) (f a))
    sum-Σ-finite-Ab =
      product-Σ-finite-Commutative-Monoid (commutative-monoid-Ab G) A B
```

### The sum over an empty type is zero

```agda
module _
  {l1 l2 : Level} (G : Ab l1) (A : Finite-Type l2)
  (H : is-empty (type-Finite-Type A))
  where

  abstract
    is-zero-sum-finite-is-empty-Ab :
      (f : type-Finite-Type A → type-Ab G) →
      is-zero-Ab G (sum-finite-Ab G A f)
    is-zero-sum-finite-is-empty-Ab =
      eq-unit-product-finite-is-empty-Commutative-Monoid
        ( commutative-monoid-Ab G)
        ( A)
        ( H)
```

### The sum over a finite type is the sum over any count for that type

```agda
abstract
  eq-sum-finite-sum-count-Ab :
    {l1 l2 : Level} (G : Ab l1) (A : Finite-Type l2)
    (cA : count (type-Finite-Type A))
    (f : type-Finite-Type A → type-Ab G) →
    sum-finite-Ab G A f ＝ sum-count-Ab G (type-Finite-Type A) cA f
  eq-sum-finite-sum-count-Ab G =
    eq-product-finite-product-count-Commutative-Monoid
      ( commutative-monoid-Ab G)
```

### Interchange law of sums and addition

```agda
module _
  {l1 l2 : Level} (G : Ab l1) (A : Finite-Type l2)
  where

  abstract
    interchange-sum-add-finite-Ab :
      (f g : type-Finite-Type A → type-Ab G) →
      sum-finite-Ab G A (λ a → add-Ab G (f a) (g a)) ＝
      add-Ab G (sum-finite-Ab G A f) (sum-finite-Ab G A g)
    interchange-sum-add-finite-Ab =
      interchange-product-mul-finite-Commutative-Monoid
        ( commutative-monoid-Ab G)
        ( A)
```

### Interchange law of sums and negation

```agda
module _
  {l1 l2 : Level} (G : Ab l1) (A : Finite-Type l2)
  where

  abstract
    interchange-sum-neg-finite-Ab :
      (f : type-Finite-Type A → type-Ab G) →
      sum-finite-Ab G A (λ a → neg-Ab G (f a)) ＝ neg-Ab G (sum-finite-Ab G A f)
    interchange-sum-neg-finite-Ab f =
      unique-right-inv-Ab G
        ( equational-reasoning
          add-Ab G
            ( sum-finite-Ab G A f)
            ( sum-finite-Ab G A (λ a → neg-Ab G (f a)))
          ＝ sum-finite-Ab G A (λ a → add-Ab G (f a) (neg-Ab G (f a)))
            by inv (interchange-sum-add-finite-Ab G A _ _)
          ＝ sum-finite-Ab G A (λ _ → zero-Ab G)
            by htpy-sum-finite-Ab G A (λ a → right-inverse-law-add-Ab G _)
          ＝ zero-Ab G by sum-zero-finite-Ab G A)
```
