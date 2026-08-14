# Inserting elements in finite sequences

```agda
{-# OPTIONS --lossy-unification #-}

module lists.insert-at-index-finite-sequences where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.unit-type
open import foundation.universe-levels

open import lists.finite-sequences
open import lists.functoriality-finite-sequences
open import lists.insert-at-index-finite-sequences-of-types
open import lists.remove-at-index-finite-sequences

open import univalent-combinatorics.equality-standard-finite-types
open import univalent-combinatorics.skipping-element-standard-finite-types
open import univalent-combinatorics.skipping-two-elements-standard-finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [natural number](elementary-number-theory.natural-numbers.md) `n : ℕ`
and a type `A`, the
{{#concept "insertion map" Disambiguation="of finite sequences" Agda=insert-at-fin-sequence}}
of an element `x : A` at an
[index](univalent-combinatorics.standard-finite-types.md) `i : Fin (n+1)` is the
map `Aⁿ → Aⁿ⁺¹` that **inserts** `x` at the `i`th coordinate:

```text
  (x₀,...xᵢ₋₁,xᵢ₊₁,...,xₙ) ↦ (x₀,...xᵢ₋₁,x,xᵢ₊₁,...,xₙ)
```

## Definitions

### Insertion at an index

```agda
module _
  {l : Level} {A : UU l}
  where

  insert-at-fin-sequence :
    (n : ℕ) → Fin (succ-ℕ n) → A → fin-sequence A n → fin-sequence A (succ-ℕ n)
  insert-at-fin-sequence n = insert-at-Π-fin-sequence n (λ _ → A)
```

### Insertion at two indices

```agda
module _
  {l : Level} {A : UU l}
  where

  insert-at-two-indices-fin-sequence :
    (n : ℕ) (i j : Fin (n +ℕ 2)) → i ≠ j → A → A →
    fin-sequence A n → fin-sequence A (n +ℕ 2)
  insert-at-two-indices-fin-sequence n =
    insert-at-two-indices-Π-fin-sequence n (λ _ → A)
```

## Properties

### The coordinate at the index of an inserted element is the inserted element

```agda
module _
  {l : Level} {A : UU l}
  where abstract

  compute-elem-at-insert-at-fin-sequence :
    (n : ℕ)
    (i : Fin (succ-ℕ n))
    (a : A)
    (u : fin-sequence A n) →
    elem-at-fin-sequence (succ-ℕ n) i (insert-at-fin-sequence n i a u) ＝
    a
  compute-elem-at-insert-at-fin-sequence n =
    compute-elem-at-insert-at-Π-fin-sequence n (λ _ → A)
```

### The coordinate at the first index of two inserted elements is the inserted element

```agda
module _
  {l : Level} {A : UU l}
  where abstract

  compute-first-elem-at-insert-at-two-indices-fin-sequence :
    (n : ℕ) (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) (aᵢ aⱼ : A)
    (u : fin-sequence A n) →
    insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u i ＝ aᵢ
  compute-first-elem-at-insert-at-two-indices-fin-sequence n =
    compute-first-elem-at-insert-at-two-indices-Π-fin-sequence n (λ _ → A)
```

### The coordinate at the second index of two inserted elements is the inserted element

```agda
module _
  {l : Level} {A : UU l}
  where abstract

  compute-second-elem-at-insert-at-two-indices-fin-sequence :
    (n : ℕ) (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) (aᵢ aⱼ : A)
    (u : fin-sequence A n) →
    insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u j ＝ aⱼ
  compute-second-elem-at-insert-at-two-indices-fin-sequence n =
    compute-second-elem-at-insert-at-two-indices-Π-fin-sequence n (λ _ → A)
```

### Insertion is functorial

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where abstract

  htpy-map-insert-at-fin-sequence :
    (n : ℕ) →
    (x : A) →
    (i : Fin (succ-ℕ n)) →
    (u : fin-sequence A n) →
    insert-at-fin-sequence n
      ( i)
      ( f x)
      ( map-fin-sequence n f u) ~
    map-fin-sequence (succ-ℕ n) f (insert-at-fin-sequence n i x u)
  htpy-map-insert-at-fin-sequence zero-ℕ x (inr star) u (inr star) = refl
  htpy-map-insert-at-fin-sequence (succ-ℕ n) x (inl i) u (inl j) =
    htpy-map-insert-at-fin-sequence n x i (tail-fin-sequence n u) j
  htpy-map-insert-at-fin-sequence (succ-ℕ n) x (inl i) u (inr j) = refl
  htpy-map-insert-at-fin-sequence (succ-ℕ n) x (inr _) u (inl j) = refl
  htpy-map-insert-at-fin-sequence (succ-ℕ n) x (inr _) u (inr j) = refl
```

### Inserting a removed element is the identity

```agda
module _
  {l : Level} {A : UU l}
  where abstract

  compute-insert-at-remove-at-fin-sequence :
    (n : ℕ) →
    (i : Fin (succ-ℕ n)) →
    (u : fin-sequence A (succ-ℕ n)) →
    insert-at-fin-sequence
      ( n)
      ( i)
      ( elem-at-fin-sequence (succ-ℕ n) i u)
      ( remove-at-fin-sequence n i u) ~
    u
  compute-insert-at-remove-at-fin-sequence n =
    compute-insert-at-remove-at-Π-fin-sequence n (λ _ → A)
```

### Removing an inserted element is the identity

```agda
module _
  {l : Level} {A : UU l}
  where abstract

  compute-remove-at-insert-at-fin-sequence :
    (n : ℕ)
    (i : Fin (succ-ℕ n))
    (a : A)
    (u : fin-sequence A n) →
    remove-at-fin-sequence
      ( n)
      ( i)
      ( insert-at-fin-sequence n i a u) ~
    u
  compute-remove-at-insert-at-fin-sequence n =
    compute-remove-at-insert-at-Π-fin-sequence n (λ _ → A)
```

### Removing two inserted elements is the identity

```agda
module _
  {l : Level} {A : UU l}
  where abstract

  compute-remove-at-insert-at-two-indices-fin-sequence :
    (n : ℕ)
    (i j : Fin (n +ℕ 2))
    (i≠j : i ≠ j)
    (aᵢ aⱼ : A)
    (u : fin-sequence A n) →
    remove-at-two-indices-fin-sequence
      ( n)
      ( i)
      ( j)
      ( i≠j)
      ( insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u) ~
    u
  compute-remove-at-insert-at-two-indices-fin-sequence n =
    compute-remove-at-insert-at-two-indices-Π-fin-sequence n (λ _ → A)
```

### Inserting two elements in terms of inserting one element

```agda
module _
  {l : Level} {A : UU l}
  where

  insert-at-two-indices-fin-sequence' :
    (n : ℕ) (i j : Fin (n +ℕ 2)) → i ≠ j → A → A →
    fin-sequence A n → fin-sequence A (n +ℕ 2)
  insert-at-two-indices-fin-sequence' n i j i≠j aᵢ aⱼ u =
    let
      (j' , _) = fiber-skip-Fin (succ-ℕ n) i j i≠j
    in
      insert-at-fin-sequence
        ( succ-ℕ n)
        ( i)
        ( aᵢ)
        ( insert-at-fin-sequence n j' aⱼ u)

  abstract
    htpy-insert-at-two-indices-fin-sequence' :
      (n : ℕ) (i j : Fin (n +ℕ 2)) (i≠j : i ≠ j) (aᵢ aⱼ : A)
      (u : fin-sequence A n) →
      insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u ~
      insert-at-two-indices-fin-sequence' n i j i≠j aᵢ aⱼ u
    htpy-insert-at-two-indices-fin-sequence' n i j i≠j aᵢ aⱼ u k =
      let
        (j' , snij'=j) = fiber-skip-Fin (succ-ℕ n) i j i≠j
        case-i=k i=k =
          equational-reasoning
            insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u k
            ＝ insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u i
              by
                ap
                  ( insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u)
                  ( inv i=k)
            ＝ aᵢ
              by
                compute-first-elem-at-insert-at-two-indices-fin-sequence
                  ( n)
                  ( i)
                  ( j)
                  ( i≠j)
                  ( aᵢ)
                  ( aⱼ)
                  ( u)
            ＝ insert-at-two-indices-fin-sequence' n i j i≠j aᵢ aⱼ u i
              by
                inv
                  ( compute-elem-at-insert-at-fin-sequence
                    ( succ-ℕ n)
                    ( i)
                    ( aᵢ)
                    ( insert-at-fin-sequence n j' aⱼ u))
            ＝ insert-at-two-indices-fin-sequence' n i j i≠j aᵢ aⱼ u k
              by ap (insert-at-two-indices-fin-sequence' n i j i≠j aᵢ aⱼ u) i=k
        case-j=k j=k =
          equational-reasoning
            insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u k
            ＝ insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u j
              by
                ap
                  ( insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u)
                  ( inv j=k)
            ＝ aⱼ
              by
                compute-second-elem-at-insert-at-two-indices-fin-sequence
                  ( n)
                  ( i)
                  ( j)
                  ( i≠j)
                  ( aᵢ)
                  ( aⱼ)
                  ( u)
            ＝ insert-at-fin-sequence n j' aⱼ u j'
              by inv (compute-elem-at-insert-at-fin-sequence n j' aⱼ u)
            ＝
              insert-at-two-indices-fin-sequence' n i j i≠j aᵢ aⱼ u
                ( skip-Fin (succ-ℕ n) i j')
              by
                inv
                  ( compute-remove-at-insert-at-fin-sequence
                    ( succ-ℕ n)
                    ( i)
                    ( aᵢ)
                    ( insert-at-fin-sequence n j' aⱼ u)
                    ( j'))
            ＝ insert-at-two-indices-fin-sequence' n i j i≠j aᵢ aⱼ u k
              by
                ap
                  ( insert-at-two-indices-fin-sequence' n i j i≠j aᵢ aⱼ u)
                  ( snij'=j ∙ j=k)
        case-else i≠k j≠k =
          let (k' , snijk'=k) = fiber-skip-two-Fin n i j i≠j k i≠k j≠k
          in
            equational-reasoning
              insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u k
              ＝
                remove-at-two-indices-fin-sequence n i j i≠j
                  ( insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u)
                  ( k')
                by
                  ap
                    ( insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u)
                    ( inv snijk'=k)
              ＝ u k'
                by
                  compute-remove-at-insert-at-two-indices-fin-sequence
                    ( n)
                    ( i)
                    ( j)
                    ( i≠j)
                    ( aᵢ)
                    ( aⱼ)
                    ( u)
                    ( k')
              ＝ insert-at-fin-sequence n j' aⱼ u (skip-Fin n j' k')
                by inv (compute-remove-at-insert-at-fin-sequence n j' aⱼ u k')
              ＝
                insert-at-two-indices-fin-sequence' n i j i≠j aᵢ aⱼ u
                  ( skip-two-Fin' n i j i≠j k')
                by
                  inv
                    ( compute-remove-at-insert-at-fin-sequence
                      ( succ-ℕ n)
                      ( i)
                      ( aᵢ)
                      ( insert-at-fin-sequence n j' aⱼ u)
                      ( skip-Fin n j' k'))
              ＝ insert-at-two-indices-fin-sequence' n i j i≠j aᵢ aⱼ u k
                by
                  ap
                    ( insert-at-two-indices-fin-sequence' n i j i≠j aᵢ aⱼ u)
                    ( inv (htpy-skip-two-Fin' n i j i≠j k') ∙ snijk'=k)
      in
        rec-coproduct
          ( case-i=k)
          ( λ i≠k →
            rec-coproduct
              ( case-j=k)
              ( case-else i≠k)
              ( has-decidable-equality-Fin (n +ℕ 2) j k))
          ( has-decidable-equality-Fin (n +ℕ 2) i k)
```

### Elements can be inserted at distinct indices in either order

```agda
module _
  {l : Level} {A : UU l}
  where abstract

  swap-insert-at-two-indices-fin-sequence :
    (n : ℕ)
    (i j : Fin (n +ℕ 2))
    (i≠j : i ≠ j)
    (aᵢ aⱼ : A)
    (u : fin-sequence A n) →
    insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u ~
    insert-at-two-indices-fin-sequence n j i
      ( is-symmetric-nonequal i j i≠j)
      ( aⱼ)
      ( aᵢ)
      ( u)
  swap-insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u k =
    let
      j≠i = is-symmetric-nonequal i j i≠j
      case-i=k i=k =
        ( ap (insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u) (inv i=k)) ∙
        ( compute-first-elem-at-insert-at-two-indices-fin-sequence
          ( n)
          ( i)
          ( j)
          ( i≠j)
          ( aᵢ)
          ( aⱼ)
          ( u)) ∙
        ( inv
          ( compute-second-elem-at-insert-at-two-indices-fin-sequence
            ( n)
            ( j)
            ( i)
            ( j≠i)
            ( aⱼ)
            ( aᵢ)
            ( u))) ∙
        ( ap (insert-at-two-indices-fin-sequence n j i j≠i aⱼ aᵢ u) i=k)
      case-j=k j=k =
        ( ap (insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u) (inv j=k)) ∙
        ( compute-second-elem-at-insert-at-two-indices-fin-sequence
          ( n)
          ( i)
          ( j)
          ( i≠j)
          ( aᵢ)
          ( aⱼ)
          ( u)) ∙
        ( inv
          ( compute-first-elem-at-insert-at-two-indices-fin-sequence
            ( n)
            ( j)
            ( i)
            ( j≠i)
            ( aⱼ)
            ( aᵢ)
            ( u))) ∙
        ( ap (insert-at-two-indices-fin-sequence n j i j≠i aⱼ aᵢ u) j=k)
      case-else i≠k j≠k =
        let
          (k' , snijk'=k) = fiber-skip-two-Fin n i j i≠j k i≠k j≠k
          snjik'=k = swap-skip-two-Fin n j i j≠i i≠j k' ∙ snijk'=k
        in
          ( ap
            ( insert-at-two-indices-fin-sequence n i j i≠j aᵢ aⱼ u)
            ( inv snijk'=k)) ∙
          ( compute-remove-at-insert-at-two-indices-fin-sequence
            ( n)
            ( i)
            ( j)
            ( i≠j)
            ( aᵢ)
            ( aⱼ)
            ( u)
            ( k')) ∙
          ( inv
            ( compute-remove-at-insert-at-two-indices-fin-sequence
              ( n)
              ( j)
              ( i)
              ( j≠i)
              ( aⱼ)
              ( aᵢ)
              ( u)
              ( k'))) ∙
          ( ap (insert-at-two-indices-fin-sequence n j i j≠i aⱼ aᵢ u) snjik'=k)
    in
      rec-coproduct
        ( case-i=k)
        ( λ i≠k →
          rec-coproduct
            ( case-j=k)
            ( case-else i≠k)
            ( has-decidable-equality-Fin (n +ℕ 2) j k))
        ( has-decidable-equality-Fin (n +ℕ 2) i k)
```

### Inserting at one of two removed indices

```agda
module _
  {l : Level} {A : UU l}
  where abstract opaque

  unfolding fiber-skip-Fin

  insert-at-second-remove-at-two-indices-fin-sequence :
    (n : ℕ)
    (i j : Fin (n +ℕ 2))
    (i≠j : i ≠ j)
    (u : fin-sequence A (n +ℕ 2)) →
    insert-at-fin-sequence
      ( n)
      ( pr1 (fiber-skip-Fin (succ-ℕ n) i j i≠j))
      ( u j)
      ( remove-at-two-indices-fin-sequence n i j i≠j u) ~
    remove-at-fin-sequence (succ-ℕ n) i u
  insert-at-second-remove-at-two-indices-fin-sequence
    n (inr star) (inr star) i≠j =
    ex-falso (i≠j refl)
  insert-at-second-remove-at-two-indices-fin-sequence
    zero-ℕ (inl (inr star)) (inl (inr star)) i≠j =
    ex-falso (i≠j refl)
  insert-at-second-remove-at-two-indices-fin-sequence
    zero-ℕ (inr star) (inl (inr star)) i≠j u (inr star) =
    refl
  insert-at-second-remove-at-two-indices-fin-sequence
    zero-ℕ (inl (inr star)) (inr star) i≠j u (inr star) =
    refl
  insert-at-second-remove-at-two-indices-fin-sequence
    (succ-ℕ n) (inl i) (inl j) i≠j u (inl k) =
    insert-at-second-remove-at-two-indices-fin-sequence
      ( n)
      ( i)
      ( j)
      ( nonequal-map inl i≠j)
      ( tail-fin-sequence (n +ℕ 2) u)
      ( k)
  insert-at-second-remove-at-two-indices-fin-sequence
    (succ-ℕ n) (inl i) (inl j) i≠j u (inr star) =
    refl
  insert-at-second-remove-at-two-indices-fin-sequence
    (succ-ℕ n) (inl i) (inr star) i≠j u (inl k) =
    refl
  insert-at-second-remove-at-two-indices-fin-sequence
    (succ-ℕ n) (inl i) (inr star) i≠j u (inr star) =
    refl
  insert-at-second-remove-at-two-indices-fin-sequence
    (succ-ℕ n) (inr star) (inl j) i≠j u k =
    compute-insert-at-remove-at-fin-sequence
      ( succ-ℕ n)
      ( j)
      ( tail-fin-sequence (n +ℕ 2) u)
      ( k)
```
