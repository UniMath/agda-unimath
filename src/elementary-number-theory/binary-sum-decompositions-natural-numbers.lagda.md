# Binary sum decompositions of natural numbers

```agda
module elementary-number-theory.binary-sum-decompositions-natural-numbers where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.strict-inequality-natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.cartesian-product-types
open import foundation.complements-subtypes
open import foundation.conjunction
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.involutions
open import foundation.negation
open import foundation.propositions
open import foundation.retractions
open import foundation.sections
open import foundation.sets
open import foundation.subtypes
open import foundation.type-arithmetic-coproduct-types
open import foundation.unit-type
open import foundation.universe-levels

open import logic.complements-decidable-subtypes

open import univalent-combinatorics.classical-finite-types
open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A binary sum decomposition of a
[natural number](elementary-number-theory.natural-numbers.md) `n : ℕ` resembles
an [integer partition](elementary-number-theory.integer-partitions.md), but is
ordered, and the components may be zero.

## Definition

```agda
binary-sum-decomposition-ℕ : ℕ → UU lzero
binary-sum-decomposition-ℕ n = Σ ℕ ( λ a → Σ ℕ (λ b → b +ℕ a ＝ n))
```

## Properties

### Equality characterization

```agda
module _
  (n : ℕ)
  where

  Eq-binary-sum-decomposition-ℕ :
    binary-sum-decomposition-ℕ n → binary-sum-decomposition-ℕ n → UU lzero
  Eq-binary-sum-decomposition-ℕ (a , b , _) (a' , b' , _) = a ＝ a'

  is-prop-Eq-binary-sum-decomposition-ℕ :
    (x y : binary-sum-decomposition-ℕ n) →
    is-prop (Eq-binary-sum-decomposition-ℕ x y)
  is-prop-Eq-binary-sum-decomposition-ℕ (a , _) (a' , _) =
    is-prop-type-Prop (Id-Prop ℕ-Set a a')

  refl-Eq-binary-sum-decomposition-ℕ :
    (x : binary-sum-decomposition-ℕ n) → Eq-binary-sum-decomposition-ℕ x x
  refl-Eq-binary-sum-decomposition-ℕ _ = refl

  eq-Eq-binary-sum-decomposition-ℕ :
    (x y : binary-sum-decomposition-ℕ n) → Eq-binary-sum-decomposition-ℕ x y →
    x ＝ y
  eq-Eq-binary-sum-decomposition-ℕ (a , b , b+a=n) (.a , b' , b'+a=n) refl =
    eq-pair-eq-fiber
      ( eq-pair-Σ
        ( is-injective-right-add-ℕ a (b+a=n ∙ inv b'+a=n))
        ( eq-type-Prop (Id-Prop ℕ-Set _ _)))

  abstract
    is-set-binary-sum-decomposition-ℕ : is-set (binary-sum-decomposition-ℕ n)
    is-set-binary-sum-decomposition-ℕ =
      is-set-prop-in-id
        Eq-binary-sum-decomposition-ℕ
        is-prop-Eq-binary-sum-decomposition-ℕ
        refl-Eq-binary-sum-decomposition-ℕ
        eq-Eq-binary-sum-decomposition-ℕ

  set-binary-sum-decomposition-ℕ : Set lzero
  set-binary-sum-decomposition-ℕ =
    ( binary-sum-decomposition-ℕ n ,
      is-set-binary-sum-decomposition-ℕ)
```

### Involution of swapping the components

```agda
module _
  (n : ℕ)
  where

  swap-binary-sum-decomposition-ℕ :
    binary-sum-decomposition-ℕ n → binary-sum-decomposition-ℕ n
  swap-binary-sum-decomposition-ℕ (a , b , b+a=n) =
    (b , a , commutative-add-ℕ a b ∙ b+a=n)

  is-involution-swap-binary-sum-decomposition-ℕ :
    is-involution swap-binary-sum-decomposition-ℕ
  is-involution-swap-binary-sum-decomposition-ℕ _ =
    eq-Eq-binary-sum-decomposition-ℕ n _ _ refl

  aut-swap-binary-sum-decomposition-ℕ : Aut (binary-sum-decomposition-ℕ n)
  aut-swap-binary-sum-decomposition-ℕ =
    ( swap-binary-sum-decomposition-ℕ ,
      is-equiv-is-involution is-involution-swap-binary-sum-decomposition-ℕ)
```

### Equivalence of dependent pairs further partitioning a component

```agda
module _
  (n : ℕ)
  where

  map-equiv-binary-sum-decomposition-pr1-pr2 :
    Σ (binary-sum-decomposition-ℕ n) (binary-sum-decomposition-ℕ ∘ pr1) →
    Σ (binary-sum-decomposition-ℕ n) (binary-sum-decomposition-ℕ ∘ pr1 ∘ pr2)
  pr1 (map-equiv-binary-sum-decomposition-pr1-pr2 ((p , c , c+p=n) , _)) =
    (c , p , commutative-add-ℕ p c ∙ c+p=n)
  pr2 (map-equiv-binary-sum-decomposition-pr1-pr2 (_ , y)) = y

  map-inv-equiv-binary-sum-decomposition-pr1-pr2 :
    Σ (binary-sum-decomposition-ℕ n) (binary-sum-decomposition-ℕ ∘ pr1 ∘ pr2) →
    Σ (binary-sum-decomposition-ℕ n) (binary-sum-decomposition-ℕ ∘ pr1)
  pr1 (map-inv-equiv-binary-sum-decomposition-pr1-pr2 ((c , p , p+c=n) , _)) =
    (p , c , commutative-add-ℕ c p ∙ p+c=n)
  pr2 (map-inv-equiv-binary-sum-decomposition-pr1-pr2 (_ , y)) = y

  abstract
    is-section-map-inv-equiv-binary-sum-decomposition-pr1-pr2 :
      is-section
        map-equiv-binary-sum-decomposition-pr1-pr2
        map-inv-equiv-binary-sum-decomposition-pr1-pr2
    is-section-map-inv-equiv-binary-sum-decomposition-pr1-pr2
      x@((c , p , p+c=n) , a , b , b+a=p) =
        inv
          ( ind-Id
            ( p+c=n)
            ( λ H' H=H' → x ＝ ((c , p , H') , a , b , b+a=p))
            ( refl)
            ( _)
            ( eq-type-Prop (Id-Prop ℕ-Set _ _)))

    is-retraction-map-inv-equiv-binary-sum-decomposition-pr1-pr2 :
      is-retraction
        map-equiv-binary-sum-decomposition-pr1-pr2
        map-inv-equiv-binary-sum-decomposition-pr1-pr2
    is-retraction-map-inv-equiv-binary-sum-decomposition-pr1-pr2
      x@((p , c , c+p=n) , a , b , b+a=p) =
        inv
          ( ind-Id
            ( c+p=n)
            ( λ H' H=H' → x ＝ ((p , c , H') , a , b , b+a=p))
            ( refl)
            ( _)
            ( eq-type-Prop (Id-Prop ℕ-Set _ _)))

  equiv-binary-sum-decomposition-pr1-pr2 :
    Σ (binary-sum-decomposition-ℕ n) (binary-sum-decomposition-ℕ ∘ pr1) ≃
    Σ (binary-sum-decomposition-ℕ n) (binary-sum-decomposition-ℕ ∘ pr1 ∘ pr2)
  pr1 equiv-binary-sum-decomposition-pr1-pr2 =
    map-equiv-binary-sum-decomposition-pr1-pr2
  pr2 equiv-binary-sum-decomposition-pr1-pr2 =
    is-equiv-is-invertible
      ( map-inv-equiv-binary-sum-decomposition-pr1-pr2)
      ( is-section-map-inv-equiv-binary-sum-decomposition-pr1-pr2)
      ( is-retraction-map-inv-equiv-binary-sum-decomposition-pr1-pr2)
```

### Pairs with a fixed sum are a finite type

```agda
module _
  (n : ℕ)
  where

  equiv-binary-sum-decomposition-leq-ℕ :
    Σ ℕ (λ k → leq-ℕ k n) ≃ binary-sum-decomposition-ℕ n
  pr1 equiv-binary-sum-decomposition-leq-ℕ (k , k≤n) =
    (k , subtraction-leq-ℕ k n k≤n)
  pr2 equiv-binary-sum-decomposition-leq-ℕ =
    is-equiv-is-invertible
      ( λ (k , l , l+k=n) → k , leq-subtraction-ℕ k n l l+k=n)
      ( λ (k , l , l+k=n) →
        let
          (l' , l'+k=n) =
            subtraction-leq-ℕ k n (leq-subtraction-ℕ k n l l+k=n)
        in
          eq-pair-eq-fiber
            ( eq-pair-Σ
              ( is-injective-right-add-ℕ k (l'+k=n ∙ inv l+k=n))
              ( eq-type-Prop (Id-Prop ℕ-Set (l +ℕ k) n))))
    ( λ (k , k≤n) → eq-pair-eq-fiber (eq-type-Prop (leq-ℕ-Prop k n)))

  count-binary-sum-decomposition-ℕ : count (binary-sum-decomposition-ℕ n)
  pr1 count-binary-sum-decomposition-ℕ = succ-ℕ n
  pr2 count-binary-sum-decomposition-ℕ =
    equiv-binary-sum-decomposition-leq-ℕ ∘e
    equiv-le-succ-ℕ-leq-ℕ n ∘e
    equiv-classical-standard-Fin (succ-ℕ n)

  count-reverse-binary-sum-decomposition-ℕ :
    count (binary-sum-decomposition-ℕ n)
  pr1 count-reverse-binary-sum-decomposition-ℕ = succ-ℕ n
  pr2 count-reverse-binary-sum-decomposition-ℕ =
    equiv-binary-sum-decomposition-leq-ℕ ∘e
    equiv-le-succ-ℕ-leq-ℕ n ∘e
    equiv-classical-standard-Fin-reverse (succ-ℕ n)

  finite-type-binary-sum-decomposition-ℕ : Finite-Type lzero
  finite-type-binary-sum-decomposition-ℕ =
    ( binary-sum-decomposition-ℕ n ,
      is-finite-count count-binary-sum-decomposition-ℕ)
```

### Permuting components in a triple of sums

```agda
module _
  (n : ℕ)
  where

  map-equiv-permute-components-triple-with-sum-pr2 :
    Σ (binary-sum-decomposition-ℕ n) (binary-sum-decomposition-ℕ ∘ pr1 ∘ pr2) →
    Σ (binary-sum-decomposition-ℕ n) (binary-sum-decomposition-ℕ ∘ pr1 ∘ pr2)
  map-equiv-permute-components-triple-with-sum-pr2
    ((c , p , p+c=n) , a , b , b+a=p) =
      ( b , a +ℕ c ,
        ( equational-reasoning
          (a +ℕ c) +ℕ b
          ＝ b +ℕ (a +ℕ c) by commutative-add-ℕ (a +ℕ c) b
          ＝ (b +ℕ a) +ℕ c by inv (associative-add-ℕ b a c)
          ＝ p +ℕ c by ap (_+ℕ c) b+a=p
          ＝ n by p+c=n)) ,
        c , a , refl

  map-inv-equiv-permute-components-triple-with-sum-pr2 :
    Σ (binary-sum-decomposition-ℕ n) (binary-sum-decomposition-ℕ ∘ pr1 ∘ pr2) →
    Σ (binary-sum-decomposition-ℕ n) (binary-sum-decomposition-ℕ ∘ pr1 ∘ pr2)
  map-inv-equiv-permute-components-triple-with-sum-pr2
    ((c , p , p+c=n) , a , b , b+a=p) =
      ( a , c +ℕ b ,
        ( equational-reasoning
          (c +ℕ b) +ℕ a
          ＝ c +ℕ (b +ℕ a) by associative-add-ℕ c b a
          ＝ c +ℕ p by ap (c +ℕ_) b+a=p
          ＝ p +ℕ c by commutative-add-ℕ c p
          ＝ n by p+c=n)) ,
        b , c , refl

  abstract
    is-section-map-inv-equiv-permute-components-triple-with-sum-pr2 :
      is-section
        map-equiv-permute-components-triple-with-sum-pr2
        map-inv-equiv-permute-components-triple-with-sum-pr2
    is-section-map-inv-equiv-permute-components-triple-with-sum-pr2
      x@((c , .(b +ℕ a) , p+c=n) , a , b , refl) =
        inv
          ( ind-Id
            ( p+c=n)
            ( λ H' H=H' → x ＝ ((c , b +ℕ a , H') , a , b , refl))
            ( refl)
            ( _)
            ( eq-type-Prop (Id-Prop ℕ-Set _ _)))

    is-retraction-map-inv-equiv-permute-components-triple-with-sum-pr2 :
      is-retraction
        map-equiv-permute-components-triple-with-sum-pr2
        map-inv-equiv-permute-components-triple-with-sum-pr2
    is-retraction-map-inv-equiv-permute-components-triple-with-sum-pr2
      x@((c , .(b +ℕ a) , p+c=n) , a , b , refl) =
        inv
          ( ind-Id
            ( p+c=n)
            ( λ H' H=H' → x ＝ ((c , b +ℕ a , H') , a , b , refl))
            ( refl)
            ( _)
            ( eq-type-Prop (Id-Prop ℕ-Set _ _)))

  equiv-permute-components-triple-with-sum-pr2 :
    Aut
      ( Σ
        ( binary-sum-decomposition-ℕ n)
        ( binary-sum-decomposition-ℕ ∘ pr1 ∘ pr2))
  pr1 equiv-permute-components-triple-with-sum-pr2 =
    map-equiv-permute-components-triple-with-sum-pr2
  pr2 equiv-permute-components-triple-with-sum-pr2 =
    is-equiv-is-invertible
      ( map-inv-equiv-permute-components-triple-with-sum-pr2)
      ( is-section-map-inv-equiv-permute-components-triple-with-sum-pr2)
      ( is-retraction-map-inv-equiv-permute-components-triple-with-sum-pr2)
```
