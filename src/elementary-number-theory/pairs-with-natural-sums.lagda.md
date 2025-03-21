# Pairs of natural numbers with a given sum

```agda
module elementary-number-theory.pairs-with-natural-sums where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers
open import elementary-number-theory.inequality-natural-numbers

open import foundation.negation
open import foundation.type-arithmetic-coproduct-types
open import foundation.contractible-types
open import foundation.action-on-identifications-functions
open import foundation.automorphisms
open import foundation.decidable-subtypes
open import foundation.subtypes
open import foundation.complements-subtypes
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.functoriality-coproduct-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.cartesian-product-types
open import foundation.retractions
open import foundation.sections
open import foundation.complements-decidable-subtypes
open import foundation.sets
open import foundation.conjunction
open import foundation.universe-levels
open import foundation.unit-type

open import univalent-combinatorics.counting
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A pair of natural numbers with a specific known sum resembles an
[integer partition](elementary-number-theory.integer-partitions.md), but is
ordered, and the components may be zero.

## Definition

```agda
pair-with-sum-ℕ : ℕ → UU lzero
pair-with-sum-ℕ n = Σ ℕ ( λ a → Σ ℕ (λ b → b +ℕ a ＝ n))
```

## Properties

### Equality characterization

```agda
module _
  (n : ℕ)
  where

  Eq-pair-with-sum-ℕ : pair-with-sum-ℕ n → pair-with-sum-ℕ n → UU lzero
  Eq-pair-with-sum-ℕ (a , b , _) (a' , b' , _) = a ＝ a'

  is-prop-Eq-pair-with-sum-ℕ :
    (x y : pair-with-sum-ℕ n) → is-prop (Eq-pair-with-sum-ℕ x y)
  is-prop-Eq-pair-with-sum-ℕ (a , _) (a' , _) =
    is-prop-type-Prop (Id-Prop ℕ-Set a a')

  refl-Eq-pair-with-sum-ℕ : (x : pair-with-sum-ℕ n) → Eq-pair-with-sum-ℕ x x
  refl-Eq-pair-with-sum-ℕ _ = refl

  eq-Eq-pair-with-sum-ℕ :
    (x y : pair-with-sum-ℕ n) → Eq-pair-with-sum-ℕ x y → x ＝ y
  eq-Eq-pair-with-sum-ℕ (a , b , b+a=n) (.a , b' , b'+a=n) refl =
    eq-pair-eq-fiber
      ( eq-pair-Σ
        ( is-injective-right-add-ℕ a (b+a=n ∙ inv b'+a=n))
        ( eq-type-Prop (Id-Prop ℕ-Set _ _)))

  abstract
    is-set-pair-with-sum-ℕ : is-set (pair-with-sum-ℕ n)
    is-set-pair-with-sum-ℕ =
      is-set-prop-in-id
        Eq-pair-with-sum-ℕ
        is-prop-Eq-pair-with-sum-ℕ
        refl-Eq-pair-with-sum-ℕ
        eq-Eq-pair-with-sum-ℕ

  set-pair-with-sum-ℕ : Set lzero
  set-pair-with-sum-ℕ = pair-with-sum-ℕ n , is-set-pair-with-sum-ℕ
```

### Equivalence of dependent pairs further partitioning a component

```agda
module _
  (n : ℕ)
  where

  map-equiv-pair-with-sum-pr1-pr2 :
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1) →
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1 ∘ pr2)
  pr1 (map-equiv-pair-with-sum-pr1-pr2 ((p , c , c+p=n) , _)) =
    (c , p , commutative-add-ℕ p c ∙ c+p=n)
  pr2 (map-equiv-pair-with-sum-pr1-pr2 (_ , y)) = y

  map-inv-equiv-pair-with-sum-pr1-pr2 :
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1 ∘ pr2) →
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1)
  pr1 (map-inv-equiv-pair-with-sum-pr1-pr2 ((c , p , p+c=n) , _)) =
    (p , c , commutative-add-ℕ c p ∙ p+c=n)
  pr2 (map-inv-equiv-pair-with-sum-pr1-pr2 (_ , y)) = y

  abstract
    is-section-map-inv-equiv-pair-with-sum-pr1-pr2 :
      is-section
        map-equiv-pair-with-sum-pr1-pr2
        map-inv-equiv-pair-with-sum-pr1-pr2
    is-section-map-inv-equiv-pair-with-sum-pr1-pr2
      x@((c , p , p+c=n) , a , b , b+a=p) =
        inv
          ( ind-Id
            ( p+c=n)
            ( λ H' H=H' → x ＝ ((c , p , H') , a , b , b+a=p))
            ( refl)
            ( _)
            ( eq-type-Prop (Id-Prop ℕ-Set _ _)))

    is-retraction-map-inv-equiv-pair-with-sum-pr1-pr2 :
      is-retraction
        map-equiv-pair-with-sum-pr1-pr2
        map-inv-equiv-pair-with-sum-pr1-pr2
    is-retraction-map-inv-equiv-pair-with-sum-pr1-pr2
      x@((p , c , c+p=n) , a , b , b+a=p) =
        inv
          ( ind-Id
            ( c+p=n)
            ( λ H' H=H' → x ＝ ((p , c , H') , a , b , b+a=p))
            ( refl)
            ( _)
            ( eq-type-Prop (Id-Prop ℕ-Set _ _)))

  equiv-pair-with-sum-pr1-pr2 :
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1) ≃
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1 ∘ pr2)
  equiv-pair-with-sum-pr1-pr2 =
    map-equiv-pair-with-sum-pr1-pr2 ,
    ( map-inv-equiv-pair-with-sum-pr1-pr2 ,
      is-section-map-inv-equiv-pair-with-sum-pr1-pr2) ,
    ( map-inv-equiv-pair-with-sum-pr1-pr2 ,
      is-retraction-map-inv-equiv-pair-with-sum-pr1-pr2)
```

### Pairs with a fixed sum are a finite type

```agda
module _
  (n : ℕ)
  where

  abstract
    equiv-pair-with-sum-leq-ℕ :
      Σ ℕ (λ k → leq-ℕ k n) ≃ pair-with-sum-ℕ n
    equiv-pair-with-sum-leq-ℕ =
      ( λ (k , k≤n) → k , subtraction-leq-ℕ k n k≤n) ,
      ((λ (k , l , l+k=n) → k , leq-subtraction-ℕ k n l l+k=n) ,
        λ (k , l , l+k=n) →
          let
            (l' , l'+k=n) =
              subtraction-leq-ℕ k n (leq-subtraction-ℕ k n l l+k=n)
          in
            eq-pair-eq-fiber
              ( eq-pair-Σ
                ( is-injective-right-add-ℕ k (l'+k=n ∙ inv l+k=n))
                ( eq-type-Prop (Id-Prop ℕ-Set (l +ℕ k) n)))) ,
      (( λ (k , l , l+k=n) → k , leq-subtraction-ℕ k n l l+k=n) ,
        (λ (k , k≤n) → eq-pair-eq-fiber (eq-type-Prop (leq-ℕ-Prop k n))))

    count-pair-with-sum-ℕ : count (pair-with-sum-ℕ n)
    count-pair-with-sum-ℕ =
      succ-ℕ n , equiv-pair-with-sum-leq-ℕ ∘e equiv-fin-succ-leq-ℕ n

  finite-type-pair-with-sum-ℕ : Finite-Type lzero
  finite-type-pair-with-sum-ℕ =
    pair-with-sum-ℕ n ,
    is-finite-count count-pair-with-sum-ℕ
```

### Permuting components in a triple of sums

```agda
module _
  (n : ℕ)
  where

  map-equiv-permute-components-triple-with-sum-pr2 :
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1 ∘ pr2) →
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1 ∘ pr2)
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
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1 ∘ pr2) →
    Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1 ∘ pr2)
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
      x@((c , .(b +ℕ a), p+c=n) , a , b , refl) =
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
      x@((c , .(b +ℕ a), p+c=n) , a , b , refl) =
        inv
          ( ind-Id
            ( p+c=n)
            ( λ H' H=H' → x ＝ ((c , b +ℕ a , H') , a , b , refl))
            ( refl)
            ( _)
            ( eq-type-Prop (Id-Prop ℕ-Set _ _)))

  equiv-permute-components-triple-with-sum-pr2 :
    Aut (Σ (pair-with-sum-ℕ n) (pair-with-sum-ℕ ∘ pr1 ∘ pr2))
  equiv-permute-components-triple-with-sum-pr2 =
    map-equiv-permute-components-triple-with-sum-pr2 ,
    ( ( map-inv-equiv-permute-components-triple-with-sum-pr2 ,
        is-section-map-inv-equiv-permute-components-triple-with-sum-pr2) ,
      ( map-inv-equiv-permute-components-triple-with-sum-pr2 ,
        is-retraction-map-inv-equiv-permute-components-triple-with-sum-pr2))
```

### Breaking out the zero case

```agda
module _
  (n : ℕ)
  where

  decidable-subtype-zero-pair-with-sum-ℕ :
    decidable-subtype lzero (pair-with-sum-ℕ n)
  decidable-subtype-zero-pair-with-sum-ℕ (a , _ , _) =
    is-zero-ℕ a , is-prop-is-zero-ℕ a , is-decidable-is-zero-ℕ a

  is-contr-decidable-subtype-zero-pair-with-sum-ℕ :
    is-contr (type-decidable-subtype decidable-subtype-zero-pair-with-sum-ℕ)
  is-contr-decidable-subtype-zero-pair-with-sum-ℕ =
    ((zero-ℕ , n , right-unit-law-add-ℕ n) , refl) ,
    λ ((x , y , y+x=n) , x=0) →
      eq-type-subtype
        ( subtype-decidable-subtype decidable-subtype-zero-pair-with-sum-ℕ)
        ( eq-Eq-pair-with-sum-ℕ n _ _ (inv x=0))

  equiv-pair-with-sum-coproduct-zero-nonzero :
    pair-with-sum-ℕ n ≃
      unit +
      type-decidable-subtype
        ( complement-decidable-subtype (decidable-subtype-zero-pair-with-sum-ℕ))
  equiv-pair-with-sum-coproduct-zero-nonzero =
    equiv-coproduct
      ( equiv-unit-is-contr is-contr-decidable-subtype-zero-pair-with-sum-ℕ)
      ( id-equiv) ∘e
    equiv-coproduct-decidable-subtype-complement
      ( decidable-subtype-zero-pair-with-sum-ℕ)
```
