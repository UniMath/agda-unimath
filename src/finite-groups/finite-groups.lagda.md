# Finite groups

```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-groups.finite-groups where

open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation
open import elementary-number-theory
open import univalent-combinatorics

open import groups
```

```agda
-- We show that there are finitely many semi-groups of order n

Semigroup-of-Order' : (l : Level) (n : ℕ) → UU (lsuc l)
Semigroup-of-Order' l n =
  Σ ( UU-Fin-Level l n)
    ( λ X → has-associative-mul (type-UU-Fin-Level X))

Semigroup-of-Order : (l : Level) (n : ℕ) → UU (lsuc l)
Semigroup-of-Order l n =
  Σ (Semigroup l) (λ G → mere-equiv (Fin n) (type-Semigroup G))

is-finite-has-associative-mul :
  {l : Level} {X : UU l} → is-finite X → is-finite (has-associative-mul X)
is-finite-has-associative-mul H =
  is-finite-Σ
    ( is-finite-function-type H (is-finite-function-type H H))
    ( λ μ →
      is-finite-Π H
        ( λ x →
          is-finite-Π H
            ( λ y →
              is-finite-Π H
                ( λ z →
                  is-finite-eq (has-decidable-equality-is-finite H)))))

is-π-finite-Semigroup-of-Order' :
  {l : Level} (k n : ℕ) → is-π-finite k (Semigroup-of-Order' l n)
is-π-finite-Semigroup-of-Order' k n =
  is-π-finite-Σ k
    ( is-π-finite-UU-Fin-Level (succ-ℕ k) n)
    ( λ x →
      is-π-finite-is-finite k
        ( is-finite-has-associative-mul
          ( is-finite-type-UU-Fin-Level x)))

is-π-finite-Semigroup-of-Order :
  {l : Level} (k n : ℕ) → is-π-finite k (Semigroup-of-Order l n)
is-π-finite-Semigroup-of-Order {l} k n =
  is-π-finite-equiv k e
    ( is-π-finite-Semigroup-of-Order' k n)
  where
  e : Semigroup-of-Order l n ≃ Semigroup-of-Order' l n
  e = ( equiv-Σ
        ( has-associative-mul ∘ type-UU-Fin-Level)
        ( ( right-unit-law-Σ-is-contr
            ( λ X →
              is-proof-irrelevant-is-prop
                ( is-prop-is-set _)
                ( is-set-is-finite
                  ( is-finite-has-cardinality (pr2 X))))) ∘e
          ( equiv-right-swap-Σ))
        ( λ X → id-equiv)) ∘e
      ( equiv-right-swap-Σ
        { A = UU-Set l}
        { B = has-associative-mul-Set}
        { C = mere-equiv (Fin n) ∘ type-Set})

number-of-semi-groups-of-order : ℕ → ℕ
number-of-semi-groups-of-order n =
  number-of-connected-components
    ( is-π-finite-Semigroup-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-semi-groups-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-semi-groups-of-order n))
    ( type-trunc-Set (Semigroup-of-Order lzero n))
mere-equiv-number-of-semi-groups-of-order n =
  mere-equiv-number-of-connected-components
    ( is-π-finite-Semigroup-of-Order {lzero} zero-ℕ n)

-- We show that there are finitely many monoids of order n

Monoid-of-Order : (l : Level) (n : ℕ) → UU (lsuc l)
Monoid-of-Order l n = Σ (Monoid l) (λ M → mere-equiv (Fin n) (type-Monoid M))

is-finite-is-unital :
  {l : Level} {n : ℕ} (X : Semigroup-of-Order l n) →
  is-finite (is-unital (pr1 X))
is-finite-is-unital {l} {n} X =
  apply-universal-property-trunc-Prop
    ( pr2 X)
    ( is-finite-Prop _)
    ( λ e →
      is-finite-is-decidable-Prop
        ( is-unital-Prop (pr1 X))
        ( is-decidable-Σ-count
          ( pair n e)
          ( λ u →
            is-decidable-prod
              ( is-decidable-Π-count
                ( pair n e)
                ( λ x →
                  has-decidable-equality-count
                    ( pair n e)
                    ( mul-Semigroup (pr1 X) u x)
                    ( x)))
              ( is-decidable-Π-count
                ( pair n e)
                ( λ x →
                  has-decidable-equality-count
                    ( pair n e)
                    ( mul-Semigroup (pr1 X) x u)
                    ( x))))))

is-π-finite-Monoid-of-Order :
  {l : Level} (k n : ℕ) → is-π-finite k (Monoid-of-Order l n)
is-π-finite-Monoid-of-Order {l} k n =
  is-π-finite-equiv k e
    ( is-π-finite-Σ k
      ( is-π-finite-Semigroup-of-Order (succ-ℕ k) n)
      ( λ X →
        is-π-finite-is-finite k
          ( is-finite-is-unital X)))
  where
  e : Monoid-of-Order l n ≃
      Σ (Semigroup-of-Order l n) (λ X → is-unital (pr1 X))
  e = equiv-right-swap-Σ

number-of-monoids-of-order : ℕ → ℕ
number-of-monoids-of-order n =
  number-of-connected-components
    ( is-π-finite-Monoid-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-monoids-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-monoids-of-order n))
    ( type-trunc-Set (Monoid-of-Order lzero n))
mere-equiv-number-of-monoids-of-order n =
  mere-equiv-number-of-connected-components
    ( is-π-finite-Monoid-of-Order {lzero} zero-ℕ n)
```


```agda
Group-of-Order : (l : Level) (n : ℕ) → UU (lsuc l)
Group-of-Order l n = Σ (Group l) (λ G → mere-equiv (Fin n) (type-Group G))

is-finite-is-group :
  {l : Level} {n : ℕ} (G : Semigroup-of-Order l n) →
  is-finite {l} (is-group (pr1 G))
is-finite-is-group {l} {n} G =
  apply-universal-property-trunc-Prop
    ( pr2 G)
    ( is-finite-Prop _)
    ( λ e →
      is-finite-is-decidable-Prop
        ( is-group-Prop (pr1 G))
        ( is-decidable-Σ-count
          ( count-Σ
            ( pair n e)
            ( λ u →
              count-prod
                ( count-Π
                  ( pair n e)
                  ( λ x →
                    count-eq
                      ( has-decidable-equality-count (pair n e))
                      ( mul-Semigroup (pr1 G) u x)
                      ( x)))
                ( count-Π
                  ( pair n e)
                  ( λ x →
                    count-eq
                      ( has-decidable-equality-count (pair n e))
                      ( mul-Semigroup (pr1 G) x u)
                      ( x)))))
          ( λ u →
            is-decidable-Σ-count
              ( count-function-type (pair n e) (pair n e))
              ( λ i →
                is-decidable-prod
                  ( is-decidable-Π-count
                    ( pair n e)
                    ( λ x →
                      has-decidable-equality-count
                        ( pair n e)
                        ( mul-Semigroup (pr1 G) (i x) x)
                        ( pr1 u)))
                  ( is-decidable-Π-count
                    ( pair n e)
                    ( λ x →
                      has-decidable-equality-count
                        ( pair n e)
                        ( mul-Semigroup (pr1 G) x (i x))
                        ( pr1 u)))))))

is-π-finite-Group-of-Order :
  {l : Level} (k n : ℕ) → is-π-finite k (Group-of-Order l n)
is-π-finite-Group-of-Order {l} k n =
  is-π-finite-equiv k e
    ( is-π-finite-Σ k
      ( is-π-finite-Semigroup-of-Order (succ-ℕ k) n)
      ( λ X →
        is-π-finite-is-finite k
          ( is-finite-is-group X)))
  where
  e : Group-of-Order l n ≃
      Σ (Semigroup-of-Order l n) (λ X → is-group (pr1 X))
  e = equiv-right-swap-Σ

number-of-groups-of-order : ℕ → ℕ
number-of-groups-of-order n =
  number-of-connected-components
    ( is-π-finite-Group-of-Order {lzero} zero-ℕ n)

mere-equiv-number-of-groups-of-order :
  (n : ℕ) →
  mere-equiv
    ( Fin (number-of-groups-of-order n))
    ( type-trunc-Set (Group-of-Order lzero n))
mere-equiv-number-of-groups-of-order n =
  mere-equiv-number-of-connected-components
    ( is-π-finite-Group-of-Order {lzero} zero-ℕ n)
```
