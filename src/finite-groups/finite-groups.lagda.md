# Finite groups

```agda
{-# OPTIONS --without-K --exact-split #-}

module finite-groups.finite-groups where

open import elementary-number-theory.natural-numbers using (ℕ)

open import foundation.dependent-pair-types using (Σ; pair; pr1; pr2)
open import foundation.universe-levels using (Level; UU; lsuc)

open import groups.abstract-groups using (Group)
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
