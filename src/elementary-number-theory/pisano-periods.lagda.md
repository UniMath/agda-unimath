# Pisano periods

```agda
module elementary-number-theory.pisano-periods where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.fibonacci-sequence
open import elementary-number-theory.modular-arithmetic-standard-finite-types
open import elementary-number-theory.natural-numbers

open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

The sequence `P : ℕ → ℕ` of **Pisano periods** is the sequence where `P n` is the period of the Fibonacci sequence modulo `n`. This sequence is listed as [A001175](https://oeis.org/A001175) in the OEIS.

## Definitions

```agda
generating-map-fibonacci-pair-Fin :
  (k : ℕ) → Fin (succ-ℕ k) × Fin (succ-ℕ k) → Fin (succ-ℕ k) × Fin (succ-ℕ k)
generating-map-fibonacci-pair-Fin k p =
  pair (pr2 p) (add-Fin (pr2 p) (pr1 p))

inv-generating-map-fibonacci-pair-Fin :
  (k : ℕ) → Fin (succ-ℕ k) × Fin (succ-ℕ k) → Fin (succ-ℕ k) × Fin (succ-ℕ k)
inv-generating-map-fibonacci-pair-Fin k (pair x y) =
  pair (add-Fin y (neg-Fin x)) x

issec-inv-generating-map-fibonacci-pair-Fin :
  (k : ℕ) (p : Fin (succ-ℕ k) × Fin (succ-ℕ k)) →
  Id ( generating-map-fibonacci-pair-Fin k
       ( inv-generating-map-fibonacci-pair-Fin k p))
     ( p)
issec-inv-generating-map-fibonacci-pair-Fin k (pair x y) =
  ap-binary pair refl
    ( ( commutative-add-Fin x (add-Fin y (neg-Fin x))) ∙
      ( ( associative-add-Fin y (neg-Fin x) x) ∙
        ( ( ap (add-Fin y) (left-inverse-law-add-Fin x)) ∙
          ( right-unit-law-add-Fin y))))

isretr-inv-generating-map-fibonacci-pair-Fin :
  (k : ℕ ) (p : Fin (succ-ℕ k) × Fin (succ-ℕ k)) →
  Id ( inv-generating-map-fibonacci-pair-Fin k
       ( generating-map-fibonacci-pair-Fin k p))
     ( p)
isretr-inv-generating-map-fibonacci-pair-Fin k (pair x y) =
  ap-binary pair
    ( commutative-add-Fin (add-Fin y x) (neg-Fin y) ∙
      ( ( inv (associative-add-Fin (neg-Fin y) y x)) ∙
        ( ( ap (λ t → add-Fin t x) (left-inverse-law-add-Fin y)) ∙
          ( left-unit-law-add-Fin x))))
    ( refl)

is-equiv-generating-map-fibonacci-pair-Fin :
  (k : ℕ) → is-equiv (generating-map-fibonacci-pair-Fin k)
is-equiv-generating-map-fibonacci-pair-Fin k =
  is-equiv-has-inverse
    ( inv-generating-map-fibonacci-pair-Fin k)
    ( issec-inv-generating-map-fibonacci-pair-Fin k)
    ( isretr-inv-generating-map-fibonacci-pair-Fin k)

fibonacci-pair-Fin :
  (k : ℕ) → ℕ → Fin (succ-ℕ k) × Fin (succ-ℕ k)
fibonacci-pair-Fin k zero-ℕ = pair zero-Fin one-Fin
fibonacci-pair-Fin k (succ-ℕ n) =
  generating-map-fibonacci-pair-Fin k (fibonacci-pair-Fin k n)

compute-fibonacci-pair-Fin :
  (k : ℕ) (n : ℕ) →
  Id ( fibonacci-pair-Fin k n)
     ( pair ( mod-succ-ℕ k (Fibonacci-ℕ n))
            ( mod-succ-ℕ k (Fibonacci-ℕ (succ-ℕ n))))
compute-fibonacci-pair-Fin k zero-ℕ = refl
compute-fibonacci-pair-Fin k (succ-ℕ zero-ℕ) =
  ap-binary pair refl (right-unit-law-add-Fin one-Fin)
compute-fibonacci-pair-Fin k (succ-ℕ (succ-ℕ n)) =
  ap-binary pair
    ( ap pr2 (compute-fibonacci-pair-Fin k (succ-ℕ n)))
    ( ( ap-binary add-Fin
        ( ap pr2 (compute-fibonacci-pair-Fin k (succ-ℕ n)))
        ( ap pr1 (compute-fibonacci-pair-Fin k (succ-ℕ n)))) ∙
      ( inv
        ( mod-succ-add-ℕ k
          ( Fibonacci-ℕ (succ-ℕ (succ-ℕ n)))
          ( Fibonacci-ℕ (succ-ℕ n)))))

has-ordered-repetition-fibonacci-pair-Fin :
  (k : ℕ) → has-ordered-repetition-ℕ (fibonacci-pair-Fin k)
has-ordered-repetition-fibonacci-pair-Fin k =
  has-ordered-repetition-nat-to-count
    ( count-prod (count-Fin (succ-ℕ k)) (count-Fin (succ-ℕ k)))
    ( fibonacci-pair-Fin k)

minimal-ordered-repetition-fibonacci-pair-Fin :
  (k : ℕ) →
  minimal-element-ℕ (is-ordered-repetition-ℕ (fibonacci-pair-Fin k))
minimal-ordered-repetition-fibonacci-pair-Fin k =
  well-ordering-principle-ℕ
    ( is-ordered-repetition-ℕ (fibonacci-pair-Fin k))
    ( is-decidable-is-ordered-repetition-ℕ-count
        ( count-prod (count-Fin (succ-ℕ k)) (count-Fin (succ-ℕ k)))
        ( fibonacci-pair-Fin k))
    ( has-ordered-repetition-fibonacci-pair-Fin k)

pisano-period : ℕ → ℕ
pisano-period k = pr1 (minimal-ordered-repetition-fibonacci-pair-Fin k)

is-ordered-repetition-pisano-period :
  (k : ℕ) →
  is-ordered-repetition-ℕ (fibonacci-pair-Fin k) (pisano-period k)
is-ordered-repetition-pisano-period k =
  pr1 (pr2 (minimal-ordered-repetition-fibonacci-pair-Fin k))

is-lower-bound-pisano-period :
  (k : ℕ) →
  is-lower-bound-ℕ
    ( is-ordered-repetition-ℕ (fibonacci-pair-Fin k))
    ( pisano-period k)
is-lower-bound-pisano-period k =
  pr2 (pr2 (minimal-ordered-repetition-fibonacci-pair-Fin k))

cases-is-repetition-of-zero-pisano-period :
  (k x y : ℕ) → Id (pr1 (is-ordered-repetition-pisano-period k)) x →
  Id (pisano-period k) y → is-zero-ℕ x
cases-is-repetition-of-zero-pisano-period k zero-ℕ y p q = refl
cases-is-repetition-of-zero-pisano-period k (succ-ℕ x) zero-ℕ p q =
   ex-falso
     ( concatenate-eq-le-eq-ℕ
       ( inv p)
       ( pr1 (pr2 (is-ordered-repetition-pisano-period k)))
       ( q))
cases-is-repetition-of-zero-pisano-period k (succ-ℕ x) (succ-ℕ y) p q =
  ex-falso
    ( contradiction-leq-ℕ y y (refl-leq-ℕ y)
      ( concatenate-eq-leq-ℕ y (inv q) (is-lower-bound-pisano-period k y R)))
  where
  R : is-ordered-repetition-ℕ (fibonacci-pair-Fin k) y
  R = triple x
        ( concatenate-eq-le-eq-ℕ
          ( inv p)
          ( pr1 (pr2 (is-ordered-repetition-pisano-period k)))
          ( q))
        ( is-injective-is-equiv
          ( is-equiv-generating-map-fibonacci-pair-Fin k)
          ( ( ap (fibonacci-pair-Fin k) (inv p)) ∙
            ( ( pr2 (pr2 (is-ordered-repetition-pisano-period k))) ∙
              ( ap (fibonacci-pair-Fin k) q))))

is-repetition-of-zero-pisano-period :
  (k : ℕ) → is-zero-ℕ (pr1 (is-ordered-repetition-pisano-period k))
is-repetition-of-zero-pisano-period k =
  cases-is-repetition-of-zero-pisano-period k
    ( pr1 (is-ordered-repetition-pisano-period k))
    ( pisano-period k)
    ( refl)
    ( refl)

compute-fibonacci-pair-Fin-pisano-period :
  (k : ℕ) →
  Id (fibonacci-pair-Fin k (pisano-period k)) (fibonacci-pair-Fin k zero-ℕ)
compute-fibonacci-pair-Fin-pisano-period k =
  ( inv (pr2 (pr2 (is-ordered-repetition-pisano-period k)))) ∙
  ( ap (fibonacci-pair-Fin k) (is-repetition-of-zero-pisano-period k)) 

le-zero-pisano-period :
  (k : ℕ) → le-ℕ zero-ℕ (pisano-period k)
le-zero-pisano-period k =
  concatenate-eq-le-ℕ
    { x = zero-ℕ}
    { y = pr1 (is-ordered-repetition-pisano-period k)}
    { z = pisano-period k}
    ( inv (is-repetition-of-zero-pisano-period k))
    ( pr1 (pr2 (is-ordered-repetition-pisano-period k)))

is-nonzero-pisano-period :
  (k : ℕ) → is-nonzero-ℕ (pisano-period k)
is-nonzero-pisano-period k p =
  ex-falso (concatenate-le-eq-ℕ (le-zero-pisano-period k) p)

div-fibonacci-pisano-period :
  (k : ℕ) → div-ℕ (succ-ℕ k) (Fibonacci-ℕ (pisano-period k))
div-fibonacci-pisano-period k =
  div-ℕ-is-zero-Fin k
    ( Fibonacci-ℕ (pisano-period k))
    ( ( ap pr1 (inv (compute-fibonacci-pair-Fin k (pisano-period k)))) ∙
      ( inv
        ( ap pr1
          { x = fibonacci-pair-Fin k zero-ℕ}
          { y = fibonacci-pair-Fin k (pisano-period k)}
          ( ( ap ( fibonacci-pair-Fin k)
                 ( inv (is-repetition-of-zero-pisano-period k))) ∙
            ( pr2 (pr2 (is-ordered-repetition-pisano-period k)))))))
```
