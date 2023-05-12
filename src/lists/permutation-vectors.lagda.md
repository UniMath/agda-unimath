# Permutations of vectors

```agda
module lists.permutation-vectors where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types
open import finite-group-theory.transpositions-standard-finite-types

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.identity-types
open import foundation.universe-levels
open import foundation.contractible-types
open import foundation.unit-type
open import foundation.coproduct-types

open import linear-algebra.vectors

open import lists.arrays

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given an functional vector `t` of length `n` and a automorphism `σ` of `Fin n`,
the permutation of `t` according to `σ` is the functional vector where the index
are permuted by `σ`. Then, we can define what is a permutation of a vector of
length `n` via the equivalence between functional vectors and vectors.

## Definitions

```agda
module _
  {l : Level} {A : UU l}
  where

  permute-vec : (n : ℕ) → vec A n → Permutation n → vec A n
  permute-vec n v s =
    listed-vec-functional-vec n (functional-vec-vec n v ∘ (map-equiv s))
```

### The predicate that a function from `vec` to `vec` is just permuting vectors.

```agda
  is-permutation-vec : (n : ℕ) → (vec A n → vec A n) → UU l
  is-permutation-vec n f =
    (v : vec A n) →
    Σ ( Permutation n)
      ( λ t → f v ＝ permute-vec n v t)

  permutation-is-permutation-vec :
    (n : ℕ )(f : vec A n → vec A n) → is-permutation-vec n f →
    (v : vec A n) → Permutation n
  permutation-is-permutation-vec n f P v = pr1 (P v)

  eq-permute-vec-permutation-is-permutation-vec :
    (n : ℕ) (f : vec A n → vec A n) → (P : is-permutation-vec n f) →
    (v : vec A n) →
    (f v ＝ permute-vec n v (permutation-is-permutation-vec n f P v))
  eq-permute-vec-permutation-is-permutation-vec n f P v = pr2 (P v)
```

## Properties

### Computational rules

```agda
  compute-permute-vec-id-equiv :
    (n : ℕ)
    (v : vec A n) →
    permute-vec n v id-equiv ＝ v
  compute-permute-vec-id-equiv n v =
    ap (λ f → map-equiv f v) (right-inverse-law-equiv (compute-vec n))

  compute-composition-permute-vec :
    (n : ℕ)
    (v : vec A n) →
    (a b : Permutation n) →
    permute-vec n v (a ∘e b) ＝ permute-vec n (permute-vec n v a) b
  compute-composition-permute-vec n v a b =
    ap
      ( λ f → listed-vec-functional-vec n (f ∘ (map-equiv b)))
      ( inv
        ( isretr-functional-vec-vec n (functional-vec-vec n v ∘ map-equiv a)))

  compute-swap-two-last-elements-transposition-Fin-permute-vec :
    (n : ℕ)
    (v : vec A n) →
    (x y : A) →
    permute-vec
      (succ-ℕ (succ-ℕ n))
      (x ∷ y ∷ v)
      (swap-two-last-elements-transposition-Fin n) ＝
    (y ∷ x ∷ v)
  compute-swap-two-last-elements-transposition-Fin-permute-vec n v x y =
    eq-Eq-vec
      ( succ-ℕ (succ-ℕ n))
      ( permute-vec
          ( succ-ℕ (succ-ℕ n))
          ( x ∷ y ∷ v)
          ( swap-two-last-elements-transposition-Fin n))
      ( y ∷ x ∷ v)
      ( refl ,
        refl ,
        Eq-eq-vec
          ( n)
          ( permute-vec n v id-equiv)
          ( v)
          ( compute-permute-vec-id-equiv n v))

  ap-permute-vec :
    {n : ℕ}
    (a : Permutation n)
    {v w : vec A n} →
    v ＝ w →
    permute-vec n v a ＝ permute-vec n w a
  ap-permute-vec a refl = refl
```

### `x` is in a vector `v` iff it is in `permute v t`

```agda
  is-in-functional-vec-is-in-permute-functional-vec :
    (n : ℕ) (v : Fin n → A) (t : Permutation n) (x : A) →
    in-functional-vec n x (v ∘ map-equiv t) → in-functional-vec n x v
  is-in-functional-vec-is-in-permute-functional-vec n v t x (k , refl) =
    map-equiv t k , refl

  is-in-vec-is-in-permute-vec :
    (n : ℕ) (v : vec A n) (t : Permutation n) (x : A) →
    x ∈-vec (permute-vec n v t) → x ∈-vec v
  is-in-vec-is-in-permute-vec n v t x I =
    is-in-vec-is-in-functional-vec
      ( n)
      ( v)
      ( x)
      ( is-in-functional-vec-is-in-permute-functional-vec
        ( n)
        ( functional-vec-vec n v)
        ( t)
        ( x)
        ( tr
          ( λ p → in-functional-vec n x p)
          ( isretr-functional-vec-vec n (functional-vec-vec n v ∘ map-equiv t))
          ( is-in-functional-vec-is-in-vec n (permute-vec n v t) x I)))

  is-in-permute-functional-vec-is-in-functional-vec :
    (n : ℕ) (v : Fin n → A) (t : Permutation n) (x : A) →
    in-functional-vec n x v → in-functional-vec n x (v ∘ map-equiv t)
  is-in-permute-functional-vec-is-in-functional-vec n v t x (k , refl) =
    map-inv-equiv t k , ap v (inv (issec-map-inv-equiv t k))

  is-in-permute-vec-is-in-vec :
    (n : ℕ) (v : vec A n) (t : Permutation n) (x : A) →
    x ∈-vec v → x ∈-vec (permute-vec n v t)
  is-in-permute-vec-is-in-vec n v t x I =
    is-in-vec-is-in-functional-vec
      ( n)
      ( permute-vec n v t)
      ( x)
      ( tr
        ( λ p → in-functional-vec n x p)
        ( inv
          ( isretr-functional-vec-vec n (functional-vec-vec n v ∘ map-equiv t)))
        ( is-in-permute-functional-vec-is-in-functional-vec
          ( n)
          ( functional-vec-vec n v)
          ( t)
          ( x)
          ( is-in-functional-vec-is-in-vec n v x I)))
```

### If `(μ : A → (B → B))` satisfies a property of commutativity, then for `b : B` the function `fold-vec b μ` is invariant by permutation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (b : B) (μ : A → (B → B))
  where

  commutative-fold-vec : UU (l1 ⊔ l2)
  commutative-fold-vec = (a1 a2 : A) (b : B) → μ a1 (μ a2 b) ＝ μ a2 (μ a1 b)

  invariant-permutation-fold-vec :
    {n : ℕ} → (v : vec A n) → (t : Permutation n) →
    fold-vec b μ v ＝ fold-vec b μ (permute-vec n v t)
  invariant-permutation-fold-vec {0} v t = refl
  invariant-permutation-fold-vec {1} (x ∷ empty-vec) t =
    ap
      ( λ p → μ p b)
      ( ap (λ k → (cons-functional-vec 0 x empty-functional-vec) k)
      ( eq-is-contr' is-contr-Fin-one-ℕ (inr star) (pr1 t (inr star))))
  invariant-permutation-fold-vec {succ-ℕ (succ-ℕ n)} v t = {!!}
```
