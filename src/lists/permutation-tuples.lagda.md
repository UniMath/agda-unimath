# Permutations of tuples

```agda
module lists.permutation-tuples where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types
open import finite-group-theory.transpositions-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.negated-equality
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.arrays
open import lists.equivalence-tuples-finite-sequences
open import lists.finite-sequences
open import lists.functoriality-finite-sequences
open import lists.functoriality-tuples
open import lists.functoriality-tuples-finite-sequences
open import lists.lists
open import lists.tuples

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Given a [tuple](lists.tuples.md) `t` of length `n` and an
[automorphism](finite-group-theory.permutations-standard-finite-types.md) `σ` of
`Fin n`, the
{{#concept "permutation" Disambiguation="of a tuple" WD="permutation" WDID=Q161519 Agda=permute-tuple}}
of `t` according to `σ` is the tuple where the positions of elements are
permuted according to `σ`.

## Definitions

```agda
module _
  {l : Level} {A : UU l}
  where

  permute-tuple : (n : ℕ) → tuple A n → Permutation n → tuple A n
  permute-tuple n v s =
    tuple-fin-sequence n (fin-sequence-tuple n v ∘ map-equiv s)
```

### The predicate that a function from `tuple` to `tuple` is just permuting tuples

```agda
  is-permutation-tuple : (n : ℕ) → (tuple A n → tuple A n) → UU l
  is-permutation-tuple n f =
    (v : tuple A n) →
    Σ ( Permutation n)
      ( λ t → f v ＝ permute-tuple n v t)

  permutation-is-permutation-tuple :
    (n : ℕ) (f : tuple A n → tuple A n) → is-permutation-tuple n f →
    (v : tuple A n) → Permutation n
  permutation-is-permutation-tuple n f P v = pr1 (P v)

  eq-permute-tuple-permutation-is-permutation-tuple :
    (n : ℕ) (f : tuple A n → tuple A n) → (P : is-permutation-tuple n f) →
    (v : tuple A n) →
    (f v ＝ permute-tuple n v (permutation-is-permutation-tuple n f P v))
  eq-permute-tuple-permutation-is-permutation-tuple n f P v = pr2 (P v)
```

## Properties

### Computational rules

```agda
  compute-permute-tuple-id-equiv :
    (n : ℕ)
    (v : tuple A n) →
    permute-tuple n v id-equiv ＝ v
  compute-permute-tuple-id-equiv n v =
    ap (λ f → map-equiv f v) (right-inverse-law-equiv (compute-tuple n))

  compute-composition-permute-tuple :
    (n : ℕ)
    (v : tuple A n) →
    (a b : Permutation n) →
    permute-tuple n v (a ∘e b) ＝ permute-tuple n (permute-tuple n v a) b
  compute-composition-permute-tuple n v a b =
    ap
      ( λ f → tuple-fin-sequence n (f ∘ (map-equiv b)))
      ( inv
        ( is-retraction-fin-sequence-tuple n
          ( fin-sequence-tuple n v ∘ map-equiv a)))

  compute-swap-two-last-elements-transposition-Fin-permute-tuple :
    (n : ℕ)
    (v : tuple A n) →
    (x y : A) →
    permute-tuple
      (succ-ℕ (succ-ℕ n))
      (x ∷ y ∷ v)
      (swap-two-last-elements-transposition-Fin n) ＝
    (y ∷ x ∷ v)
  compute-swap-two-last-elements-transposition-Fin-permute-tuple n v x y =
    eq-Eq-tuple
      ( succ-ℕ (succ-ℕ n))
      ( permute-tuple
          ( succ-ℕ (succ-ℕ n))
          ( x ∷ y ∷ v)
          ( swap-two-last-elements-transposition-Fin n))
      ( y ∷ x ∷ v)
      ( refl ,
        refl ,
        Eq-eq-tuple
          ( n)
          ( permute-tuple n v id-equiv)
          ( v)
          ( compute-permute-tuple-id-equiv n v))

  compute-equiv-coproduct-permutation-id-equiv-permute-tuple :
    (n : ℕ)
    (v : tuple A n)
    (x : A)
    (t : Permutation n) →
    permute-tuple (succ-ℕ n) (x ∷ v) (equiv-coproduct t id-equiv) ＝
    (x ∷ permute-tuple n v t)
  compute-equiv-coproduct-permutation-id-equiv-permute-tuple n v x t =
    eq-Eq-tuple
      ( succ-ℕ n)
      ( permute-tuple (succ-ℕ n) (x ∷ v) (equiv-coproduct t id-equiv))
      ( x ∷ permute-tuple n v t)
      ( refl ,
        ( Eq-eq-tuple
          ( n)
          ( _)
          ( permute-tuple n v t)
          ( refl)))

  ap-permute-tuple :
    {n : ℕ}
    (a : Permutation n)
    {v w : tuple A n} →
    v ＝ w →
    permute-tuple n v a ＝ permute-tuple n w a
  ap-permute-tuple a refl = refl
```

### `x` is in a tuple `v` iff it is in `permute v t`

```agda
  is-in-fin-sequence-is-in-permute-fin-sequence :
    (n : ℕ) (v : Fin n → A) (t : Permutation n) (x : A) →
    in-fin-sequence n x (v ∘ map-equiv t) → in-fin-sequence n x v
  is-in-fin-sequence-is-in-permute-fin-sequence n v t x (k , refl) =
    map-equiv t k , refl

  is-in-tuple-is-in-permute-tuple :
    (n : ℕ) (v : tuple A n) (t : Permutation n) (x : A) →
    x ∈-tuple (permute-tuple n v t) → x ∈-tuple v
  is-in-tuple-is-in-permute-tuple n v t x I =
    is-in-tuple-is-in-fin-sequence
      ( n)
      ( v)
      ( x)
      ( is-in-fin-sequence-is-in-permute-fin-sequence
        ( n)
        ( fin-sequence-tuple n v)
        ( t)
        ( x)
        ( tr
          ( λ p → in-fin-sequence n x p)
          ( is-retraction-fin-sequence-tuple n
            ( fin-sequence-tuple n v ∘ map-equiv t))
          ( is-in-fin-sequence-is-in-tuple n (permute-tuple n v t) x I)))

  is-in-permute-fin-sequence-is-in-fin-sequence :
    (n : ℕ) (v : Fin n → A) (t : Permutation n) (x : A) →
    in-fin-sequence n x v → in-fin-sequence n x (v ∘ map-equiv t)
  is-in-permute-fin-sequence-is-in-fin-sequence n v t x (k , refl) =
    map-inv-equiv t k , ap v (inv (is-section-map-inv-equiv t k))

  is-in-permute-tuple-is-in-tuple :
    (n : ℕ) (v : tuple A n) (t : Permutation n) (x : A) →
    x ∈-tuple v → x ∈-tuple (permute-tuple n v t)
  is-in-permute-tuple-is-in-tuple n v t x I =
    is-in-tuple-is-in-fin-sequence
      ( n)
      ( permute-tuple n v t)
      ( x)
      ( tr
        ( λ p → in-fin-sequence n x p)
        ( inv
          ( is-retraction-fin-sequence-tuple n
            ( fin-sequence-tuple n v ∘ map-equiv t)))
        ( is-in-permute-fin-sequence-is-in-fin-sequence
          ( n)
          ( fin-sequence-tuple n v)
          ( t)
          ( x)
          ( is-in-fin-sequence-is-in-tuple n v x I)))
```

### If `μ : A → (B → B)` satisfies a commutativity property, then `fold-tuple b μ` is invariant under permutation for every `b : B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (μ : A → (B → B))
  where

  commutative-fold-tuple : UU (l1 ⊔ l2)
  commutative-fold-tuple = (a1 a2 : A) (b : B) → μ a1 (μ a2 b) ＝ μ a2 (μ a1 b)

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (b : B)
  (μ : A → (B → B))
  (C : commutative-fold-tuple μ)
  where

  invariant-swap-two-last-elements-transposition-fold-tuple :
    {n : ℕ} → (v : tuple A (succ-ℕ (succ-ℕ n))) →
    fold-tuple b μ v ＝
    fold-tuple
      ( b)
      ( μ)
      ( permute-tuple (succ-ℕ (succ-ℕ n))
      ( v)
      ( swap-two-last-elements-transposition-Fin n))
  invariant-swap-two-last-elements-transposition-fold-tuple {n} (y ∷ z ∷ v) =
    C y z (fold-tuple b μ v) ∙
    inv
      ( ap
        ( fold-tuple b μ)
        ( compute-swap-two-last-elements-transposition-Fin-permute-tuple
          ( n)
          ( v)
          ( y)
          ( z)))

  invariant-adjacent-transposition-fold-tuple :
    {n : ℕ} → (v : tuple A (succ-ℕ n)) → (k : Fin n) →
    fold-tuple b μ v ＝
    fold-tuple b μ (permute-tuple (succ-ℕ n) v (adjacent-transposition-Fin n k))
  invariant-adjacent-transposition-fold-tuple {succ-ℕ n} (x ∷ v) (inl k) =
    ap
      ( μ x)
      ( invariant-adjacent-transposition-fold-tuple v k) ∙
    inv
      ( ap
        ( fold-tuple b μ)
        ( compute-equiv-coproduct-permutation-id-equiv-permute-tuple
          ( succ-ℕ n)
          ( v)
          ( x)
          ( adjacent-transposition-Fin n k)))
  invariant-adjacent-transposition-fold-tuple {succ-ℕ n} (x ∷ v) (inr _) =
    invariant-swap-two-last-elements-transposition-fold-tuple (x ∷ v)

  invariant-list-adjacent-transpositions-fold-tuple :
    {n : ℕ} (v : tuple A (succ-ℕ n)) (l : list (Fin n)) →
    fold-tuple b μ v ＝
    fold-tuple
      ( b)
      ( μ)
      ( permute-tuple
        ( succ-ℕ n)
        ( v)
        ( permutation-list-adjacent-transpositions n l))
  invariant-list-adjacent-transpositions-fold-tuple {n} v nil =
    ap (fold-tuple b μ) (inv (compute-permute-tuple-id-equiv (succ-ℕ n) v))
  invariant-list-adjacent-transpositions-fold-tuple {n} v (cons x l) =
    ( invariant-adjacent-transposition-fold-tuple v x ∙
      ( ( invariant-list-adjacent-transpositions-fold-tuple
          ( permute-tuple (succ-ℕ n) v (adjacent-transposition-Fin n x))
          ( l)) ∙
        ( ap
          ( fold-tuple b μ)
          ( inv
            ( compute-composition-permute-tuple
              ( succ-ℕ n)
              ( v)
              ( adjacent-transposition-Fin n x)
              ( permutation-list-adjacent-transpositions n l))))))

  invariant-transposition-fold-tuple :
    {n : ℕ} (v : tuple A (succ-ℕ n)) (i j : Fin (succ-ℕ n)) (neq : i ≠ j) →
    fold-tuple b μ v ＝
    fold-tuple
      ( b)
      ( μ)
      ( permute-tuple (succ-ℕ n) v (transposition-Fin (succ-ℕ n) i j neq))
  invariant-transposition-fold-tuple {n} v i j neq =
    ( ( invariant-list-adjacent-transpositions-fold-tuple
        ( v)
        ( list-adjacent-transpositions-transposition-Fin n i j)) ∙
      ( ap
        ( λ t → fold-tuple b μ (permute-tuple (succ-ℕ n) v t))
        ( eq-htpy-equiv
          { e =
            permutation-list-adjacent-transpositions
              ( n)
              ( list-adjacent-transpositions-transposition-Fin n i j)}
          { e' = transposition-Fin (succ-ℕ n) i j neq}
          ( htpy-permutation-list-adjacent-transpositions-transposition-Fin
            ( n)
            ( i)
            ( j)
            ( neq)))))

  invariant-list-transpositions-fold-tuple :
    {n : ℕ}
    (v : tuple A n)
    (l : list (Σ (Fin n × Fin n) (λ (i , j) → i ≠ j))) →
    fold-tuple b μ v ＝
    fold-tuple
      ( b)
      ( μ)
      ( permute-tuple
        ( n)
        ( v)
        ( permutation-list-standard-transpositions-Fin n l))
  invariant-list-transpositions-fold-tuple {n} v nil =
    ap
      ( fold-tuple b μ)
      ( inv ( compute-permute-tuple-id-equiv n v))
  invariant-list-transpositions-fold-tuple {0} v (cons _ _) = refl
  invariant-list-transpositions-fold-tuple
    {succ-ℕ n} v (cons ((i , j) , neq) l) =
    ( invariant-transposition-fold-tuple v i j neq ∙
      ( ( invariant-list-transpositions-fold-tuple
          ( permute-tuple (succ-ℕ n) v (transposition-Fin (succ-ℕ n) i j neq))
          ( l)) ∙
        ( ap
          ( fold-tuple b μ)
          ( inv
            ( compute-composition-permute-tuple
              ( succ-ℕ n)
              ( v)
              ( transposition-Fin (succ-ℕ n) i j neq)
              ( permutation-list-standard-transpositions-Fin (succ-ℕ n) l))))))

  invariant-permutation-fold-tuple :
    {n : ℕ} → (v : tuple A n) → (f : Permutation n) →
    fold-tuple b μ v ＝ fold-tuple b μ (permute-tuple n v f)
  invariant-permutation-fold-tuple {n} v f =
    ( ( invariant-list-transpositions-fold-tuple
        ( v)
        ( list-standard-transpositions-permutation-Fin n f)) ∙
      ( ap
        ( λ f → fold-tuple b μ (permute-tuple n v f))
        ( eq-htpy-equiv
          {e =
            permutation-list-standard-transpositions-Fin
              ( n)
              ( list-standard-transpositions-permutation-Fin n f)}
          {e' = f}
          ( retraction-permutation-list-standard-transpositions-Fin n f))))
```

### `map-tuple` of the permutation of a tuple

```agda
eq-map-tuple-permute-tuple :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) {n : ℕ} (v : tuple A n) (t : Permutation n) →
  permute-tuple n (map-tuple f v) t ＝
  map-tuple f (permute-tuple n v t)
eq-map-tuple-permute-tuple f {n} v t =
  ( ( ap
      ( λ w →
        ( tuple-fin-sequence
          ( n)
          ( fin-sequence-tuple n w ∘ (map-equiv t)))))
      ( inv (map-tuple-map-fin-sequence f n v)) ∙
    ( ( ap
        ( λ p →
          tuple-fin-sequence
            ( n)
            ( p ∘ map-equiv t))
        ( is-retraction-fin-sequence-tuple
          ( n)
          ( map-fin-sequence n f (fin-sequence-tuple n v)))) ∙
      ( ( ap
          ( tuple-fin-sequence n ∘ map-fin-sequence n f)
          ( inv
            ( is-retraction-fin-sequence-tuple
              ( n)
              ( λ z → fin-sequence-tuple n v (map-equiv t z))))) ∙
        ( map-tuple-map-fin-sequence f n (permute-tuple n v t)))))
```
