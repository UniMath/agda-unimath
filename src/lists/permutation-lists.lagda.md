# Permutations of lists

```agda
module lists.permutation-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import finite-group-theory.permutations-standard-finite-types

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import lists.arrays
open import lists.functoriality-lists
open import lists.functoriality-tuples
open import lists.lists
open import lists.permutation-tuples
open import lists.tuples
```

</details>

## Idea

Given an [array](lists.arrays.md) `t` of length `n` and an
[automorphism](foundation.automorphisms.md) `σ` of `Fin n`, the
{{#concept "permutation" WD="permutation" WDID=Q161519 Disambiguation="of an array"}}
of `t` according to `σ` is the array where the indexes are permuted by `σ`.
Then, we can define what is a
{{#concept "permutation" Disambiguation="of a list" WD="permutation" WDID=Q161519 Agda=permute-list}}
of a [list](lists.lists.md) of length `n` via the
[equivalence](foundation-core.equivalences.md) between arrays and lists.

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  permute-list : (l : list A) → Permutation (length-list l) → list A
  permute-list l s =
    list-tuple
      ( length-list l)
      ( permute-tuple (length-list l) (tuple-list l) s)
```

### The predicate that a function from `list` to `list` is permuting lists

```agda
  is-permutation-list : (list A → list A) → UU l
  is-permutation-list f =
    (l : list A) →
    Σ ( Permutation (length-list l))
      ( λ t → f l ＝ permute-list l t)

  permutation-is-permutation-list :
    (f : list A → list A) → is-permutation-list f →
    ((l : list A) → Permutation (length-list l))
  permutation-is-permutation-list f P l = pr1 (P l)

  eq-permute-list-permutation-is-permutation-list :
    (f : list A → list A) → (P : is-permutation-list f) →
    (l : list A) →
    (f l ＝ permute-list l (permutation-is-permutation-list f P l))
  eq-permute-list-permutation-is-permutation-list f P l = pr2 (P l)
```

## Properties

### The length of a permuted list

```agda
  length-permute-list :
    (l : list A) (t : Permutation (length-list l)) →
    length-list (permute-list l t) ＝ (length-list l)
  length-permute-list l t =
    compute-length-list-list-tuple
      ( length-list l)
      ( permute-tuple (length-list l) (tuple-list l) t)
```

### Link between `permute-list` and `permute-tuple`

```agda
  eq-tuple-list-permute-list :
    (l : list A) (f : Permutation (length-list l)) →
    permute-tuple (length-list l) (tuple-list l) f ＝
    tr
      ( tuple A)
      ( _)
      ( tuple-list ( permute-list l f))
  eq-tuple-list-permute-list l f =
    inv
      ( pr2
        ( pair-eq-Σ
          ( is-retraction-tuple-list
            ( length-list l ,
              permute-tuple (length-list l) (tuple-list l) f))))
```

### If a function `f` from `tuple` to `tuple` is a permutation of tuples then `list-tuple ∘ f ∘ tuple-list` is a permutation of lists

```agda
  is-permutation-list-is-permutation-tuple :
    (f : (n : ℕ) → tuple A n → tuple A n) →
    ((n : ℕ) → is-permutation-tuple n (f n)) →
    is-permutation-list
      ( λ l → list-tuple (length-list l) (f (length-list l) (tuple-list l)))
  pr1 (is-permutation-list-is-permutation-tuple f T l) =
    pr1 (T (length-list l) (tuple-list l))
  pr2 (is-permutation-list-is-permutation-tuple f T l) =
    ap
      ( λ p → list-tuple (length-list l) p)
      ( pr2 (T (length-list l) (tuple-list l)))
```

### If `x` is in `permute-list l t` then `x` is in `l`

```agda
  is-in-list-is-in-permute-list :
    (l : list A) (t : Permutation (length-list l)) (x : A) →
    x ∈-list (permute-list l t) → x ∈-list l
  is-in-list-is-in-permute-list l t x I =
    is-in-list-is-in-tuple-list
      ( l)
      ( x)
      ( is-in-tuple-is-in-permute-tuple
        ( length-list l)
        ( tuple-list l)
        ( t)
        ( x)
        ( tr
          ( λ p → x ∈-tuple (pr2 p))
          ( is-retraction-tuple-list
            ( length-list l ,
              permute-tuple (length-list l) (tuple-list l) t))
          ( is-in-tuple-list-is-in-list
            ( list-tuple
              ( length-list l)
              ( permute-tuple (length-list l) (tuple-list l) t))
            ( x)
            ( I))))

  is-in-permute-list-is-in-list :
    (l : list A) (t : Permutation (length-list l)) (x : A) →
    x ∈-list l → x ∈-list (permute-list l t)
  is-in-permute-list-is-in-list l t x I =
    is-in-list-is-in-tuple-list
      ( permute-list l t)
      ( x)
      ( tr
        ( λ p → x ∈-tuple (pr2 p))
        ( inv
          ( is-retraction-tuple-list
            ( length-list l , permute-tuple (length-list l) (tuple-list l) t)))
        ( is-in-permute-tuple-is-in-tuple
          ( length-list l)
          ( tuple-list l)
          ( t)
          ( x)
          ( is-in-tuple-list-is-in-list l x I)))
```

### If `μ : A → (B → B)` satisfies a commutativity property, then `fold-list b μ` is invariant under permutation for every `b : B`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (b : B)
  (μ : A → (B → B))
  (C : commutative-fold-tuple μ)
  where

  invariant-fold-tuple-tr :
    {n m : ℕ} (v : tuple A n) (eq : n ＝ m) →
    fold-tuple b μ (tr (tuple A) eq v) ＝ fold-tuple b μ v
  invariant-fold-tuple-tr v refl = refl

  invariant-permutation-fold-list :
    (l : list A) → (f : Permutation (length-list l)) →
    fold-list b μ l ＝ fold-list b μ (permute-list l f)
  invariant-permutation-fold-list l f =
    ( inv (htpy-fold-list-fold-tuple b μ l) ∙
      ( invariant-permutation-fold-tuple b μ C (tuple-list l) f ∙
        ( ap (fold-tuple b μ) (eq-tuple-list-permute-list l f) ∙
          ( ( invariant-fold-tuple-tr
              { m = length-list l}
              ( tuple-list (permute-list l f))
              ( _)) ∙
            ( htpy-fold-list-fold-tuple b μ (permute-list l f))))))
```

### `map-list` of the permutation of a list

```agda
compute-tr-permute-tuple :
  {l : Level} {A : UU l} {n m : ℕ}
  (e : n ＝ m) (v : tuple A n) (t : Permutation m) →
  tr
    ( tuple A)
    ( e)
    ( permute-tuple
      ( n)
      ( v)
      ( tr Permutation (inv e) t)) ＝
  permute-tuple
    ( m)
    ( tr (tuple A) e v)
    ( t)
compute-tr-permute-tuple refl v t = refl

compute-tr-map-tuple :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) {n m : ℕ} (p : n ＝ m) (v : tuple A n) →
  tr (tuple B) p (map-tuple f v) ＝ map-tuple f (tr (tuple A) p v)
compute-tr-map-tuple f refl v = refl

helper-compute-list-tuple-map-tuple-permute-tuple-tuple-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) (p : list A) (t : Permutation (length-list p)) →
  tr
    ( tuple B)
    ( inv (length-permute-list p t))
    ( map-tuple f (permute-tuple (length-list p) (tuple-list p) t)) ＝
  map-tuple f (tuple-list (permute-list p t))
helper-compute-list-tuple-map-tuple-permute-tuple-tuple-list f p t =
  ( ( compute-tr-map-tuple
      ( f)
      ( inv (length-permute-list p t))
      ( permute-tuple (length-list p) (tuple-list p) t)) ∙
    ( ( ap
        ( λ P →
          map-tuple
            ( f)
            ( tr (tuple _) P (permute-tuple (length-list p) (tuple-list p) t)))
        ( eq-is-prop (is-set-ℕ _ _))) ∙
      ( ap
        ( map-tuple f)
        ( pr2
          ( pair-eq-Σ
            ( inv
              ( is-retraction-tuple-list
                ( length-list p ,
                  permute-tuple (length-list p) (tuple-list p) t))))))))

compute-list-tuple-map-tuple-permute-tuple-tuple-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) (p : list A) (t : Permutation (length-list p)) →
  list-tuple
    ( length-list p)
    ( map-tuple f (permute-tuple (length-list p) (tuple-list p) t)) ＝
  list-tuple
    ( length-list (permute-list p t))
    ( map-tuple f (tuple-list (permute-list p t)))
compute-list-tuple-map-tuple-permute-tuple-tuple-list f p t =
  ap
    ( λ p → list-tuple (pr1 p) (pr2 p))
    ( eq-pair-Σ
      ( inv (length-permute-list p t))
      ( ( helper-compute-list-tuple-map-tuple-permute-tuple-tuple-list f p t)))

eq-map-list-permute-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B) (p : list A) (t : Permutation (length-list p)) →
  permute-list (map-list f p) (tr Permutation (inv (length-map-list f p)) t) ＝
  map-list f (permute-list p t)
eq-map-list-permute-list {B = B} f p t =
  ( ( ap
      ( λ (n , p) → list-tuple n p)
      ( eq-pair-Σ
        ( length-map-list f p)
        ( ( ap
            ( λ x →
              tr
                ( tuple B)
                ( length-map-list f p)
                ( permute-tuple
                  ( length-list (map-list f p))
                  ( x)
                  ( tr Permutation (inv (length-map-list f p)) t)))
            ( tuple-list-map-list-map-tuple-list' f p)) ∙
          ( ( compute-tr-permute-tuple
              ( length-map-list f p)
              ( tr
                ( tuple B)
                ( inv (length-map-list f p))
                ( map-tuple f (tuple-list p)))
              ( t)) ∙
            ( ap
              ( λ v → permute-tuple (length-list p) v t)
              ( is-section-inv-tr
                ( tuple B)
                ( length-map-list f p)
                ( map-tuple f (tuple-list p)))))))) ∙
    ( ( ap
        ( list-tuple (length-list p))
        ( eq-map-tuple-permute-tuple f (tuple-list p) t)) ∙
      ( compute-list-tuple-map-tuple-permute-tuple-tuple-list f p t ∙
        ( map-list-map-tuple-list f (permute-list p t)))))
```
