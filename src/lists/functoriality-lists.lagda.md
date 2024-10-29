# Functoriality of the list operation

```agda
module lists.functoriality-lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.equality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.function-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.propositions
open import foundation.transport-along-identifications
open import foundation.universe-levels

open import linear-algebra.functoriality-vectors
open import linear-algebra.vectors

open import lists.arrays
open import lists.concatenation-lists
open import lists.lists
```

</details>

## Idea

Given a functiion `f : A → B`, we obtain a function
`map-list f : list A → list B`.

## Definition

```agda
map-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) →
  list A → list B
map-list f = fold-list nil (λ a → cons (f a))
```

## Properties

### `map-list` preserves the length of a list

```agda
length-map-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (l : list A) →
  Id (length-list (map-list f l)) (length-list l)
length-map-list f nil = refl
length-map-list f (cons x l) =
  ap succ-ℕ (length-map-list f l)
```

### Link between `map-list` and `map-vec`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B)
  where

  map-list-map-vec-list :
    (l : list A) →
    list-vec (length-list l) (map-vec f (vec-list l)) ＝
    map-list f l
  map-list-map-vec-list nil = refl
  map-list-map-vec-list (cons x l) =
    eq-Eq-list
      ( list-vec (length-list (cons x l)) (map-vec f (vec-list (cons x l))))
      ( map-list f (cons x l))
      ( refl ,
        Eq-eq-list
          ( list-vec (length-list l) (map-vec f (vec-list l)))
          ( map-list f l)
          ( map-list-map-vec-list l))

  map-vec-map-list-vec :
    (n : ℕ) (v : vec A n) →
    tr
      ( vec B)
      ( length-map-list f (list-vec n v) ∙
        compute-length-list-list-vec n v)
      ( vec-list (map-list f (list-vec n v))) ＝
    map-vec f v
  map-vec-map-list-vec 0 empty-vec = refl
  map-vec-map-list-vec (succ-ℕ n) (x ∷ v) =
    compute-tr-vec
      ( ap succ-ℕ (length-map-list f (list-vec n v)) ∙
        compute-length-list-list-vec (succ-ℕ n) (x ∷ v))
      ( vec-list (fold-list nil (λ a → cons (f a)) (list-vec n v)))
      ( f x) ∙
    eq-Eq-vec
      ( succ-ℕ n)
      ( f x ∷
        tr
          ( vec B)
          ( is-injective-succ-ℕ
            ( ap succ-ℕ (length-map-list f (list-vec n v)) ∙
              compute-length-list-list-vec (succ-ℕ n) (x ∷ v)))
          ( vec-list (map-list f (list-vec n v))))
      ( map-vec f (x ∷ v))
      ( refl ,
        ( Eq-eq-vec
          ( n)
          ( tr
            ( vec B)
            ( is-injective-succ-ℕ
              ( ap succ-ℕ (length-map-list f (list-vec n v)) ∙
                compute-length-list-list-vec (succ-ℕ n) (x ∷ v)))
            ( vec-list (map-list f (list-vec n v))))
          ( map-vec f v)
          ( tr
            ( λ p →
              tr
                ( vec B)
                ( p)
                ( vec-list (map-list f (list-vec n v))) ＝
              map-vec f v)
            ( eq-is-prop
              ( is-set-ℕ
                ( length-list (map-list f (list-vec n v)))
                ( n)))
            ( map-vec-map-list-vec n v))))

  map-vec-map-list-vec' :
    (n : ℕ) (v : vec A n) →
    vec-list (map-list f (list-vec n v)) ＝
    tr
      ( vec B)
      ( inv
        ( length-map-list f (list-vec n v) ∙
          compute-length-list-list-vec n v))
      ( map-vec f v)
  map-vec-map-list-vec' n v =
    eq-transpose-tr'
      ( length-map-list f (list-vec n v) ∙ compute-length-list-list-vec n v)
      ( map-vec-map-list-vec n v)

  vec-list-map-list-map-vec-list :
    (l : list A) →
    tr
      ( vec B)
      ( length-map-list f l)
      ( vec-list (map-list f l)) ＝
    map-vec f (vec-list l)
  vec-list-map-list-map-vec-list nil = refl
  vec-list-map-list-map-vec-list (cons x l) =
    compute-tr-vec
      ( ap succ-ℕ (length-map-list f l))
      ( vec-list (map-list f l))
      ( f x) ∙
    eq-Eq-vec
      ( succ-ℕ (length-list l))
      ( f x ∷
        tr
          ( vec B)
          ( is-injective-succ-ℕ (ap succ-ℕ (length-map-list f l)))
          ( vec-list (map-list f l)))
      ( map-vec f (vec-list (cons x l)))
      ( refl ,
        Eq-eq-vec
          ( length-list l)
          ( tr
            ( vec B)
            ( is-injective-succ-ℕ (ap succ-ℕ (length-map-list f l)))
            ( vec-list (map-list f l)))
          ( map-vec f (vec-list l))
          ( tr
            ( λ p →
              ( tr
                ( vec B)
                ( p)
                ( vec-list (map-list f l))) ＝
              ( map-vec f (vec-list l)))
            ( eq-is-prop
              ( is-set-ℕ (length-list (map-list f l)) (length-list l)))
            ( vec-list-map-list-map-vec-list l)))

  vec-list-map-list-map-vec-list' :
    (l : list A) →
    vec-list (map-list f l) ＝
    tr
      ( vec B)
      ( inv (length-map-list f l))
      ( map-vec f (vec-list l))
  vec-list-map-list-map-vec-list' l =
    eq-transpose-tr'
      ( length-map-list f l)
      ( vec-list-map-list-map-vec-list l)

  list-vec-map-vec-map-list-vec :
    (n : ℕ) (v : vec A n) →
    list-vec
      ( length-list (map-list f (list-vec n v)))
      ( vec-list (map-list f (list-vec n v))) ＝
    list-vec n (map-vec f v)
  list-vec-map-vec-map-list-vec n v =
    ap
      ( λ p → list-vec (pr1 p) (pr2 p))
      ( eq-pair-Σ
        ( length-map-list f (list-vec n v) ∙
          compute-length-list-list-vec n v)
        ( map-vec-map-list-vec n v))
```

### `map-list` preserves concatenation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  preserves-concat-map-list :
    (l k : list A) →
    Id
      ( map-list f (concat-list l k))
      ( concat-list (map-list f l) (map-list f k))
  preserves-concat-map-list nil k = refl
  preserves-concat-map-list (cons x l) k =
    ap (cons (f x)) (preserves-concat-map-list l k)
```

### Functoriality of the list operation

First we introduce the functoriality of the list operation, because it will come
in handy when we try to define and prove more advanced things.

```agda
identity-law-map-list :
  {l1 : Level} {A : UU l1} →
  map-list (id {A = A}) ~ id
identity-law-map-list nil = refl
identity-law-map-list (cons a x) =
  ap (cons a) (identity-law-map-list x)

composition-law-map-list :
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} →
  (f : A → B) (g : B → C) →
  map-list (g ∘ f) ~ (map-list g ∘ map-list f)
composition-law-map-list f g nil = refl
composition-law-map-list f g (cons a x) =
  ap (cons (g (f a))) (composition-law-map-list f g x)
```

### `map-list` applied to lists of the form `snoc x a`

```agda
map-snoc-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B) (x : list A) (a : A) →
  map-list f (snoc x a) ＝ snoc (map-list f x) (f a)
map-snoc-list f nil a = refl
map-snoc-list f (cons b x) a = ap (cons (f b)) (map-snoc-list f x a)
```
