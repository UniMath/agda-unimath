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

open import lists.arrays
open import lists.concatenation-lists
open import lists.functoriality-tuples
open import lists.lists
open import lists.tuples
```

</details>

## Idea

Given a function `f : A → B`, we obtain a function
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
  length-list (map-list f l) ＝ length-list l
length-map-list f nil = refl
length-map-list f (cons x l) =
  ap succ-ℕ (length-map-list f l)
```

### Link between `map-list` and `map-tuple`

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  (f : A → B)
  where

  map-list-map-tuple-list :
    (l : list A) →
    list-tuple (length-list l) (map-tuple f (tuple-list l)) ＝
    map-list f l
  map-list-map-tuple-list nil = refl
  map-list-map-tuple-list (cons x l) =
    eq-Eq-list
      ( list-tuple
        ( length-list (cons x l))
        ( map-tuple f (tuple-list (cons x l))))
      ( map-list f (cons x l))
      ( refl ,
        Eq-eq-list
          ( list-tuple (length-list l) (map-tuple f (tuple-list l)))
          ( map-list f l)
          ( map-list-map-tuple-list l))

  map-tuple-map-list-tuple :
    (n : ℕ) (v : tuple A n) →
    tr
      ( tuple B)
      ( length-map-list f (list-tuple n v) ∙
        compute-length-list-list-tuple n v)
      ( tuple-list (map-list f (list-tuple n v))) ＝
    map-tuple f v
  map-tuple-map-list-tuple 0 empty-tuple = refl
  map-tuple-map-list-tuple (succ-ℕ n) (x ∷ v) =
    compute-tr-tuple
      ( ap succ-ℕ (length-map-list f (list-tuple n v)) ∙
        compute-length-list-list-tuple (succ-ℕ n) (x ∷ v))
      ( tuple-list (fold-list nil (λ a → cons (f a)) (list-tuple n v)))
      ( f x) ∙
    eq-Eq-tuple
      ( succ-ℕ n)
      ( f x ∷
        tr
          ( tuple B)
          ( is-injective-succ-ℕ
            ( ap succ-ℕ (length-map-list f (list-tuple n v)) ∙
              compute-length-list-list-tuple (succ-ℕ n) (x ∷ v)))
          ( tuple-list (map-list f (list-tuple n v))))
      ( map-tuple f (x ∷ v))
      ( refl ,
        ( Eq-eq-tuple
          ( n)
          ( tr
            ( tuple B)
            ( is-injective-succ-ℕ
              ( ap succ-ℕ (length-map-list f (list-tuple n v)) ∙
                compute-length-list-list-tuple (succ-ℕ n) (x ∷ v)))
            ( tuple-list (map-list f (list-tuple n v))))
          ( map-tuple f v)
          ( tr
            ( λ p →
              tr
                ( tuple B)
                ( p)
                ( tuple-list (map-list f (list-tuple n v))) ＝
              map-tuple f v)
            ( eq-is-prop
              ( is-set-ℕ
                ( length-list (map-list f (list-tuple n v)))
                ( n)))
            ( map-tuple-map-list-tuple n v))))

  map-tuple-map-list-tuple' :
    (n : ℕ) (v : tuple A n) →
    tuple-list (map-list f (list-tuple n v)) ＝
    tr
      ( tuple B)
      ( inv
        ( length-map-list f (list-tuple n v) ∙
          compute-length-list-list-tuple n v))
      ( map-tuple f v)
  map-tuple-map-list-tuple' n v =
    eq-transpose-tr'
      ( length-map-list f (list-tuple n v) ∙ compute-length-list-list-tuple n v)
      ( map-tuple-map-list-tuple n v)

  tuple-list-map-list-map-tuple-list :
    (l : list A) →
    tr
      ( tuple B)
      ( length-map-list f l)
      ( tuple-list (map-list f l)) ＝
    map-tuple f (tuple-list l)
  tuple-list-map-list-map-tuple-list nil = refl
  tuple-list-map-list-map-tuple-list (cons x l) =
    compute-tr-tuple
      ( ap succ-ℕ (length-map-list f l))
      ( tuple-list (map-list f l))
      ( f x) ∙
    eq-Eq-tuple
      ( succ-ℕ (length-list l))
      ( f x ∷
        tr
          ( tuple B)
          ( is-injective-succ-ℕ (ap succ-ℕ (length-map-list f l)))
          ( tuple-list (map-list f l)))
      ( map-tuple f (tuple-list (cons x l)))
      ( refl ,
        Eq-eq-tuple
          ( length-list l)
          ( tr
            ( tuple B)
            ( is-injective-succ-ℕ (ap succ-ℕ (length-map-list f l)))
            ( tuple-list (map-list f l)))
          ( map-tuple f (tuple-list l))
          ( tr
            ( λ p →
              ( tr
                ( tuple B)
                ( p)
                ( tuple-list (map-list f l))) ＝
              ( map-tuple f (tuple-list l)))
            ( eq-is-prop
              ( is-set-ℕ (length-list (map-list f l)) (length-list l)))
            ( tuple-list-map-list-map-tuple-list l)))

  tuple-list-map-list-map-tuple-list' :
    (l : list A) →
    tuple-list (map-list f l) ＝
    tr
      ( tuple B)
      ( inv (length-map-list f l))
      ( map-tuple f (tuple-list l))
  tuple-list-map-list-map-tuple-list' l =
    eq-transpose-tr'
      ( length-map-list f l)
      ( tuple-list-map-list-map-tuple-list l)

  list-tuple-map-tuple-map-list-tuple :
    (n : ℕ) (v : tuple A n) →
    list-tuple
      ( length-list (map-list f (list-tuple n v)))
      ( tuple-list (map-list f (list-tuple n v))) ＝
    list-tuple n (map-tuple f v)
  list-tuple-map-tuple-map-list-tuple n v =
    ap
      ( λ p → list-tuple (pr1 p) (pr2 p))
      ( eq-pair-Σ
        ( length-map-list f (list-tuple n v) ∙
          compute-length-list-list-tuple n v)
        ( map-tuple-map-list-tuple n v))
```

### `map-list` preserves concatenation

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  preserves-concat-map-list :
    (l k : list A) →
    map-list f (concat-list l k) ＝ concat-list (map-list f l) (map-list f k)
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
