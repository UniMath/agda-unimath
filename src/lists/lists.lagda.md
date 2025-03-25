# Lists

```agda
module lists.lists where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.unit-type
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.maybe
open import foundation-core.negation
```

</details>

## Idea

The type of lists of elements of a type `A` is defined inductively, with an
empty list and an operation that extends a list with one element from `A`.

## Definition

### The inductive definition of the type of lists

```agda
data list {l : Level} (A : UU l) : UU l where
  nil : list A
  cons : A → list A → list A
{-# BUILTIN LIST list #-}
```

### Predicates on the type of lists

```agda
is-nil-list : {l : Level} {A : UU l} → list A → UU l
is-nil-list l = (l ＝ nil)

is-nonnil-list : {l : Level} {A : UU l} → list A → UU l
is-nonnil-list l = ¬ (is-nil-list l)

is-cons-list : {l : Level} {A : UU l} → list A → UU l
is-cons-list {l1} {A} l = Σ (A × list A) (λ (a , l') → l ＝ cons a l')
```

## The induction principle of the type of lists

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : list A → UU l2)
  where

  ind-list :
    P nil → ((a : A) (as : list A) → P as → P (cons a as)) →
    (x : list A) → P x
  ind-list Pnil Pcons nil = Pnil
  ind-list Pnil Pcons (cons a as) = Pcons a as (ind-list Pnil Pcons as)
```

## Operations

### Fold

```agda
fold-list :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (b : B) (μ : A → (B → B)) →
  list A → B
fold-list b μ nil = b
fold-list b μ (cons a l) = μ a (fold-list b μ l)
```

### The dual of `cons`

```agda
snoc : {l : Level} {A : UU l} → list A → A → list A
snoc nil a = cons a nil
snoc (cons b l) a = cons b (snoc l a)
```

### The unit list

```agda
unit-list : {l : Level} {A : UU l} → A → list A
unit-list a = cons a nil
```

### The length of a list

```agda
length-list : {l : Level} {A : UU l} → list A → ℕ
length-list = fold-list 0 (λ a → succ-ℕ)
```

### The elementhood predicate on lists

```agda
infix 6 _∈-list_

data _∈-list_ {l : Level} {A : UU l} : A → list A → UU l where
  is-head : (a : A) (l : list A) → a ∈-list (cons a l)
  is-in-tail : (a x : A) (l : list A) → a ∈-list l → a ∈-list (cons x l)
```

## Properties

### A list that uses cons is not nil

```agda
is-nonnil-cons-list :
  {l : Level} {A : UU l} →
  (a : A) → (l : list A) → is-nonnil-list (cons a l)
is-nonnil-cons-list a l ()

is-nonnil-is-cons-list :
  {l : Level} {A : UU l} →
  (l : list A) → is-cons-list l → is-nonnil-list l
is-nonnil-is-cons-list l ((a , l') , refl) q =
  is-nonnil-cons-list a l' q
```

### A list that uses cons is not nil

```agda
is-cons-is-nonnil-list :
  {l : Level} {A : UU l} →
  (l : list A) → is-nonnil-list l → is-cons-list l
is-cons-is-nonnil-list nil p = ex-falso (p refl)
is-cons-is-nonnil-list (cons x l) p = ((x , l) , refl)

head-is-nonnil-list :
  {l : Level} {A : UU l} →
  (l : list A) → is-nonnil-list l → A
head-is-nonnil-list l p =
  pr1 (pr1 (is-cons-is-nonnil-list l p))

tail-is-nonnil-list :
  {l : Level} {A : UU l} →
  (l : list A) → is-nonnil-list l → list A
tail-is-nonnil-list l p =
  pr2 (pr1 (is-cons-is-nonnil-list l p))
```

### The length operation behaves well with respect to the other list operations

```agda
length-nil :
  {l1 : Level} {A : UU l1} →
  Id (length-list {A = A} nil) zero-ℕ
length-nil = refl

is-nil-is-zero-length-list :
  {l1 : Level} {A : UU l1}
  (l : list A) →
  is-zero-ℕ (length-list l) →
  is-nil-list l
is-nil-is-zero-length-list nil p = refl

is-nonnil-is-nonzero-length-list :
  {l1 : Level} {A : UU l1}
  (l : list A) →
  is-nonzero-ℕ (length-list l) →
  is-nonnil-list l
is-nonnil-is-nonzero-length-list nil p q = p refl
is-nonnil-is-nonzero-length-list (cons x l) p ()

is-nonzero-length-is-nonnil-list :
  {l1 : Level} {A : UU l1}
  (l : list A) →
  is-nonnil-list l →
  is-nonzero-ℕ (length-list l)
is-nonzero-length-is-nonnil-list nil p q = p refl

lenght-tail-is-nonnil-list :
  {l1 : Level} {A : UU l1}
  (l : list A) → (p : is-nonnil-list l) →
  succ-ℕ (length-list (tail-is-nonnil-list l p)) ＝
    length-list l
lenght-tail-is-nonnil-list nil p = ex-falso (p refl)
lenght-tail-is-nonnil-list (cons x l) p = refl
```

### Head and tail operations

We define the head and tail operations, and we define the operations of picking
and removing the last element from a list.

```agda
head-snoc-list :
  {l : Level} {A : UU l} (l : list A) → A → A
head-snoc-list nil a = a
head-snoc-list (cons h l) a = h

head-list :
  {l1 : Level} {A : UU l1} → list A → list A
head-list nil = nil
head-list (cons a x) = unit-list a

tail-list :
  {l1 : Level} {A : UU l1} → list A → list A
tail-list nil = nil
tail-list (cons a x) = x

last-element-list :
  {l1 : Level} {A : UU l1} → list A → list A
last-element-list nil = nil
last-element-list (cons a nil) = unit-list a
last-element-list (cons a (cons b x)) = last-element-list (cons b x)
```

### Removing the last element of a list

```agda
remove-last-element-list :
  {l1 : Level} {A : UU l1} → list A → list A
remove-last-element-list nil = nil
remove-last-element-list (cons a nil) = nil
remove-last-element-list (cons a (cons b x)) =
  cons a (remove-last-element-list (cons b x))
```

### Properties of heads and tails and their duals

```agda
head-snoc-snoc-list :
  {l1 : Level} {A : UU l1} (x : list A) (a : A) (b : A) →
  head-list (snoc (snoc x a) b) ＝ head-list (snoc x a)
head-snoc-snoc-list nil a b = refl
head-snoc-snoc-list (cons c x) a b = refl

tail-snoc-snoc-list :
  {l1 : Level} {A : UU l1} (x : list A) (a : A) (b : A) →
  tail-list (snoc (snoc x a) b) ＝ snoc (tail-list (snoc x a)) b
tail-snoc-snoc-list nil a b = refl
tail-snoc-snoc-list (cons c x) a b = refl

last-element-snoc :
  {l1 : Level} {A : UU l1} (x : list A) (a : A) →
  Id (last-element-list (snoc x a)) (unit-list a)
last-element-snoc nil a = refl
last-element-snoc (cons b nil) a = refl
last-element-snoc (cons b (cons c x)) a =
  last-element-snoc (cons c x) a
```

### Algebra structure on the type of lists of elements of `A`

```agda
map-algebra-list :
  {l1 : Level} (A : UU l1) →
  Maybe (A × list A) → list A
map-algebra-list A (inl (a , x)) = cons a x
map-algebra-list A (inr star) = nil

map-inv-algebra-list :
  {l1 : Level} (A : UU l1) →
  list A → Maybe (A × list A)
map-inv-algebra-list A nil = inr star
map-inv-algebra-list A (cons a x) = inl (pair a x)

is-section-map-inv-algebra-list :
  {l1 : Level} (A : UU l1) →
  (map-algebra-list A ∘ map-inv-algebra-list A) ~ id
is-section-map-inv-algebra-list A nil = refl
is-section-map-inv-algebra-list A (cons a x) = refl

is-retraction-map-inv-algebra-list :
  {l1 : Level} (A : UU l1) →
  (map-inv-algebra-list A ∘ map-algebra-list A) ~ id
is-retraction-map-inv-algebra-list A (inl (a , x)) = refl
is-retraction-map-inv-algebra-list A (inr star) = refl

is-equiv-map-algebra-list :
  {l1 : Level} (A : UU l1) → is-equiv (map-algebra-list A)
is-equiv-map-algebra-list A =
  is-equiv-is-invertible
    ( map-inv-algebra-list A)
    ( is-section-map-inv-algebra-list A)
    ( is-retraction-map-inv-algebra-list A)
```
