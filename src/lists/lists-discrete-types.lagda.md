# Lists of elements in discrete types

```agda
module lists.lists-discrete-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.coproduct-types
open import foundation.decidable-equality
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.function-types
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists
```

</details>

## Idea

On this page we study [lists](lists.lists.md) of elements in
[discrete types](foundation.discrete-types.md), i.e., types with
[decidable equality](foundation.decidable-equality.md).

## Definitions

### The type of lists of a discrete type is discrete

```agda
has-decidable-equality-list :
  {l1 : Level} {A : UU l1} →
  has-decidable-equality A → has-decidable-equality (list A)
has-decidable-equality-list d nil nil = inl refl
has-decidable-equality-list d nil (cons x l) =
  inr (map-inv-raise ∘ Eq-eq-list nil (cons x l))
has-decidable-equality-list d (cons x l) nil =
  inr (map-inv-raise ∘ Eq-eq-list (cons x l) nil)
has-decidable-equality-list d (cons x l) (cons x' l') =
  is-decidable-iff
    ( eq-Eq-list (cons x l) (cons x' l'))
    ( Eq-eq-list (cons x l) (cons x' l'))
    ( is-decidable-product
      ( d x x')
      ( is-decidable-iff
        ( Eq-eq-list l l')
        ( eq-Eq-list l l')
        ( has-decidable-equality-list d l l')))

has-decidable-equality-has-decidable-equality-list :
  {l1 : Level} {A : UU l1} →
  has-decidable-equality (list A) → has-decidable-equality A
has-decidable-equality-has-decidable-equality-list d x y =
  is-decidable-left-factor
    ( is-decidable-iff
      ( Eq-eq-list (cons x nil) (cons y nil))
      ( eq-Eq-list (cons x nil) (cons y nil))
      ( d (cons x nil) (cons y nil)))
    ( raise-star)
```

### Testing whether an element of a discrete type is in a list

```agda
elem-list :
  {l1 : Level} {A : UU l1} →
  has-decidable-equality A →
  A → list A → bool
elem-list d x nil = false
elem-list d x (cons x' l) with (d x x')
... | inl _ = true
... | inr _ = elem-list d x l
```

### Removing duplicates in lists

```agda
union-list :
  {l1 : Level} {A : UU l1} →
  has-decidable-equality A →
  list A → list A → list A
union-list d nil l' = l'
union-list d (cons x l) l' with (elem-list d x l')
... | true = l'
... | false = cons x l'
```

## Properties

### If a list has an element then it is non empty

```agda
is-nonnil-elem-list :
  {l : Level} {A : UU l} →
  (d : has-decidable-equality A) →
  (a : A) →
  (l : list A) →
  elem-list d a l ＝ true →
  is-nonnil-list l
is-nonnil-elem-list d a nil ()
is-nonnil-elem-list d a (cons x l) p ()
```

### If the union of two lists is empty, then these two lists are empty

```agda
is-nil-union-is-nil-list :
  {l : Level} {A : UU l} →
  (d : has-decidable-equality A) →
  (l l' : list A) →
  union-list d l l' ＝ nil →
  is-nil-list l × is-nil-list l'
is-nil-union-is-nil-list d nil l' p = (refl , p)
is-nil-union-is-nil-list d (cons x l) l' p with (elem-list d x l') in q
... | true =
  ex-falso (is-nonnil-elem-list d x l' q p)
... | false = ex-falso (is-nonnil-cons-list x l' p)
```
