# The elementhood relation on lists

```agda
module lists.elementhood-relation-lists where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.empty-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.raising-universe-levels
open import foundation.retractions
open import foundation.sections
open import foundation.unit-type
open import foundation.universe-levels

open import linear-algebra.vectors

open import lists.lists

open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

Consider a [list](lists.lists.md) `l` of elements of a type `A`. We say that an element `a : A` is an {{#concept "element" Disambiguation="lists" Agda=_∈-list_}} of `l` if there is an element of type `a ∈-list l`, which is the data type with constructors

```text
  is-head : (a : A) (l : list A) → a ∈-list cons a l
  is-in-tail : (a x : A) (l : list) → a ∈-list l → a ∈-list cons x l
```

Equivalently, the elementhood relation can be defined inductively by

```text
  a ∈-list nil := empty
  a ∈-list (cons x l) := (a ＝ x) + (a ∈-list l).
```

The elementhood relation is a special case of the [elementhood relation](trees.elementhood-relation-w-types.md) on [W-types](trees.w-types.md) and the [elementhood relation](trees.elementhood-relation-coalgebras-polynomial-endofunctors.md) of [coalgebras](trees.coalgebras-polynomial-endofunctors.md) of [polynomial endofunctors](trees.polynomial-endofunctors.md).

## Definitions

### The elementhood predicate on lists

```agda
infix 6 _∈-list_

data _∈-list_ {l1 : Level} {A : UU l1} : A → list A → UU l1 where
  is-head : (a : A) (l : list A) → a ∈-list cons a l
  is-in-tail : (a x : A) (l : list A) → a ∈-list l → a ∈-list cons x l
```

### The recursive definition of the elementhood relation

```agda
elementhood-list : {l1 : Level} {A : UU l1} → A → list A → UU l1
elementhood-list a nil = raise-empty _
elementhood-list a (cons x l) = (a ＝ x) + (elementhood-list a l)
```

## Properties

### The `nil` list has no elements

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  is-empty-∈-nil-list : (x : A) → is-empty (x ∈-list nil)
  is-empty-∈-nil-list x ()
```

### The two definitions of the elementhood relation are equivalent

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  map-compute-elementhood-list :
    (a : A) (l : list A) → elementhood-list a l → a ∈-list l
  map-compute-elementhood-list a nil (map-raise ())
  map-compute-elementhood-list a (cons .a l) (inl refl) =
    is-head a l
  map-compute-elementhood-list a (cons x l) (inr H) =
    is-in-tail a x l (map-compute-elementhood-list a l H)

  map-inv-compute-elementhood-list :
    (a : A) (l : list A) → a ∈-list l → elementhood-list a l
  map-inv-compute-elementhood-list a .(cons a l) (is-head .a l) =
    inl refl
  map-inv-compute-elementhood-list a .(cons x l) (is-in-tail .a x l H) =
    inr (map-inv-compute-elementhood-list a l H)

  is-section-map-inv-compute-elementhood-list :
    (a : A) (l : list A) →
    is-section
      ( map-compute-elementhood-list a l)
      ( map-inv-compute-elementhood-list a l)
  is-section-map-inv-compute-elementhood-list a .(cons a l) (is-head .a l) =
    refl
  is-section-map-inv-compute-elementhood-list a ._ (is-in-tail .a x l H) =
    ap (is-in-tail a x l) (is-section-map-inv-compute-elementhood-list a l H)

  is-retraction-map-inv-compute-elementhood-list :
    (a : A) (l : list A) →
    is-retraction
      ( map-compute-elementhood-list a l)
      ( map-inv-compute-elementhood-list a l)
  is-retraction-map-inv-compute-elementhood-list a nil (map-raise ())
  is-retraction-map-inv-compute-elementhood-list a (cons .a l) (inl refl) =
    refl
  is-retraction-map-inv-compute-elementhood-list a (cons x l) (inr H) =
    ap inr (is-retraction-map-inv-compute-elementhood-list a l H)

  is-equiv-map-compute-elementhood-list :
    (a : A) (l : list A) → is-equiv (map-compute-elementhood-list a l)
  is-equiv-map-compute-elementhood-list a l =
    is-equiv-is-invertible
      ( map-inv-compute-elementhood-list a l)
      ( is-section-map-inv-compute-elementhood-list a l)
      ( is-retraction-map-inv-compute-elementhood-list a l)

  compute-elementhood-list :
    (a : A) (l : list A) → elementhood-list a l ≃ (a ∈-list l)
  pr1 (compute-elementhood-list a l) = map-compute-elementhood-list a l
  pr2 (compute-elementhood-list a l) = is-equiv-map-compute-elementhood-list a l
```

### The type of all elements of a list is equivalent to the standard finite type with the length of the list as its number of elements

Furthermore, there is a commuting triangle

```text
            Fin (length l)
             /          \
            /            \ vec-list l
           ∨              ∨
  type-of-elements l ----> X
                      pr1
```

```agda
module _
  {l1 : Level} {A : UU l1}
  where

  type-of-elements-list : list A → UU l1
  type-of-elements-list l = Σ A (_∈-list l)

  element-type-of-elements-list :
    (l : list A) → type-of-elements-list l → A
  element-type-of-elements-list l = pr1

  cons-type-of-elements-list :
    (x : A) (l : list A) →
    type-of-elements-list l → type-of-elements-list (cons x l)
  cons-type-of-elements-list x l =
    tot (λ z → is-in-tail z x l)

  map-compute-type-of-elements-list :
    (l : list A) → Fin (length-list l) → type-of-elements-list l
  map-compute-type-of-elements-list (cons x l) (inl i) =
    cons-type-of-elements-list x l (map-compute-type-of-elements-list l i)
  map-compute-type-of-elements-list (cons x l) (inr _) =
    (x , is-head x l)

  coherence-square-cons-type-of-elements-list :
    (x : A) (l : list A) →
    coherence-square-maps
      ( map-compute-type-of-elements-list l)
      ( inl-Fin (length-list l))
      ( cons-type-of-elements-list x l)
      ( map-compute-type-of-elements-list (cons x l))
  coherence-square-cons-type-of-elements-list x l a = refl

  map-inv-compute-type-of-elements-list :
    (l : list A) → type-of-elements-list l → Fin (length-list l)
  map-inv-compute-type-of-elements-list (cons x l) (.x , is-head .x .l) =
    inr star
  map-inv-compute-type-of-elements-list (cons x l) (a , is-in-tail .a .x .l H) =
    inl (map-inv-compute-type-of-elements-list l (a , H))

  is-section-map-inv-compute-type-of-elements-list :
    (l : list A) →
    is-section
      ( map-compute-type-of-elements-list l)
      ( map-inv-compute-type-of-elements-list l)
  is-section-map-inv-compute-type-of-elements-list
    ( cons x l)
    ( .x , is-head .x .l) =
    refl
  is-section-map-inv-compute-type-of-elements-list
    ( cons x l)
    ( a , is-in-tail .a .x .l H) =
    ap
      ( cons-type-of-elements-list x l)
      ( is-section-map-inv-compute-type-of-elements-list l (a , H))

  is-retraction-map-inv-compute-type-of-elements-list :
    (l : list A) →
    is-retraction
      ( map-compute-type-of-elements-list l)
      ( map-inv-compute-type-of-elements-list l)
  is-retraction-map-inv-compute-type-of-elements-list (cons x l) (inl i) =
    ap inl (is-retraction-map-inv-compute-type-of-elements-list l i)
  is-retraction-map-inv-compute-type-of-elements-list (cons x l) (inr star) =
    refl

  is-equiv-map-compute-type-of-elements-list :
    (l : list A) → is-equiv (map-compute-type-of-elements-list l)
  is-equiv-map-compute-type-of-elements-list l =
    is-equiv-is-invertible
      ( map-inv-compute-type-of-elements-list l)
      ( is-section-map-inv-compute-type-of-elements-list l)
      ( is-retraction-map-inv-compute-type-of-elements-list l)

  compute-type-of-elements-list :
    (l : list A) → Fin (length-list l) ≃ type-of-elements-list l
  pr1 (compute-type-of-elements-list l) =
    map-compute-type-of-elements-list l
  pr2 (compute-type-of-elements-list l) =
    is-equiv-map-compute-type-of-elements-list l

  triangle-compute-type-of-elements-list :
    (l : list A) →
    coherence-triangle-maps
      {!functional-vec-list l!}
      {!!}
      {!!}
  triangle-compute-type-of-elements-list = {!!}
```