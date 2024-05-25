# Lists subtypes

```agda
module lists.lists-subtypes where
```

<details><summary>Imports</summary>

```agda
open import foundation.decidable-types
open import foundation.dependent-pair-types
open import foundation.disjunction
open import foundation.existential-quantification
open import foundation.inhabited-subtypes
open import foundation.intersections-subtypes
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.unions-subtypes
open import foundation.universe-levels

open import foundation-core.cartesian-product-types
open import foundation-core.coproduct-types
open import foundation-core.empty-types
open import foundation-core.function-types
open import foundation-core.negation
open import foundation-core.propositions
open import foundation-core.sets
open import foundation-core.subtypes

open import lists.concatenation-lists
open import lists.lists
open import lists.reversing-lists
```

</details>

## Idea

TODO

## Definition

```agda
module _
  {l : Level} {A : UU l}
  where

  list-subtype : list A → subtype l A
  list-subtype l a = trunc-Prop (a ∈-list l)

  not-in-list-nil : {a : A} → ¬ (is-in-subtype (list-subtype nil) a)
  not-in-list-nil = map-universal-property-trunc-Prop empty-Prop (λ ())

  subset-list-subtype-nil :
    {l2 : Level} (S : subtype l2 A) → list-subtype nil ⊆ S
  subset-list-subtype-nil S _ = ex-falso ∘ not-in-list-nil

  in-list-subtype-in-list :
    {a : A} {l : list A} → a ∈-list l → is-in-subtype (list-subtype l) a
  in-list-subtype-in-list = unit-trunc-Prop

  subset-tail-list-subtype :
    {a : A} {l : list A} → list-subtype l ⊆ list-subtype (cons a l)
  subset-tail-list-subtype {a} {l} x =
    map-universal-property-trunc-Prop
      ( list-subtype (cons a l) x)
      ( in-list-subtype-in-list ∘ is-in-tail x a l)

  head-in-list-subtype :
    {a : A} {l : list A} → is-in-subtype (list-subtype (cons a l)) a
  head-in-list-subtype {a} {l} = in-list-subtype-in-list (is-head a l)

  is-decidable-is-inhabited-list-subtype :
    (l : list A) → is-decidable (is-inhabited-subtype (list-subtype l))
  is-decidable-is-inhabited-list-subtype nil =
    inr
      ( map-universal-property-trunc-Prop
        ( empty-Prop)
        ( λ (x , in-list) → not-in-list-nil in-list))
  is-decidable-is-inhabited-list-subtype (cons x xs) =
    inl (unit-trunc-Prop (x , head-in-list-subtype))

  subset-list-subtype-cons :
    {a : A} {l : list A} →
    {l2 : Level} (S : subtype l2 A) →
    is-in-subtype S a →
    list-subtype l ⊆ S →
    list-subtype (cons a l) ⊆ S
  subset-list-subtype-cons {a} {l} S a-in-S l-sub-S x =
    map-universal-property-trunc-Prop
      ( S x)
      ( λ where
        (is-head .x .l) → a-in-S
        (is-in-tail .x .a .l t) → l-sub-S x (in-list-subtype-in-list t))

  subset-list-subtype-reverse-list :
    (l : list A) → list-subtype l ⊆ list-subtype (reverse-list l)
  subset-list-subtype-reverse-list l x =
    map-universal-property-trunc-Prop
      ( list-subtype (reverse-list l) x)
      ( in-list-subtype-in-list ∘ forward-contains-reverse-list x l)

  subset-list-subtype-concat-union :
    {l1 l2 : list A} →
    list-subtype (concat-list l1 l2) ⊆ list-subtype l1 ∪ list-subtype l2
  subset-list-subtype-concat-union {nil} {l2} =
    subtype-union-right (list-subtype nil) (list-subtype l2)
  subset-list-subtype-concat-union {cons x l1} {l2} =
    subset-list-subtype-cons
      ( list-subtype (cons x l1) ∪ list-subtype l2)
      ( subtype-union-left (list-subtype (cons x l1)) (list-subtype l2) x
        ( head-in-list-subtype))
      ( transitive-leq-subtype
        ( list-subtype (concat-list l1 l2))
        ( list-subtype l1 ∪ list-subtype l2)
        ( list-subtype (cons x l1) ∪ list-subtype l2)
        ( subset-union-subset-left
          ( list-subtype l1)
          ( list-subtype (cons x l1))
          ( list-subtype l2)
          ( subset-tail-list-subtype))
        ( subset-list-subtype-concat-union))

  subset-list-subset-concat-left :
    (l1 l2 : list A) →
    list-subtype l1 ⊆ list-subtype (concat-list l1 l2)
  subset-list-subset-concat-left l1 l2 x =
    map-universal-property-trunc-Prop
      ( list-subtype (concat-list l1 l2) x)
      ( in-list-subtype-in-list ∘ in-concat-left l1 l2)

  subset-list-subset-concat-right :
    (l1 l2 : list A) →
    list-subtype l2 ⊆ list-subtype (concat-list l1 l2)
  subset-list-subset-concat-right l1 l2 x =
    map-universal-property-trunc-Prop
      ( list-subtype (concat-list l1 l2) x)
      ( in-list-subtype-in-list ∘ in-concat-right l1 l2)

  subset-list-subtype-union-concat :
    {l1 l2 : list A} →
    list-subtype l1 ∪ list-subtype l2 ⊆ list-subtype (concat-list l1 l2)
  subset-list-subtype-union-concat {l1} {l2} =
    subtype-union-both
      ( list-subtype l1)
      ( list-subtype l2)
      ( list-subtype (concat-list l1 l2))
      ( subset-list-subset-concat-left l1 l2)
      ( subset-list-subset-concat-right l1 l2)

  iff-subset-head-tail :
    {l2 : Level} (x : A) (l : list A) (a : subtype l2 A) →
    (list-subtype (cons x l) ⊆ a) ↔ is-in-subtype a x × (list-subtype l ⊆ a)
  pr1 (pr1 (iff-subset-head-tail x l a) leq) =
    leq x head-in-list-subtype
  pr2 (pr1 (iff-subset-head-tail x l a) leq) =
    transitive-leq-subtype (list-subtype l) (list-subtype (cons x l)) a
      ( leq)
      ( subset-tail-list-subtype)
  pr2 (iff-subset-head-tail x xs a) (x-in-a , leq) =
    subset-list-subtype-cons a x-in-a leq

  lists-in-union-lists :
    {l2 l3 : Level}
    (xs : list A) (a : subtype l2 A) (b : subtype l3 A) →
    list-subtype xs ⊆ union-subtype a b →
    exists-structure ( list A × list A)
      ( λ (xsl , xsr) →
        ( list-subtype xs ⊆ list-subtype xsl ∪ list-subtype xsr) ×
        ( list-subtype xsl ⊆ a) ×
        ( list-subtype xsr ⊆ b))
  lists-in-union-lists nil a b sub =
    intro-exists (nil , nil)
      ( triple
        ( subset-list-subtype-nil (list-subtype nil ∪ list-subtype nil))
        ( subset-list-subtype-nil a)
        ( subset-list-subtype-nil b))
  lists-in-union-lists (cons x xs) a b leq =
    apply-universal-property-trunc-Prop
      ( lists-in-union-lists xs a b
        ( transitive-leq-subtype
          ( list-subtype xs)
          ( list-subtype (cons x xs))
          ( union-subtype a b)
          ( leq)
          ( subset-tail-list-subtype)))
      ( exists-structure-Prop _ _)
      ( λ ((xsl , xsr) , leq-lists , leq-xsl , leq-xsr) →
        ( elim-disjunction (exists-structure-Prop _ _)
          ( λ x-in-a →
            ( intro-exists (cons x xsl , xsr)
              ( triple
                ( subset-list-subtype-cons
                  ( list-subtype (cons x xsl) ∪ list-subtype xsr)
                  ( subtype-union-left
                    ( list-subtype (cons x xsl))
                    ( list-subtype xsr)
                    ( x)
                    ( head-in-list-subtype))
                  ( transitive-leq-subtype
                    ( list-subtype xs)
                    ( list-subtype xsl ∪ list-subtype xsr)
                    ( list-subtype (cons x xsl) ∪ list-subtype xsr)
                    ( subset-union-subset-left
                      ( list-subtype xsl)
                      ( list-subtype (cons x xsl))
                      ( list-subtype xsr)
                      ( subset-tail-list-subtype))
                    ( leq-lists)))
                ( backward-implication (iff-subset-head-tail x xsl a)
                  ( x-in-a , leq-xsl))
                ( leq-xsr))))
          ( λ x-in-b →
            ( intro-exists (xsl , cons x xsr)
              ( triple
                ( subset-list-subtype-cons
                  ( list-subtype xsl ∪ list-subtype (cons x xsr))
                  ( subtype-union-right
                    ( list-subtype xsl)
                    ( list-subtype (cons x xsr))
                    ( x)
                    ( head-in-list-subtype))
                  ( transitive-leq-subtype
                    ( list-subtype xs)
                    ( list-subtype xsl ∪ list-subtype xsr)
                    ( list-subtype xsl ∪ list-subtype (cons x xsr))
                    ( subset-union-subset-right
                      ( list-subtype xsl)
                      ( list-subtype xsr)
                      ( list-subtype (cons x xsr))
                      ( subset-tail-list-subtype))
                    ( leq-lists)))
                ( leq-xsl)
                ( backward-implication (iff-subset-head-tail x xsr b)
                  ( x-in-b , leq-xsr)))))
          ( leq x head-in-list-subtype)))
```
