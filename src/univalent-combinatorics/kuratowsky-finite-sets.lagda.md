# Kuratowsky finite sets

```agda
module univalent-combinatorics.kuratowsky-finite-sets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.decidable-equality
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.functoriality-propositional-truncation
open import foundation.law-of-excluded-middle
open import foundation.logical-equivalences
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.sets
open import foundation.subtypes
open import foundation.surjective-maps
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.transport-along-identifications

open import lists.functoriality-lists
open import lists.lists
open import lists.lists-subtypes

open import univalent-combinatorics.equality-finite-types
open import univalent-combinatorics.finite-types
open import univalent-combinatorics.image-of-maps
open import univalent-combinatorics.standard-finite-types
```

</details>

## Idea

A Kuratowsky finite type is a set `X` for which there exists a surjection into
`X` from a standard finite type. In other words, the Kuratowsky finite types are
the set-quotient of a standard finite type.

## Definition

```agda
is-kuratowsky-finite-set-Prop : {l : Level} → Set l → Prop l
is-kuratowsky-finite-set-Prop X =
  exists-structure-Prop ℕ (λ n → Fin n ↠ type-Set X)

is-kuratowsky-finite-set : {l : Level} → Set l → UU l
is-kuratowsky-finite-set X = type-Prop (is-kuratowsky-finite-set-Prop X)

𝔽-Kuratowsky : (l : Level) → UU (lsuc l)
𝔽-Kuratowsky l = Σ (Set l) is-kuratowsky-finite-set

module _
  {l : Level} (X : 𝔽-Kuratowsky l)
  where

  set-𝔽-Kuratowsky : Set l
  set-𝔽-Kuratowsky = pr1 X

  type-𝔽-Kuratowsky : UU l
  type-𝔽-Kuratowsky = type-Set set-𝔽-Kuratowsky

  is-set-type-𝔽-Kuratowsky : is-set type-𝔽-Kuratowsky
  is-set-type-𝔽-Kuratowsky = is-set-type-Set set-𝔽-Kuratowsky

  is-kuratowsky-finite-set-𝔽-Kuratowsky :
    is-kuratowsky-finite-set set-𝔽-Kuratowsky
  is-kuratowsky-finite-set-𝔽-Kuratowsky = pr2 X
```

## Second definition

```agda
is-kuratowsky-finite-set-list-Prop : {l : Level} → Set l → Prop l
is-kuratowsky-finite-set-list-Prop X =
  exists-structure-Prop (list (type-Set X))
    ( λ l → (x : type-Set X) → is-in-subtype (list-subtype l) x)

is-kuratowsky-finite-set-list : {l : Level} → Set l → UU l
is-kuratowsky-finite-set-list X =
  type-Prop (is-kuratowsky-finite-set-list-Prop X)

is-kuratowsky-finite-set-is-kuratowsky-finite-set-list :
  {l : Level} (X : Set l) →
  is-kuratowsky-finite-set-list X → is-kuratowsky-finite-set X
is-kuratowsky-finite-set-is-kuratowsky-finite-set-list X =
  elim-exists
    ( is-kuratowsky-finite-set-Prop X)
    ( λ l all-list-subtype →
      intro-exists (length-list l)
        ( pair
          ( component-list l)
          ( λ x →
            map-trunc-Prop
              ( λ in-list →
                pair
                  ( index-in-list x l in-list)
                  ( inv (eq-component-list-index-in-list x l in-list)))
              ( all-list-subtype x))))

-- TODO: prove another implication
```

### Kuratowky finite subsets

```agda
is-kuratowsky-finite-subset :
  {l1 l2 : Level} (A : Set l1) (B : subtype l2 (type-Set A))
  (l : list (type-Set A)) →
  equiv-subtypes B (list-subtype l) →
  is-kuratowsky-finite-set (set-subset A B)
is-kuratowsky-finite-subset A B l e =
  is-kuratowsky-finite-set-is-kuratowsky-finite-set-list
    ( set-subset A B)
    ( intro-exists l'
      ( λ (a , in-B) →
        map-trunc-Prop
          ( λ a-in-l →
            tr
              ( λ i → (a , i) ∈-list l')
              ( eq-is-prop (is-prop-type-Prop (B a)))
              ( in-dependent-map-list _ a-in-l))
          ( map-equiv (e a) in-B)))
  where
  l' : list (type-subtype B)
  l' =
    dependent-map-list l
      ( λ a in-list →
        a , map-section-map-equiv (e a) (in-list-subtype-in-list in-list))
```

### List subtype is Kuratowky finite

```agda
is-kuratowski-finite-list-subtype :
  {l1 : Level} (A : Set l1) (l : list (type-Set A)) →
  is-kuratowsky-finite-set (set-subset A (list-subtype l))
is-kuratowski-finite-list-subtype A l =
  is-kuratowsky-finite-subset A (list-subtype l) l
    ( id-equiv-subtypes (list-subtype l))
```

## Properties

### A Kuratowsky finite set is finite if and only if it has decidable equality

```agda
is-finite-has-decidable-equality-type-𝔽-Kuratowsky :
  {l : Level} (X : 𝔽-Kuratowsky l) →
  has-decidable-equality (type-𝔽-Kuratowsky X) →
  is-finite (type-𝔽-Kuratowsky X)
is-finite-has-decidable-equality-type-𝔽-Kuratowsky X H =
  apply-universal-property-trunc-Prop
    ( is-kuratowsky-finite-set-𝔽-Kuratowsky X)
    ( is-finite-Prop (type-𝔽-Kuratowsky X))
    ( λ (n , f , s) → is-finite-codomain (is-finite-Fin n) s H)

has-decidable-equality-is-finite-type-𝔽-Kuratowsky :
  {l : Level} (X : 𝔽-Kuratowsky l) →
  is-finite (type-𝔽-Kuratowsky X) →
  has-decidable-equality (type-𝔽-Kuratowsky X)
has-decidable-equality-is-finite-type-𝔽-Kuratowsky X H =
  has-decidable-equality-is-finite H
```

### Kuratowsky finite sets are closed under surjections

```agda
is-kuratowsky-finite-set-surjection :
  {l1 l2 : Level} (X : Set l1) (Y : Set l2) →
  type-Set X ↠ type-Set Y →
  is-kuratowsky-finite-set X →
  is-kuratowsky-finite-set Y
is-kuratowsky-finite-set-surjection X Y f =
  elim-exists
    ( is-kuratowsky-finite-set-Prop Y)
    ( λ n g → intro-exists n (surjection-comp f g))
```

### Any finite set is Kuratowsky finite

```agda
is-kuratowsky-finite-set-is-finite :
  {l : Level} (X : Set l) →
  is-finite (type-Set X) →
  is-kuratowsky-finite-set X
is-kuratowsky-finite-set-is-finite X =
  elim-exists
    ( is-kuratowsky-finite-set-Prop X)
    ( λ n e → intro-exists n (map-equiv e , is-surjective-map-equiv e))
```

### Classical facts

```agda
is-finite-is-kuratowsky-finite-set :
  {l : Level} (X : Set l) →
  LEM l →
  is-kuratowsky-finite-set X → is-finite (type-Set X)
is-finite-is-kuratowsky-finite-set X lem is-fin =
  is-finite-has-decidable-equality-type-𝔽-Kuratowsky
    ( X , is-fin)
    ( λ x y → lem (Id-Prop X x y))
```
