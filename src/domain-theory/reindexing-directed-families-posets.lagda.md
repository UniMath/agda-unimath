# Reindexing directed families in posets

```agda
module domain-theory.reindexing-directed-families-posets where
```

<details><summary>Imports</summary>

```agda
open import domain-theory.directed-families-posets

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.surjective-maps
open import foundation.universal-quantification
open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea

TODO

## Definitions

### Reindexing directed families in a poset

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (x : directed-family-Poset l3 P)
  {I : UU l4} (f : I ↠ type-directed-family-Poset P x)
  where

  type-reindex-directed-family-Poset : UU l4
  type-reindex-directed-family-Poset = I

  is-inhabited-type-reindex-directed-family-Poset :
    is-inhabited type-reindex-directed-family-Poset
  is-inhabited-type-reindex-directed-family-Poset =
    is-inhabited-surjection f (is-inhabited-type-directed-family-Poset P x)

  inhabited-type-reindex-directed-family-Poset : Inhabited-Type l4
  inhabited-type-reindex-directed-family-Poset =
    type-reindex-directed-family-Poset ,
    is-inhabited-type-reindex-directed-family-Poset

  family-reindex-directed-family-Poset :
    type-reindex-directed-family-Poset → type-Poset P
  family-reindex-directed-family-Poset =
    family-directed-family-Poset P x ∘ map-surjection f

  abstract
    is-directed-family-reindex-directed-family-Poset :
      is-directed-family-Poset P
        inhabited-type-reindex-directed-family-Poset
        family-reindex-directed-family-Poset
    is-directed-family-reindex-directed-family-Poset u v =
      elim-exists
        ( exists-structure-Prop type-reindex-directed-family-Poset _)
        ( λ z y →
          rec-trunc-Prop
            ( exists-structure-Prop type-reindex-directed-family-Poset _)
            ( λ p →
              intro-exists
                ( pr1 p)
                ( concatenate-leq-eq-Poset P
                    ( pr1 y)
                    ( ap (family-directed-family-Poset P x) (inv (pr2 p))) ,
                  concatenate-leq-eq-Poset P
                    ( pr2 y)
                    ( ap (family-directed-family-Poset P x) (inv (pr2 p)))))
            ( is-surjective-map-surjection f z))
        ( is-directed-family-directed-family-Poset P x
          ( map-surjection f u)
          ( map-surjection f v))

  reindex-directed-family-Poset : directed-family-Poset l4 P
  reindex-directed-family-Poset =
    inhabited-type-reindex-directed-family-Poset ,
    family-reindex-directed-family-Poset ,
    is-directed-family-reindex-directed-family-Poset
```

### Reindexing directed families in a poset by an equivalence

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (x : directed-family-Poset l3 P)
  {I : UU l4}
  where

  reindex-equiv-directed-family-Poset :
    I ≃ type-directed-family-Poset P x → directed-family-Poset l4 P
  reindex-equiv-directed-family-Poset f =
    reindex-directed-family-Poset P x (surjection-equiv f)

  reindex-inv-equiv-directed-family-Poset :
    type-directed-family-Poset P x ≃ I → directed-family-Poset l4 P
  reindex-inv-equiv-directed-family-Poset f =
    reindex-directed-family-Poset P x (surjection-inv-equiv f)
```
