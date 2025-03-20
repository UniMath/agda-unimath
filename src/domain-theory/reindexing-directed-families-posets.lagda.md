# Reindexing directed families in posets

```agda
open import foundation.function-extensionality-axiom

module
  domain-theory.reindexing-directed-families-posets
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import domain-theory.directed-families-posets funext

open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types funext
open import foundation.conjunction funext
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.existential-quantification funext
open import foundation.function-types funext
open import foundation.identity-types funext
open import foundation.inhabited-types funext
open import foundation.propositional-truncations funext
open import foundation.propositions funext
open import foundation.surjective-maps funext
open import foundation.universal-quantification funext
open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets funext
open import order-theory.posets funext
```

</details>

## Idea

Given a [directed family](domain-theory.directed-families-posets.md) `x : J → P`
in a [poset](order-theory.posets.md) `P` and a
[surjection](foundation.surjective-maps.md) `f : I ↠ J`, then we can
{{#concept "reindex" Disambiguation="directed family in a poset" Agda=reindex-directed-family-Poset}}
the directed family `x` by `f` to obtain another directed family
`x ∘ f : I → P`. The requirement that `f` is surjective guarantees that
[upper bounds](order-theory.upper-bounds-posets.md) in `x` also
[exist](foundation.existential-quantification.md) in `x ∘ f`.

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
