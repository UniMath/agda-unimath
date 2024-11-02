# Directed families in posets

```agda
module domain-theory.directed-families-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.function-types
open import foundation.identity-types
open import foundation.inhabited-types
open import foundation.propositional-truncations
open import foundation.propositions
open import foundation.surjective-maps
open import foundation.universal-quantification
open import foundation.universe-levels

open import order-theory.posets
```

</details>

## Idea

A
{{#concept "directed family of elements" WD="upward directed set" WDID=Q1513048 Agda=directed-family-Poset}}
in a [poset](order-theory.posets.md) `P` consists of an
[inhabited type](foundation.inhabited-types.md) `I` and a map `x : I → P` such
that for any two elements `i j : I` there
[exists](foundaiton.existential-quantification.md) an element `k : I` such that
both `x i ≤ x k` and `x j ≤ x k` hold.

## Definitions

### The predicate on a family of being directed

```agda
is-directed-family-Poset-Prop :
  {l1 l2 l3 : Level} (P : Poset l1 l2) (I : Inhabited-Type l3)
  (x : type-Inhabited-Type I → type-Poset P) → Prop (l2 ⊔ l3)
is-directed-family-Poset-Prop P I x =
  ∀'
    ( type-Inhabited-Type I)
    ( λ i →
      ∀'
        ( type-Inhabited-Type I)
        ( λ j →
          ∃ ( type-Inhabited-Type I)
            ( λ k →
              leq-prop-Poset P (x i) (x k) ∧ leq-prop-Poset P (x j) (x k))))

is-directed-family-Poset :
  {l1 l2 l3 : Level} (P : Poset l1 l2) (I : Inhabited-Type l3)
  (α : type-Inhabited-Type I → type-Poset P) → UU (l2 ⊔ l3)
is-directed-family-Poset P I x = type-Prop (is-directed-family-Poset-Prop P I x)
```

### The type of directed families in a poset

```agda
directed-family-Poset :
  {l1 l2 : Level} (l3 : Level) → Poset l1 l2 → UU (l1 ⊔ l2 ⊔ lsuc l3)
directed-family-Poset l3 P =
  Σ ( Inhabited-Type l3)
    ( λ I →
      Σ ( type-Inhabited-Type I → type-Poset P)
        ( is-directed-family-Poset P I))

module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) (x : directed-family-Poset l3 P)
  where

  inhabited-type-directed-family-Poset : Inhabited-Type l3
  inhabited-type-directed-family-Poset = pr1 x

  type-directed-family-Poset : UU l3
  type-directed-family-Poset =
    type-Inhabited-Type inhabited-type-directed-family-Poset

  is-inhabited-type-directed-family-Poset :
    is-inhabited type-directed-family-Poset
  is-inhabited-type-directed-family-Poset =
    is-inhabited-type-Inhabited-Type inhabited-type-directed-family-Poset

  family-directed-family-Poset : type-directed-family-Poset → type-Poset P
  family-directed-family-Poset = pr1 (pr2 x)

  is-directed-family-directed-family-Poset :
    is-directed-family-Poset P
      ( inhabited-type-directed-family-Poset)
      ( family-directed-family-Poset)
  is-directed-family-directed-family-Poset = pr2 (pr2 x)
```

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
    is-inhabited-surjects-onto f (is-inhabited-type-directed-family-Poset P x)

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
        (λ z y →
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
