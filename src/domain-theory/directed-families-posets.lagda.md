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

A
{{#concept "directed family of elements" WD="upward directed set" WDID=Q1513048 Agda=directed-family-Poset}}
in a [poset](order-theory.posets.md) `P` consists of an
[inhabited type](foundation.inhabited-types.md) `I` and a map `x : I → P` such
that for any two elements `i j : I` there
[exists](foundation.existential-quantification.md) an element `k : I` such that
both `x i ≤ x k` and `x j ≤ x k` hold.

## Definitions

### The predicate on a family of elements in a poset of being directed

```agda
is-directed-prop-family-Poset :
  {l1 l2 l3 : Level} (P : Poset l1 l2) (I : Inhabited-Type l3)
  (x : type-Inhabited-Type I → type-Poset P) → Prop (l2 ⊔ l3)
is-directed-prop-family-Poset P I x =
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
is-directed-family-Poset P I x = type-Prop (is-directed-prop-family-Poset P I x)
```

### The type of directed families of elements in a poset

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

### The action of order preserving maps on directed families

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  (P : Poset l1 l2) (Q : Poset l3 l4)
  (f : hom-Poset P Q)
  (x : directed-family-Poset l5 P)
  where

  type-directed-family-hom-Poset : UU l5
  type-directed-family-hom-Poset = type-directed-family-Poset P x

  is-inhabited-type-directed-family-hom-Poset :
    is-inhabited type-directed-family-hom-Poset
  is-inhabited-type-directed-family-hom-Poset =
    is-inhabited-type-directed-family-Poset P x

  inhabited-type-directed-family-hom-Poset : Inhabited-Type l5
  inhabited-type-directed-family-hom-Poset =
    type-directed-family-hom-Poset ,
    is-inhabited-type-directed-family-hom-Poset

  family-directed-family-hom-Poset :
    type-directed-family-hom-Poset → type-Poset Q
  family-directed-family-hom-Poset =
    map-hom-Poset P Q f ∘ family-directed-family-Poset P x

  abstract
    is-directed-family-directed-family-hom-Poset :
      is-directed-family-Poset Q
        inhabited-type-directed-family-hom-Poset
        family-directed-family-hom-Poset
    is-directed-family-directed-family-hom-Poset u v =
      elim-exists
        ( exists-structure-Prop type-directed-family-hom-Poset _)
        ( λ z y →
          intro-exists z
            ( preserves-order-hom-Poset P Q f
                ( family-directed-family-Poset P x u)
                ( family-directed-family-Poset P x z)
                ( pr1 y) ,
              preserves-order-hom-Poset P Q f
                ( family-directed-family-Poset P x v)
                ( family-directed-family-Poset P x z)
                ( pr2 y)))
        ( is-directed-family-directed-family-Poset P x u v)

  directed-family-hom-Poset : directed-family-Poset l5 Q
  directed-family-hom-Poset =
    inhabited-type-directed-family-hom-Poset ,
    family-directed-family-hom-Poset ,
    is-directed-family-directed-family-hom-Poset
```
