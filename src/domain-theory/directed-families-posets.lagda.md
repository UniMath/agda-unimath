# Directed families in posets

```agda
module domain-theory.directed-families-posets where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.conjunction
open import foundation.dependent-pair-types
open import foundation.existential-quantification
open import foundation.inhabited-types
open import foundation.propositions
open import foundation.universal-quantification
open import foundation.universe-levels

open import order-theory.posets
```

</details>

## Idea

A **directed family of elements** in a poset `P` consists of an inhabited type
`I` and a map `x : I → P` such that for any two elements `i j : I` there exists
an element `k : I` such that both `x i ≤ x k` and `x j ≤ x k` hold.

## Definition

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
              leq-Poset-Prop P (x i) (x k) ∧ leq-Poset-Prop P (x j) (x k))))

is-directed-family-Poset :
  {l1 l2 l3 : Level} (P : Poset l1 l2) (I : Inhabited-Type l3)
  (α : type-Inhabited-Type I → type-Poset P) → UU (l2 ⊔ l3)
is-directed-family-Poset P I x = type-Prop (is-directed-family-Poset-Prop P I x)

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
