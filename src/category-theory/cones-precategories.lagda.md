# Cones in precategories

```agda
module category-theory.cones-precategories where
```

<details><summary>Imports</summary>

```agda
open import category-theory.composition-operations-on-binary-families-of-sets
open import category-theory.constant-functors
open import category-theory.functors-precategories
open import category-theory.natural-transformations-functors-precategories
open import category-theory.precategories
open import category-theory.precategory-of-functors

open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equality-dependent-pair-types
open import foundation.identity-types
open import foundation.propositions
open import foundation.sets
open import foundation.strictly-involutive-identity-types
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "cone of a functor between precategories" }} `F` is a
[natural transformation](category-theory.natural-transformations-functors-precategories.md)
from a [constant functor](category-theory.constant-functors.md) to `F`.

We call the object that the constant functor takes values at the **vertex** of
the cone. Further, we say it is a "cone _over_ `F`" rather than a "cone _of_
`F`", and it's standard to refer to `F` as a diagram here.

## Definitions

### The type of cones of a functor

```agda
module _
  {l1 l2 l3 l4 : Level} (C : Precategory l1 l2) (D : Precategory l3 l4)
  (F : functor-Precategory C D)
  where

  cone-Precategory : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cone-Precategory =
    Σ ( obj-Precategory D)
      ( λ d →
        natural-transformation-Precategory C D
          ( constant-functor-Precategory C D d)
          ( F))

  vertex-cone-Precategory : cone-Precategory → obj-Precategory D
  vertex-cone-Precategory = pr1

  vertex-functor-cone-Precategory :
    cone-Precategory → functor-Precategory C D
  vertex-functor-cone-Precategory α =
    constant-functor-Precategory C D (vertex-cone-Precategory α)

  natural-transformation-cone-Precategory :
    (α : cone-Precategory) →
    natural-transformation-Precategory C D
      ( vertex-functor-cone-Precategory α)
      ( F)
  natural-transformation-cone-Precategory = pr2

  component-cone-Precategory :
    (α : cone-Precategory) (x : obj-Precategory C) →
    hom-Precategory D
      ( vertex-cone-Precategory α)
      ( obj-functor-Precategory C D F x)
  component-cone-Precategory α =
    hom-family-natural-transformation-Precategory C D
      ( vertex-functor-cone-Precategory α)
      ( F)
      ( natural-transformation-cone-Precategory α)

  naturality-cone-Precategory :
    (α : cone-Precategory) {x y : obj-Precategory C}
    (f : hom-Precategory C x y) →
    comp-hom-Precategory D
      ( hom-functor-Precategory C D F f)
      ( component-cone-Precategory α x) ＝
    component-cone-Precategory α y
  naturality-cone-Precategory α {x} {y} f =
    naturality-natural-transformation-Precategory C D
      ( vertex-functor-cone-Precategory α)
      ( F)
      ( natural-transformation-cone-Precategory α)
      ( f) ∙
    right-unit-law-comp-hom-Precategory D _
```

### The precategory of cones of a functor

```agda
  hom-cone-Precategory : (α β : cone-Precategory) → UU (l1 ⊔ l2 ⊔ l4)
  hom-cone-Precategory α β =
    Σ ( natural-transformation-Precategory C D
        ( vertex-functor-cone-Precategory α)
        ( vertex-functor-cone-Precategory β))
      ( λ γ →
        comp-natural-transformation-Precategory C D
          ( vertex-functor-cone-Precategory α)
          ( vertex-functor-cone-Precategory β)
          ( F)
          ( natural-transformation-cone-Precategory β)
          γ ＝
        ( natural-transformation-cone-Precategory α))

  is-set-hom-cone-Precategory :
    (α β : cone-Precategory) → is-set (hom-cone-Precategory α β)
  is-set-hom-cone-Precategory α β =
    is-set-Σ
      ( is-set-natural-transformation-Precategory C D
        ( vertex-functor-cone-Precategory α)
        ( vertex-functor-cone-Precategory β))
      ( λ τ →
        is-set-is-prop
          ( is-set-natural-transformation-Precategory C D
            ( vertex-functor-cone-Precategory α) F _ _))

  hom-set-cone-Precategory :
    (α β : cone-Precategory) → Set (l1 ⊔ l2 ⊔ l4)
  pr1 (hom-set-cone-Precategory α β) = hom-cone-Precategory α β
  pr2 (hom-set-cone-Precategory α β) = is-set-hom-cone-Precategory α β

  comp-hom-cone-Precategory :
    {α β γ : cone-Precategory} →
    hom-cone-Precategory β γ →
    hom-cone-Precategory α β →
    hom-cone-Precategory α γ
  pr1 (comp-hom-cone-Precategory {α} {β} {γ} φ ψ) =
    comp-natural-transformation-Precategory C D
      ( vertex-functor-cone-Precategory α)
      ( vertex-functor-cone-Precategory β)
      ( vertex-functor-cone-Precategory γ)
      ( pr1 φ)
      ( pr1 ψ)
  pr2 (comp-hom-cone-Precategory {α} {β} {γ} φ ψ) =
    inv
      ( associative-comp-natural-transformation-Precategory C D
        ( vertex-functor-cone-Precategory α)
        ( vertex-functor-cone-Precategory β)
        ( vertex-functor-cone-Precategory γ)
        ( F)
        ( pr1 ψ)
        ( pr1 φ)
        ( natural-transformation-cone-Precategory γ)) ∙
    ap
      ( λ m →
        comp-natural-transformation-Precategory C D
          ( vertex-functor-cone-Precategory α)
          ( vertex-functor-cone-Precategory β)
          ( F)
          ( m)
          ( pr1 ψ))
      ( pr2 φ) ∙
    pr2 ψ

  associative-comp-hom-cone-Precategory :
    {α β γ τ : cone-Precategory} →
    (ξ : hom-cone-Precategory γ τ) →
    (φ : hom-cone-Precategory β γ) →
    (ψ : hom-cone-Precategory α β) →
    comp-hom-cone-Precategory (comp-hom-cone-Precategory ξ φ) ψ ＝
    comp-hom-cone-Precategory ξ (comp-hom-cone-Precategory φ ψ)
  associative-comp-hom-cone-Precategory {α} {β} {γ} {τ} ξ φ ψ =
    eq-pair-Σ
      ( associative-comp-natural-transformation-Precategory C D
        ( vertex-functor-cone-Precategory α)
        ( vertex-functor-cone-Precategory β)
        ( vertex-functor-cone-Precategory γ)
        ( vertex-functor-cone-Precategory τ)
          _ _ _)
      ( eq-is-prop
        ( is-set-natural-transformation-Precategory C D
          ( vertex-functor-cone-Precategory α) F _ _))

  id-hom-cone-Precategory :
    (α : cone-Precategory) → hom-cone-Precategory α α
  pr1 (id-hom-cone-Precategory α) =
    id-natural-transformation-Precategory C D
      ( vertex-functor-cone-Precategory α)
  pr2 (id-hom-cone-Precategory α) =
    right-unit-law-comp-natural-transformation-Precategory C D
      ( vertex-functor-cone-Precategory α)
      ( F)
      ( natural-transformation-cone-Precategory α)

  left-unit-law-comp-hom-cone-Precategory :
    {α β : cone-Precategory}
    (φ : hom-cone-Precategory α β) →
    comp-hom-cone-Precategory (id-hom-cone-Precategory β) φ ＝ φ
  left-unit-law-comp-hom-cone-Precategory {α} {β} φ =
    eq-pair-Σ
      ( left-unit-law-comp-natural-transformation-Precategory C D
          ( vertex-functor-cone-Precategory α)
          ( vertex-functor-cone-Precategory β)
          ( pr1 φ))
      ( eq-is-prop
        ( is-set-natural-transformation-Precategory C D
          ( vertex-functor-cone-Precategory α) F _ _))

  right-unit-law-comp-hom-cone-Precategory :
    {α β : cone-Precategory}
    (φ : hom-cone-Precategory α β) →
    comp-hom-cone-Precategory φ (id-hom-cone-Precategory α) ＝ φ
  right-unit-law-comp-hom-cone-Precategory {α} {β} φ =
    eq-pair-Σ
      ( right-unit-law-comp-natural-transformation-Precategory C D
        ( vertex-functor-cone-Precategory α)
          ( vertex-functor-cone-Precategory β)
          ( pr1 φ))
      ( eq-is-prop
        ( is-set-natural-transformation-Precategory C D
          ( vertex-functor-cone-Precategory α) F _ _))

  cone-precategory-Precategory : Precategory (l1 ⊔ l2 ⊔ l3 ⊔ l4) (l1 ⊔ l2 ⊔ l4)
  cone-precategory-Precategory =
    make-Precategory
      cone-Precategory
      hom-set-cone-Precategory
      comp-hom-cone-Precategory
      id-hom-cone-Precategory
      associative-comp-hom-cone-Precategory
      left-unit-law-comp-hom-cone-Precategory
      right-unit-law-comp-hom-cone-Precategory
```
