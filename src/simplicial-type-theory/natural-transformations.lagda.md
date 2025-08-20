# Natural transformations

```agda
open import foundation.universe-levels
open import order-theory.nontrivial-bounded-total-orders

module
  simplicial-type-theory.natural-transformations
  {I1 I2 : Level} (I : Nontrivial-Bounded-Total-Order I1 I2)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.equality-cartesian-product-types
open import foundation.equality-dependent-function-types
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-cartesian-product-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.torsorial-type-families
open import foundation.type-arithmetic-dependent-function-types
open import foundation.type-theoretic-principle-of-choice
open import foundation.universe-levels

open import orthogonal-factorization-systems.extensions-maps

open import simplicial-type-theory.action-on-directed-edges-functions I
open import simplicial-type-theory.arrows I
open import simplicial-type-theory.directed-edges I
open import simplicial-type-theory.directed-interval I
```

</details>

## Idea

Given two [dependent functions](foundation.dependent-function-types.md)
`f g : (x : A) → B x`, a
{{#concept "natural transformation" Disambiguation="in simplicial type theory" Agda=natural-transformation▵}}
`α` from `f` to `g` is a family of
[directed edges](simplicial-type-theory.directed-edges.md)

```text
  α : (x : A) → (f x →▵ g x).
```

Naturality follows automatically from the fact that every section is natural in
the base. I.e., for every edge `x →▵ y` in `A`, we have a dependent edge
`α x →▵ α y` over it, giving us a dependent commuting square of
[simplicial arrows](simplicial-type-theory.arrows.md)

```text
           α x
     f x ------> g x
      |           |
  f p |    α p    | g p
      ∨           ∨
     f y ------> g y.
           α y
```

## Definitions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  _⇒▵_ : ((x : A) → B x) → ((x : A) → B x) → UU (I1 ⊔ l1 ⊔ l2)
  f ⇒▵ g = ((x : A) → (f x →▵ g x))

  infix 7 _⇒▵_

  natural-transformation▵ :
    ((x : A) → B x) → ((x : A) → B x) → UU (I1 ⊔ l1 ⊔ l2)
  natural-transformation▵ = _⇒▵_

module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x} (α : f ⇒▵ g)
  where

  family-of-arrows-natural-transformation▵ : (x : A) → arrow▵ (B x)
  family-of-arrows-natural-transformation▵ x = arrow-hom▵ (α x)

  arrow-natural-transformation▵ : arrow▵ ((x : A) → B x)
  arrow-natural-transformation▵ t x = arrow-hom▵ (α x) t

  eq-source-natural-transformation▵ :
    (x : A) → family-of-arrows-natural-transformation▵ x 0▵ ＝ f x
  eq-source-natural-transformation▵ x = eq-source-hom▵ (α x)

  eq-target-natural-transformation▵ :
    (x : A) → family-of-arrows-natural-transformation▵ x 1▵ ＝ g x
  eq-target-natural-transformation▵ x = eq-target-hom▵ (α x)
```

## Properties

### Families of arrows are arrows of dependent functions

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → Δ¹ → UU l2}
  where

  family-of-arrows-arrow-of-dependent-functions▵ :
    arrow▵' (λ t → (x : A) → B x t) → (x : A) → arrow▵' (B x)
  family-of-arrows-arrow-of-dependent-functions▵ = swap-Π

  arrow-of-dependent-functions-family-of-arrows▵ :
    ((x : A) → arrow▵' (B x)) → arrow▵' (λ t → (x : A) → B x t)
  arrow-of-dependent-functions-family-of-arrows▵ = swap-Π

  equiv-family-of-arrows-arrow-of-dependent-functions▵ :
    (arrow▵' (λ t → (x : A) → B x t)) ≃ ((x : A) → arrow▵' (B x))
  equiv-family-of-arrows-arrow-of-dependent-functions▵ =
    equiv-swap-Π
```

### Extensionality for natural transformations

A natural transformation between functions `f` and `g` is the same as a directed
edge from `f` to `g`.

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  where

  natural-transformation▵-hom▵-Π : (f →▵ g) → (f ⇒▵ g)
  natural-transformation▵-hom▵-Π
    ( α , p , q) x =
    ( ( λ t → α t x) , htpy-eq p x , htpy-eq q x)

  hom▵-Π-natural-transformation▵ : (f ⇒▵ g) → (f →▵ g)
  hom▵-Π-natural-transformation▵ α =
    ( arrow-natural-transformation▵ α ,
      eq-htpy (pr1 ∘ pr2 ∘ α) ,
      eq-htpy (pr2 ∘ pr2 ∘ α))

  is-section-hom▵-Π-natural-transformation▵ :
    is-section natural-transformation▵-hom▵-Π hom▵-Π-natural-transformation▵
  is-section-hom▵-Π-natural-transformation▵ α =
    eq-htpy
      ( λ x →
        eq-pair-eq-fiber
          ( eq-pair
            ( htpy-eq (is-section-eq-htpy (pr1 ∘ pr2 ∘ α)) x)
            ( htpy-eq (is-section-eq-htpy (pr2 ∘ pr2 ∘ α)) x)))

  is-retraction-hom▵-Π-natural-transformation▵ :
    is-retraction natural-transformation▵-hom▵-Π hom▵-Π-natural-transformation▵
  is-retraction-hom▵-Π-natural-transformation▵ (α , p , q) =
    eq-pair-eq-fiber
      ( eq-pair (is-retraction-eq-htpy p) (is-retraction-eq-htpy q))

  is-equiv-natural-transformation▵-hom▵-Π :
    is-equiv natural-transformation▵-hom▵-Π
  is-equiv-natural-transformation▵-hom▵-Π =
    is-equiv-is-invertible
      ( hom▵-Π-natural-transformation▵)
      ( is-section-hom▵-Π-natural-transformation▵)
      ( is-retraction-hom▵-Π-natural-transformation▵)

  extensionality-natural-transformation▵ : (f →▵ g) ≃ (f ⇒▵ g)
  extensionality-natural-transformation▵ =
    ( natural-transformation▵-hom▵-Π ,
      is-equiv-natural-transformation▵-hom▵-Π)
```

### Characterizing equality of natural transformations

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {f g : (x : A) → B x}
  where

  htpy-natural-transformation▵ : (α β : f ⇒▵ g) → UU (I1 ⊔ l1 ⊔ l2)
  htpy-natural-transformation▵ α β = ((x : A) → htpy-hom▵ (α x) (β x))

  refl-htpy-natural-transformation▵ :
    (α : f ⇒▵ g) → htpy-natural-transformation▵ α α
  refl-htpy-natural-transformation▵ α x = refl-htpy-hom▵ (α x)

  htpy-eq-natural-transformation▵ :
    (α β : f ⇒▵ g) → α ＝ β → htpy-natural-transformation▵ α β
  htpy-eq-natural-transformation▵ α .α refl =
    refl-htpy-natural-transformation▵ α

  abstract
    is-torsorial-htpy-natural-transformation▵ :
      (α : f ⇒▵ g) → is-torsorial (htpy-natural-transformation▵ α)
    is-torsorial-htpy-natural-transformation▵ α =
      is-torsorial-Eq-Π (is-torsorial-htpy-hom▵ ∘ α)

  is-equiv-htpy-eq-natural-transformation▵ :
    (α β : f ⇒▵ g) → is-equiv (htpy-eq-natural-transformation▵ α β)
  is-equiv-htpy-eq-natural-transformation▵ α =
    fundamental-theorem-id
      ( is-torsorial-htpy-natural-transformation▵ α)
      ( htpy-eq-natural-transformation▵ α)

  equiv-htpy-eq-natural-transformation▵ :
    (α β : f ⇒▵ g) → (α ＝ β) ≃ (htpy-natural-transformation▵ α β)
  equiv-htpy-eq-natural-transformation▵ α β =
    ( htpy-eq-natural-transformation▵ α β ,
      is-equiv-htpy-eq-natural-transformation▵ α β)

  eq-htpy-natural-transformation▵ :
    (α β : f ⇒▵ g) → htpy-natural-transformation▵ α β → α ＝ β
  eq-htpy-natural-transformation▵ α β =
    map-inv-equiv (equiv-htpy-eq-natural-transformation▵ α β)
```

## The identity natural transformation

```agda
id-natural-transformation▵ :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} (f : (x : A) → B x) → (f ⇒▵ f)
id-natural-transformation▵ f x = id-hom▵ (f x)
```
