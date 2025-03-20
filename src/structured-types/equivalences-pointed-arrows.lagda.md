# Equivalences of pointed arrows

```agda
open import foundation.function-extensionality-axiom

module
  structured-types.equivalences-pointed-arrows
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences funext
open import foundation.equivalences funext-arrows
open import foundation.function-types funext
open import foundation.identity-types funext
open import foundation.universe-levels

open import structured-types.commuting-squares-of-pointed-maps funext
open import structured-types.pointed-equivalences funext
open import structured-types.pointed-homotopies funext
open import structured-types.pointed-maps funext
open import structured-types.pointed-types
```

</details>

## Idea

An {{#concept "equivalence of pointed arrows" Agda=equiv-pointed-arrow}} from a
[pointed map](structured-types.pointed-maps.md) `f : A →∗ B` to a pointed map
`g : X →∗ Y` is a [triple](foundation.dependent-pair-types.md) `(i , j , H)`
consisting of [pointed equivalences](structured-types.pointed-equivalences.md)
`i : A ≃∗ X` and `j : B ≃∗ Y` and a
[pointed homotopy](structured-types.pointed-homotopies.md)
`H : j ∘∗ f ~∗ g ∘∗ i` witnessing that the square

```text
        i
    A -----> X
    |        |
  f |        | g
    ∨        ∨
    B -----> Y
        j
```

[commutes](structured-types.commuting-squares-of-pointed-maps.md).

## Definitions

### Equivalences of pointed arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  (f : A →∗ B) (g : X →∗ Y)
  where

  coherence-equiv-pointed-arrow :
    (A ≃∗ X) → (B ≃∗ Y) → UU (l1 ⊔ l4)
  coherence-equiv-pointed-arrow i j =
    coherence-square-pointed-maps
      ( pointed-map-pointed-equiv i)
      ( f)
      ( g)
      ( pointed-map-pointed-equiv j)

  equiv-pointed-arrow : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  equiv-pointed-arrow =
    Σ (A ≃∗ X) (λ i → Σ (B ≃∗ Y) (coherence-equiv-pointed-arrow i))

module _
  {l1 l2 l3 l4 : Level} {A : Pointed-Type l1} {B : Pointed-Type l2}
  {X : Pointed-Type l3} {Y : Pointed-Type l4}
  {f : A →∗ B} {g : X →∗ Y} (e : equiv-pointed-arrow f g)
  where

  pointed-equiv-domain-equiv-pointed-arrow : A ≃∗ X
  pointed-equiv-domain-equiv-pointed-arrow = pr1 e

  equiv-domain-equiv-pointed-arrow : type-Pointed-Type A ≃ type-Pointed-Type X
  equiv-domain-equiv-pointed-arrow =
    equiv-pointed-equiv pointed-equiv-domain-equiv-pointed-arrow

  pointed-map-domain-equiv-pointed-arrow : A →∗ X
  pointed-map-domain-equiv-pointed-arrow =
    pointed-map-pointed-equiv pointed-equiv-domain-equiv-pointed-arrow

  map-domain-equiv-pointed-arrow : type-Pointed-Type A → type-Pointed-Type X
  map-domain-equiv-pointed-arrow =
    map-pointed-equiv pointed-equiv-domain-equiv-pointed-arrow

  preserves-point-map-domain-equiv-pointed-arrow :
    map-domain-equiv-pointed-arrow (point-Pointed-Type A) ＝
    point-Pointed-Type X
  preserves-point-map-domain-equiv-pointed-arrow =
    preserves-point-pointed-equiv pointed-equiv-domain-equiv-pointed-arrow

  pointed-equiv-codomain-equiv-pointed-arrow : B ≃∗ Y
  pointed-equiv-codomain-equiv-pointed-arrow = pr1 (pr2 e)

  equiv-codomain-equiv-pointed-arrow : type-Pointed-Type B ≃ type-Pointed-Type Y
  equiv-codomain-equiv-pointed-arrow =
    equiv-pointed-equiv pointed-equiv-codomain-equiv-pointed-arrow

  map-codomain-equiv-pointed-arrow : type-Pointed-Type B → type-Pointed-Type Y
  map-codomain-equiv-pointed-arrow =
    map-pointed-equiv pointed-equiv-codomain-equiv-pointed-arrow

  preserves-point-map-codomain-equiv-pointed-arrow :
    map-codomain-equiv-pointed-arrow (point-Pointed-Type B) ＝
    point-Pointed-Type Y
  preserves-point-map-codomain-equiv-pointed-arrow =
    preserves-point-pointed-equiv pointed-equiv-codomain-equiv-pointed-arrow

  coh-equiv-pointed-arrow :
    coherence-equiv-pointed-arrow
      ( f)
      ( g)
      ( pointed-equiv-domain-equiv-pointed-arrow)
      ( pointed-equiv-codomain-equiv-pointed-arrow)
  coh-equiv-pointed-arrow = pr2 (pr2 e)

  htpy-coh-equiv-pointed-arrow :
    coherence-equiv-arrow
      ( map-pointed-map f)
      ( map-pointed-map g)
      ( equiv-domain-equiv-pointed-arrow)
      ( equiv-codomain-equiv-pointed-arrow)
  htpy-coh-equiv-pointed-arrow = htpy-pointed-htpy coh-equiv-pointed-arrow
```
