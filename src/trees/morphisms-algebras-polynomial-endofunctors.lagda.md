# Morphisms of algebras of polynomial endofunctors

```agda
module trees.morphisms-algebras-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import trees.algebras-polynomial-endofunctors
open import trees.polynomial-endofunctors
```

</details>

## Idea

A
{{#concept "morphism" Disambiguation="of algebras of a polynomial endofunctor" Agda=hom-algebra-polynomial-endofunctor}}
of [algebras](trees.algebras-polynomial-endofunctors.md) of a
[polynomial endofunctor](trees.polynomial-endofunctors.md) `P` consists of a map
`f : X → Y` between the underlying types, equipped with a homotopy witnessing
that the square

```text
            P f
   P X -----------> P Y
    |                |
    |                |
    ∨                ∨
    X -------------> Y
             f
```

commutes.

## Definitions

### Morphisms of algebras for polynomial endofunctors

```agda
module _
  {l1 l2 l3 l4 : Level}
  {P : polynomial-endofunctor l1 l2}
  (X : algebra-polynomial-endofunctor l3 P)
  (Y : algebra-polynomial-endofunctor l4 P)
  where

  hom-algebra-polynomial-endofunctor : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-algebra-polynomial-endofunctor =
    Σ ( type-algebra-polynomial-endofunctor X →
        type-algebra-polynomial-endofunctor Y)
      ( λ f →
        ( f ∘ (structure-algebra-polynomial-endofunctor X)) ~
        ( ( structure-algebra-polynomial-endofunctor Y) ∘
          ( map-polynomial-endofunctor P f)))

  map-hom-algebra-polynomial-endofunctor :
    hom-algebra-polynomial-endofunctor →
    type-algebra-polynomial-endofunctor X →
    type-algebra-polynomial-endofunctor Y
  map-hom-algebra-polynomial-endofunctor f = pr1 f

  structure-hom-algebra-polynomial-endofunctor :
    (f : hom-algebra-polynomial-endofunctor) →
    ( ( map-hom-algebra-polynomial-endofunctor f) ∘
      ( structure-algebra-polynomial-endofunctor X)) ~
    ( ( structure-algebra-polynomial-endofunctor Y) ∘
      ( map-polynomial-endofunctor P
        ( map-hom-algebra-polynomial-endofunctor f)))
  structure-hom-algebra-polynomial-endofunctor f = pr2 f
```

## Properties

### The identity type of morphisms of algebras of polynomial endofunctors

```agda
module _
  {l1 l2 l3 l4 : Level}
  {P : polynomial-endofunctor l1 l2}
  (X : algebra-polynomial-endofunctor l3 P)
  (Y : algebra-polynomial-endofunctor l4 P)
  (f : hom-algebra-polynomial-endofunctor X Y)
  where

  htpy-hom-algebra-polynomial-endofunctor :
    (g : hom-algebra-polynomial-endofunctor X Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-algebra-polynomial-endofunctor g =
    Σ ( map-hom-algebra-polynomial-endofunctor X Y f ~
        map-hom-algebra-polynomial-endofunctor X Y g)
      ( λ H →
        ( ( structure-hom-algebra-polynomial-endofunctor X Y f) ∙h
          ( ( structure-algebra-polynomial-endofunctor Y) ·l
            ( htpy-polynomial-endofunctor P H))) ~
        ( ( H ·r structure-algebra-polynomial-endofunctor X) ∙h
          ( structure-hom-algebra-polynomial-endofunctor X Y g)))

  refl-htpy-hom-algebra-polynomial-endofunctor :
    htpy-hom-algebra-polynomial-endofunctor f
  pr1 refl-htpy-hom-algebra-polynomial-endofunctor = refl-htpy
  pr2 refl-htpy-hom-algebra-polynomial-endofunctor z =
    ( ap
      ( λ t →
        concat
          ( structure-hom-algebra-polynomial-endofunctor X Y f z)
          ( structure-algebra-polynomial-endofunctor Y
            ( map-polynomial-endofunctor P
              ( map-hom-algebra-polynomial-endofunctor X Y f) z))
          ( ap (structure-algebra-polynomial-endofunctor Y) t))
      ( coh-refl-htpy-polynomial-endofunctor P
        ( map-hom-algebra-polynomial-endofunctor X Y f) z)) ∙
    ( right-unit)

  htpy-eq-hom-algebra-polynomial-endofunctor :
    (g : hom-algebra-polynomial-endofunctor X Y) →
    f ＝ g → htpy-hom-algebra-polynomial-endofunctor g
  htpy-eq-hom-algebra-polynomial-endofunctor .f refl =
    refl-htpy-hom-algebra-polynomial-endofunctor

  is-torsorial-htpy-hom-algebra-polynomial-endofunctor :
    is-torsorial htpy-hom-algebra-polynomial-endofunctor
  is-torsorial-htpy-hom-algebra-polynomial-endofunctor =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (map-hom-algebra-polynomial-endofunctor X Y f))
      ( pair (map-hom-algebra-polynomial-endofunctor X Y f) refl-htpy)
      ( is-contr-equiv'
        ( Σ ( ( (pr1 f) ∘ pr2 X) ~
              ( pr2 Y ∘ map-polynomial-endofunctor P (pr1 f)))
            ( λ H → (pr2 f) ~ H))
        ( equiv-tot
          ( λ H →
            ( equiv-concat-htpy
              ( λ x →
                ap
                  ( concat
                    ( pr2 f x)
                    ( structure-algebra-polynomial-endofunctor Y
                      ( map-polynomial-endofunctor P (pr1 f) x)))
                  ( ap
                    ( ap (pr2 Y))
                    ( coh-refl-htpy-polynomial-endofunctor P (pr1 f) x)))
              ( H)) ∘e
            ( equiv-concat-htpy right-unit-htpy H)))
        ( is-torsorial-htpy (pr2 f)))

  is-equiv-htpy-eq-hom-algebra-polynomial-endofunctor :
    (g : hom-algebra-polynomial-endofunctor X Y) →
    is-equiv (htpy-eq-hom-algebra-polynomial-endofunctor g)
  is-equiv-htpy-eq-hom-algebra-polynomial-endofunctor =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-algebra-polynomial-endofunctor)
      ( htpy-eq-hom-algebra-polynomial-endofunctor)

  extensionality-hom-algebra-polynomial-endofunctor :
    (g : hom-algebra-polynomial-endofunctor X Y) →
    (f ＝ g) ≃ htpy-hom-algebra-polynomial-endofunctor g
  pr1 (extensionality-hom-algebra-polynomial-endofunctor g) =
    htpy-eq-hom-algebra-polynomial-endofunctor g
  pr2 (extensionality-hom-algebra-polynomial-endofunctor g) =
    is-equiv-htpy-eq-hom-algebra-polynomial-endofunctor g

  eq-htpy-hom-algebra-polynomial-endofunctor :
    (g : hom-algebra-polynomial-endofunctor X Y) →
    htpy-hom-algebra-polynomial-endofunctor g → f ＝ g
  eq-htpy-hom-algebra-polynomial-endofunctor g =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-algebra-polynomial-endofunctor g)
```
