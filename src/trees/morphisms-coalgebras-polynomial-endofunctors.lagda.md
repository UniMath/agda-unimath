# Morphisms of coalgebras of polynomial endofunctors

```agda
module trees.morphisms-coalgebras-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import trees.coalgebras-polynomial-endofunctors
open import trees.polynomial-endofunctors
```

</details>

## Idea

A
{{#concept "morphism" Disambiguation="of coalgebras of a polynomial endofunctor" Agda=hom-coalgebra-polynomial-endofunctor}}
of [coalgebras](trees.coalgebras-polynomial-endofunctors.md) of a
[polynomial endofunctor](trees.polynomial-endofunctors.md) `P` consists of a
function `f : X → Y` between their underlying types, equipped with a homotopy
witnessing that the square

```text
            f
    X -------------> Y
    |                |
    |                |
    ∨                ∨
   P X -----------> P Y
           P f
```

commutes.

## Definitions

### Morphisms of coalgebras for polynomial endofunctors

```agda
module _
  {l1 l2 l3 l4 : Level}
  {P : polynomial-endofunctor l1 l2}
  (X : coalgebra-polynomial-endofunctor l3 P)
  (Y : coalgebra-polynomial-endofunctor l4 P)
  where

  hom-coalgebra-polynomial-endofunctor : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  hom-coalgebra-polynomial-endofunctor =
    Σ ( type-coalgebra-polynomial-endofunctor X →
        type-coalgebra-polynomial-endofunctor Y)
      ( λ f →
        ( coherence-square-maps f
            ( structure-coalgebra-polynomial-endofunctor X)
            ( structure-coalgebra-polynomial-endofunctor Y)
            ( map-polynomial-endofunctor P f)))

  map-hom-coalgebra-polynomial-endofunctor :
    hom-coalgebra-polynomial-endofunctor →
    type-coalgebra-polynomial-endofunctor X →
    type-coalgebra-polynomial-endofunctor Y
  map-hom-coalgebra-polynomial-endofunctor f = pr1 f

  structure-hom-coalgebra-polynomial-endofunctor :
    (f : hom-coalgebra-polynomial-endofunctor) →
    coherence-square-maps
      ( map-hom-coalgebra-polynomial-endofunctor f)
      ( structure-coalgebra-polynomial-endofunctor X)
      ( structure-coalgebra-polynomial-endofunctor Y)
      ( map-polynomial-endofunctor P
        ( map-hom-coalgebra-polynomial-endofunctor f))
  structure-hom-coalgebra-polynomial-endofunctor f = pr2 f
```

## Properties

### The identity type of morphisms of coalgebras of polynomial endofunctors

```agda
module _
  {l1 l2 l3 l4 : Level}
  {P : polynomial-endofunctor l1 l2}
  (X : coalgebra-polynomial-endofunctor l3 P)
  (Y : coalgebra-polynomial-endofunctor l4 P)
  (f : hom-coalgebra-polynomial-endofunctor X Y)
  where

  htpy-hom-coalgebra-polynomial-endofunctor :
    (g : hom-coalgebra-polynomial-endofunctor X Y) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-hom-coalgebra-polynomial-endofunctor g =
    Σ ( map-hom-coalgebra-polynomial-endofunctor X Y f ~
        map-hom-coalgebra-polynomial-endofunctor X Y g)
      ( λ H →
        ( ( structure-hom-coalgebra-polynomial-endofunctor X Y f) ∙h
          ( structure-coalgebra-polynomial-endofunctor Y ·l H)) ~
        ( ( ( htpy-polynomial-endofunctor P H) ·r
            ( structure-coalgebra-polynomial-endofunctor X)) ∙h
          ( structure-hom-coalgebra-polynomial-endofunctor X Y g)))

  refl-htpy-hom-coalgebra-polynomial-endofunctor :
    htpy-hom-coalgebra-polynomial-endofunctor f
  pr1 refl-htpy-hom-coalgebra-polynomial-endofunctor = refl-htpy
  pr2 refl-htpy-hom-coalgebra-polynomial-endofunctor z =
    ( right-unit) ∙
    ( inv
      ( ap
        ( concat'
          ( map-polynomial-endofunctor P
            ( map-hom-coalgebra-polynomial-endofunctor X Y f)
            ( structure-coalgebra-polynomial-endofunctor X z))
          ( structure-hom-coalgebra-polynomial-endofunctor X Y f z))
        ( coh-refl-htpy-polynomial-endofunctor P
          ( map-hom-coalgebra-polynomial-endofunctor X Y f)
          ( structure-coalgebra-polynomial-endofunctor X z))))

  htpy-eq-hom-coalgebra-polynomial-endofunctor :
    (g : hom-coalgebra-polynomial-endofunctor X Y) →
    f ＝ g → htpy-hom-coalgebra-polynomial-endofunctor g
  htpy-eq-hom-coalgebra-polynomial-endofunctor .f refl =
    refl-htpy-hom-coalgebra-polynomial-endofunctor

  is-torsorial-htpy-hom-coalgebra-polynomial-endofunctor :
    is-torsorial htpy-hom-coalgebra-polynomial-endofunctor
  is-torsorial-htpy-hom-coalgebra-polynomial-endofunctor =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (map-hom-coalgebra-polynomial-endofunctor X Y f))
      ( map-hom-coalgebra-polynomial-endofunctor X Y f , refl-htpy)
      ( is-contr-equiv'
        ( Σ ( coherence-square-maps
              ( map-hom-coalgebra-polynomial-endofunctor X Y f)
              ( structure-coalgebra-polynomial-endofunctor X)
              ( structure-coalgebra-polynomial-endofunctor Y)
              ( map-polynomial-endofunctor P
                ( map-hom-coalgebra-polynomial-endofunctor X Y f)))
            ( λ G →
              ( ( structure-hom-coalgebra-polynomial-endofunctor X Y f) ∙h
                ( refl-htpy)) ~
              ( G)))
        ( equiv-tot
          ( λ G →
            equiv-concat-htpy'
              ( ( structure-hom-coalgebra-polynomial-endofunctor X Y f) ∙h
                ( refl-htpy))
              ( λ x →
                ap
                  ( concat'
                    ( map-polynomial-endofunctor P
                      ( map-hom-coalgebra-polynomial-endofunctor X Y f)
                      ( structure-coalgebra-polynomial-endofunctor X x))
                    (G x))
                  ( inv
                    ( coh-refl-htpy-polynomial-endofunctor P
                      ( map-hom-coalgebra-polynomial-endofunctor X Y f)
                      ( structure-coalgebra-polynomial-endofunctor X x))))))
        ( is-torsorial-htpy
          ( ( structure-hom-coalgebra-polynomial-endofunctor X Y f) ∙h
            ( refl-htpy))))

  is-equiv-htpy-eq-hom-coalgebra-polynomial-endofunctor :
    (g : hom-coalgebra-polynomial-endofunctor X Y) →
    is-equiv (htpy-eq-hom-coalgebra-polynomial-endofunctor g)
  is-equiv-htpy-eq-hom-coalgebra-polynomial-endofunctor =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-coalgebra-polynomial-endofunctor)
      ( htpy-eq-hom-coalgebra-polynomial-endofunctor)

  extensionality-hom-coalgebra-polynomial-endofunctor :
    (g : hom-coalgebra-polynomial-endofunctor X Y) →
    (f ＝ g) ≃ htpy-hom-coalgebra-polynomial-endofunctor g
  pr1 (extensionality-hom-coalgebra-polynomial-endofunctor g) =
    htpy-eq-hom-coalgebra-polynomial-endofunctor g
  pr2 (extensionality-hom-coalgebra-polynomial-endofunctor g) =
    is-equiv-htpy-eq-hom-coalgebra-polynomial-endofunctor g

  eq-htpy-hom-coalgebra-polynomial-endofunctor :
    (g : hom-coalgebra-polynomial-endofunctor X Y) →
    htpy-hom-coalgebra-polynomial-endofunctor g → f ＝ g
  eq-htpy-hom-coalgebra-polynomial-endofunctor g =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-coalgebra-polynomial-endofunctor g)
```
