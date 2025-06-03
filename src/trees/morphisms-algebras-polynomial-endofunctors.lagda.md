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

A **morphism** of algebras of a polynomial endofunctor `P A B` consists of a map
`f : X → Y` between the underlying types, equipped with a homotopy witnessing
that the square

```text
           P A B f
  P A B X ---------> P A B Y
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
hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B) →
  (Y : algebra-polynomial-endofunctor l4 A B) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
hom-algebra-polynomial-endofunctor {A = A} {B} X Y =
  Σ ( type-algebra-polynomial-endofunctor X →
      type-algebra-polynomial-endofunctor Y)
    ( λ f →
      ( f ∘ (structure-algebra-polynomial-endofunctor X)) ~
      ( ( structure-algebra-polynomial-endofunctor Y) ∘
        ( map-polynomial-endofunctor A B f)))

map-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B) →
  (Y : algebra-polynomial-endofunctor l4 A B) →
  hom-algebra-polynomial-endofunctor X Y →
  type-algebra-polynomial-endofunctor X →
  type-algebra-polynomial-endofunctor Y
map-hom-algebra-polynomial-endofunctor X Y f = pr1 f

structure-hom-algebra-polynomial-endofunctor :
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B) →
  (Y : algebra-polynomial-endofunctor l4 A B) →
  (f : hom-algebra-polynomial-endofunctor X Y) →
  ( ( map-hom-algebra-polynomial-endofunctor X Y f) ∘
    ( structure-algebra-polynomial-endofunctor X)) ~
  ( ( structure-algebra-polynomial-endofunctor Y) ∘
    ( map-polynomial-endofunctor A B
      ( map-hom-algebra-polynomial-endofunctor X Y f)))
structure-hom-algebra-polynomial-endofunctor X Y f = pr2 f
```

## Properties

### The identity type of morphisms of algebras of polynomial endofunctors

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l3 A B)
  (Y : algebra-polynomial-endofunctor l4 A B)
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
            ( htpy-polynomial-endofunctor A B H))) ~
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
            ( map-polynomial-endofunctor A B
              ( map-hom-algebra-polynomial-endofunctor X Y f) z))
          ( ap (structure-algebra-polynomial-endofunctor Y) t))
      ( coh-refl-htpy-polynomial-endofunctor A B
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
              ( pr2 Y ∘ map-polynomial-endofunctor A B (pr1 f)))
            ( λ H → (pr2 f) ~ H))
        ( equiv-tot
          ( λ H →
            ( equiv-concat-htpy
              ( λ x →
                ap
                  ( concat
                    ( pr2 f x)
                    ( structure-algebra-polynomial-endofunctor Y
                      ( map-polynomial-endofunctor A B (pr1 f) x)))
                  ( ap
                    ( ap (pr2 Y))
                    ( coh-refl-htpy-polynomial-endofunctor A B (pr1 f) x)))
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
