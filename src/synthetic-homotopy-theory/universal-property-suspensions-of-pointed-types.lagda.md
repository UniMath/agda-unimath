# Suspensions of types

```agda
module synthetic-homotopy-theory.universal-property-suspensions-of-pointed-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.commuting-squares-of-maps
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.transport
open import foundation.type-arithmetic-dependent-pair-types
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import structured-types.pointed-equivalences
open import structured-types.pointed-maps
open import structured-types.pointed-types

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.conjugation-loops
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-suspension-structures
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.dependent-universal-property-suspensions
open import synthetic-homotopy-theory.functoriality-loop-spaces
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.suspension-structures
open import synthetic-homotopy-theory.suspensions-of-pointed-types
open import synthetic-homotopy-theory.suspensions-of-types
open import synthetic-homotopy-theory.universal-property-pushouts
open import synthetic-homotopy-theory.universal-property-suspensions
```

## Idea

The suspension of a pointed type enjoys an additional universal property, on
top of the universal propertise associtated with being a suspension.
This universal property is packaged in an adjunction:
the suspension (of a pointed type) is left adjoint to the loop space.

#### The unit and counit of the adjunction

```agda
module _
  {l1 : Level} (X : Pointed-Type l1)
  where

  shift : (type-Ω (suspension-Pointed-Type X)) → (N-susp ＝ S-susp)
  shift l = l ∙ (merid-susp (point-Pointed-Type X))

  shift∗ :
    Ω (suspension-Pointed-Type X) →∗
    ((N-susp ＝ S-susp) , (merid-susp (point-Pointed-Type X)))
  pr1 shift∗ = shift
  pr2 shift∗ = refl

  unshift : (N-susp ＝ S-susp) → (type-Ω (suspension-Pointed-Type X))
  unshift p = p ∙ inv (merid-susp (point-Pointed-Type X))

  unshift∗ :
    ((N-susp ＝ S-susp) , (merid-susp (point-Pointed-Type X))) →∗
    Ω (suspension-Pointed-Type X)
  pr1 unshift∗ = unshift
  pr2 unshift∗ = right-inv (merid-susp (point-Pointed-Type X))

  is-equiv-shift : is-equiv shift
  is-equiv-shift = is-equiv-concat' N-susp (merid-susp (point-Pointed-Type X))

  pointed-equiv-shift :
    ( Ω (suspension-Pointed-Type X)) ≃∗
    ( (N-susp ＝ S-susp) , merid-susp (point-Pointed-Type X))
  pr1 (pr1 pointed-equiv-shift) = shift
  pr2 (pr1 pointed-equiv-shift) = is-equiv-shift
  pr2 pointed-equiv-shift = preserves-point-pointed-map shift∗

  merid-susp∗ : X →∗ ((N-susp ＝ S-susp) , (merid-susp (point-Pointed-Type X)))
  pr1 merid-susp∗ = merid-susp
  pr2 merid-susp∗ = refl

  unit-susp-loop-adj∗ : X →∗ Ω (suspension-Pointed-Type X)
  unit-susp-loop-adj∗ = unshift∗ ∘∗ merid-susp∗

  unit-susp-loop-adj : type-Pointed-Type X → type-Ω (suspension-Pointed-Type X)
  unit-susp-loop-adj = map-pointed-map unit-susp-loop-adj∗

  counit-susp-loop-adj : (suspension (type-Ω X)) → type-Pointed-Type X
  counit-susp-loop-adj =
    map-inv-is-equiv
      ( up-suspension (type-Ω X) (type-Pointed-Type X))
      ( ( point-Pointed-Type X) ,
        ( point-Pointed-Type X) ,
        ( id))

  counit-susp-loop-adj∗ : ((suspension (type-Ω X)) , N-susp) →∗ X
  pr1 counit-susp-loop-adj∗ = counit-susp-loop-adj
  pr2 counit-susp-loop-adj∗ =
    up-suspension-N-susp
      ( type-Ω X)
      ( type-Pointed-Type X)
      ( ( point-Pointed-Type X) ,
        ( point-Pointed-Type X) ,
        ( id))
```

#### The underlying map of the equivalence

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  map-equiv-susp-loop-adj :
    ((suspension-Pointed-Type X) →∗ Y) →
    (X →∗ Ω Y)
  map-equiv-susp-loop-adj f∗ =
    ((pointed-map-Ω f∗) ∘∗ (unit-susp-loop-adj∗ X))
```

#### The underlying map of the inverse of the equivalence

The following function takes a map `X → Ω Y` and returns a suspension structure
on `Y`.

```agda
module _
  {l1 l2 : Level} (X : UU l1) (Y : Pointed-Type l2)
  where
  suspension-structure-map-into-Ω :
    (X → type-Ω Y) → suspension-structure X (type-Pointed-Type Y)
  pr1 (suspension-structure-map-into-Ω f) = point-Pointed-Type Y
  pr1 (pr2 (suspension-structure-map-into-Ω f)) = point-Pointed-Type Y
  pr2 (pr2 (suspension-structure-map-into-Ω f)) = f
```

The above plus the universal property of suspensions defines the inverse map. We
use the universal property to define the inverse.

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  map-inv-equiv-susp-loop-adj :
    (X →∗ Ω Y) → ((suspension-Pointed-Type X) →∗ Y)
  pr1 (map-inv-equiv-susp-loop-adj f∗) =
    map-inv-up-suspension
      ( type-Pointed-Type X)
      ( type-Pointed-Type Y)
      ( suspension-structure-map-into-Ω
        ( type-Pointed-Type X)
        ( Y)
        ( map-pointed-map f∗))
  pr2 (map-inv-equiv-susp-loop-adj f∗) =
    up-suspension-N-susp
      ( type-Pointed-Type X)
      ( type-Pointed-Type Y)
      ( suspension-structure-map-into-Ω
      ( type-Pointed-Type X)
      ( Y)
      ( map-pointed-map f∗))
```

We now show these maps are inverses of each other.

[To Do]

#### The equivalence between pointed maps out of the suspension of X and pointed maps into the loop space of Y

```agda
module _
  {l1 l2 : Level} (X : Pointed-Type l1) (Y : Pointed-Type l2)
  where

  equiv-susp-loop-adj : (suspension-Pointed-Type X →∗ Y) ≃ (X →∗ Ω Y)
  equiv-susp-loop-adj =
    ( left-unit-law-Σ-is-contr
      ( is-contr-total-path (point-Pointed-Type Y))
      ( (point-Pointed-Type Y) , refl)) ∘e
    ( ( inv-equiv
        ( associative-Σ
          ( type-Pointed-Type Y)
          ( λ z → (point-Pointed-Type Y) ＝ z)
          ( λ t →
            Σ ( type-Pointed-Type X → (point-Pointed-Type Y) ＝ (pr1 t))
              ( λ f → f (point-Pointed-Type X) ＝ (pr2 t))))) ∘e
      ( ( equiv-tot (λ y1 → equiv-left-swap-Σ)) ∘e
        ( ( associative-Σ
            ( type-Pointed-Type Y)
            ( λ y1 → type-Pointed-Type X → (point-Pointed-Type Y) ＝ y1)
            ( λ z →
              Σ ( Id (point-Pointed-Type Y) (pr1 z))
                ( λ x → pr2 z (point-Pointed-Type X) ＝ x))) ∘e
          ( ( inv-equiv
              ( right-unit-law-Σ-is-contr
                ( λ ( z : Σ ( type-Pointed-Type Y)
                            ( λ y1 →
                              type-Pointed-Type X →
                              point-Pointed-Type Y ＝ y1)) →
                  is-contr-total-path ((pr2 z) (point-Pointed-Type X))))) ∘e
            ( ( left-unit-law-Σ-is-contr
                ( is-contr-total-path' (point-Pointed-Type Y))
                ( (point-Pointed-Type Y) , refl)) ∘e
              ( ( equiv-right-swap-Σ) ∘e
                ( equiv-Σ-equiv-base
                  ( λ c → (pr1 c) ＝ (point-Pointed-Type Y))
                  ( equiv-up-suspension
                    ( type-Pointed-Type X)
                    ( type-Pointed-Type Y)))))))))
```

#### The equivalence in the suspension-loop space adjunction is pointed

This remains to be shown.
