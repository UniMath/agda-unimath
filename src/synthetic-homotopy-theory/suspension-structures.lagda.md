# Suspension Structures

```agda
module synthetic-homotopy-theory.suspension-structures where
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
open import foundation.embeddings
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
open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.dependent-universal-property-pushouts
open import synthetic-homotopy-theory.loop-spaces
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

The suspension of `X` is the pushout of the span `unit <-- X --> unit`. A cocone
under such a span is called a
`suspension-cocone'. Since `unit`is a quite special type, suspension cocones are equivalent to a structure that is easier to work with, one which we call`suspension-structure`.

## Definition

### Suspension cocones on a type

```agda
suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
suspension-cocone X Y = cocone (const X unit star) (const X unit star) Y
```

### Suspension structures on a type

```agda
module _
  {l1 l2 : Level} (X : UU l1) (Y : UU l2)
  where

  suspension-structure : UU (l1 ⊔ l2)
  suspension-structure = Σ Y (λ N → Σ Y (λ S → (x : X) → N ＝ S))

module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  N-suspension-structure : suspension-structure X Y → Y
  N-suspension-structure c = pr1 c

  S-suspension-structure : suspension-structure X Y → Y
  S-suspension-structure c = (pr1 ∘ pr2) c

  merid-suspension-structure :
    (c : suspension-structure X Y) →
    X → N-suspension-structure c ＝ S-suspension-structure c
  merid-suspension-structure c = (pr2 ∘ pr2) c
```

## Properties

### Equivalence between suspension structures and suspension cocones

```agda
cocone-suspension-structure :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) →
  suspension-structure X Y → suspension-cocone X Y
cocone-suspension-structure X Y (pair N (pair S merid)) =
  pair
    ( const unit Y N)
    ( pair
      ( const unit Y S)
      ( merid))

comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  suspension-cocone X Z ≃ suspension-structure X Z
comparison-suspension-cocone X Z =
  equiv-Σ
    ( λ z1 → Σ Z (λ z2 → (x : X) → Id z1 z2))
    ( equiv-universal-property-unit Z)
    ( λ z1 →
      equiv-Σ
        ( λ z2 → (x : X) → Id (z1 star) z2)
        ( equiv-universal-property-unit Z)
        ( λ z2 → id-equiv))

map-comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  suspension-cocone X Z → suspension-structure X Z
map-comparison-suspension-cocone X Z =
  map-equiv (comparison-suspension-cocone X Z)

is-equiv-map-comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  is-equiv (map-comparison-suspension-cocone X Z)
is-equiv-map-comparison-suspension-cocone X Z =
  is-equiv-map-equiv (comparison-suspension-cocone X Z)

htpy-map-inv-comparison-suspension-cocone-cocone-suspension-structure :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
    ( map-inv-equiv (comparison-suspension-cocone X Z))
  ~
    ( cocone-suspension-structure X Z)
htpy-map-inv-comparison-suspension-cocone-cocone-suspension-structure
  ( X)
  ( Z)
  ( x) =
    map-inv-equiv
      ( equiv-ap-emb (emb-equiv (comparison-suspension-cocone X Z)))
      ( is-section-map-inv-equiv (comparison-suspension-cocone X Z) x)

is-equiv-map-inv-comparison-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  is-equiv (cocone-suspension-structure X Z)
is-equiv-map-inv-comparison-suspension-cocone X Z =
  is-equiv-htpy
    ( map-inv-equiv (comparison-suspension-cocone X Z))
    ( inv-htpy
      ( htpy-map-inv-comparison-suspension-cocone-cocone-suspension-structure
        ( X)
        ( Z)))
    ( is-equiv-map-inv-equiv (comparison-suspension-cocone X Z))
```

#### Characterization of equalities in `suspension-structure`

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2}
  where

  htpy-suspension-structure :
    (c c' : suspension-structure X Z) → UU (l1 ⊔ l2)
  htpy-suspension-structure c c' =
    Σ ( (N-suspension-structure c) ＝ (N-suspension-structure c'))
      ( λ p →
        Σ ( ( S-suspension-structure c) ＝ ( S-suspension-structure c'))
          ( λ q →
            ( x : X) →
            ( merid-suspension-structure c x ∙ q) ＝
            ( p ∙ merid-suspension-structure c' x)))

  extensionality-suspension-structure :
    (c c' : suspension-structure X Z) →
    (c ＝ c') ≃ (htpy-suspension-structure c c')
  extensionality-suspension-structure (N , S , merid) =
    extensionality-Σ
      ( λ y p →
        Σ (S ＝ pr1 y) (λ q → (x : X) → (merid x ∙ q) ＝ (p ∙ pr2 y x)))
      ( refl)
      ( refl , right-unit-htpy)
      ( λ z → id-equiv)
      ( extensionality-Σ
        ( λ H q → (x : X) → (merid x ∙ q) ＝ H x)
        ( refl)
        ( right-unit-htpy)
        ( λ z → id-equiv)
        ( λ H → equiv-concat-htpy right-unit-htpy H ∘e equiv-funext))

module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} {c c' : suspension-structure X Z}
  where

  htpy-eq-suspension-structure : (c ＝ c') → htpy-suspension-structure c c'
  htpy-eq-suspension-structure =
    map-equiv (extensionality-suspension-structure c c')

  eq-htpy-suspension-structure : htpy-suspension-structure c c' → (c ＝ c')
  eq-htpy-suspension-structure =
    map-inv-equiv (extensionality-suspension-structure c c')

module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} {c : suspension-structure X Z}
  where

  refl-htpy-suspension-structure : htpy-suspension-structure c c
  refl-htpy-suspension-structure = refl , (refl , right-unit-htpy)

  is-refl-refl-htpy-suspension-structure :
    refl-htpy-suspension-structure ＝ htpy-eq-suspension-structure refl
  is-refl-refl-htpy-suspension-structure = refl

module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} {c : suspension-structure X Z}
  where

  ind-htpy-suspension-structure :
    { l : Level}
    ( P :
      ( c' : suspension-structure X Z) →
      ( htpy-suspension-structure c c') →
      UU l) →
    ( P c refl-htpy-suspension-structure) →
    ( ( c' : suspension-structure X Z)
      ( H : htpy-suspension-structure c c') →
      P c' H)
  ind-htpy-suspension-structure P =
    pr1
      ( Ind-identity-system
        ( c)
        ( refl-htpy-suspension-structure)
        ( is-contr-equiv
          ( Σ (suspension-structure X Z) (λ c' → c ＝ c'))
          ( inv-equiv
            ( equiv-tot (extensionality-suspension-structure c)))
          ( is-contr-total-path c))
        ( P))
```

#### The action of paths of the projections have the expected effect

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} (c : suspension-structure X Z)
  where

  ap-pr1-eq-htpy-suspension-structure :
    (c' : suspension-structure X Z) (H : htpy-suspension-structure c c') →
    (ap (pr1) (eq-htpy-suspension-structure H)) ＝ (pr1 H)
  ap-pr1-eq-htpy-suspension-structure =
    ind-htpy-suspension-structure
      ( λ c' H → (ap (pr1) (eq-htpy-suspension-structure H)) ＝ (pr1 H))
      ( (ap
        ( ap pr1)
        ( is-retraction-map-inv-equiv
          ( extensionality-suspension-structure c c)
          ( refl))))

  ap-pr1∘pr2-eq-htpy-suspension-structure :
    (c' : suspension-structure X Z) (H : htpy-suspension-structure c c') →
    (ap (pr1 ∘ pr2) (eq-htpy-suspension-structure H)) ＝ ((pr1 ∘ pr2) H)
  ap-pr1∘pr2-eq-htpy-suspension-structure =
    ind-htpy-suspension-structure
      ( λ c' H →
        ap (pr1 ∘ pr2) (eq-htpy-suspension-structure H) ＝ (pr1 ∘ pr2) H)
      ( ap
        ( ap (pr1 ∘ pr2))
        ( is-retraction-map-inv-equiv
          ( extensionality-suspension-structure c c)
          ( refl)))
```
