# Suspension Structures

```agda
module synthetic-homotopy-theory.suspension-structures where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.constant-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-systems
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels
open import foundation.whiskering-identifications-concatenation

open import synthetic-homotopy-theory.cocones-under-spans
```

</details>

## Idea

The suspension of `X` is the [pushout](synthetic-homotopy-theory.pushouts.md) of
the span `unit <── X ──> unit`. A
[cocone under such a span](synthetic-homotopy-theory.dependent-cocones-under-spans.md)
is called a `suspension-cocone`. Explicitly, a suspension cocone with nadir `Y`
consists of functions

```text
f : unit → Y
g : unit → Y
```

and a homotopy

```text
h : (x : X) → (f ∘ (terminal-map X)) x ＝ (g ∘ (terminal-map X)) x
```

Using the
[universal property of the unit type](foundation.universal-property-unit-type.md),
we can characterize suspension cocones as equivalent to a selection of "north"
and "south" poles

```text
north , south : Y
```

and a meridian function

```text
meridian : X → north ＝ south
```

We call this type of structure `suspension-structure`.

## Definition

### Suspension cocones on a type

```agda
suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) → UU (l1 ⊔ l2)
suspension-cocone X Y = cocone (terminal-map X) (terminal-map X) Y
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

  north-suspension-structure : suspension-structure X Y → Y
  north-suspension-structure c = pr1 c

  south-suspension-structure : suspension-structure X Y → Y
  south-suspension-structure c = (pr1 ∘ pr2) c

  meridian-suspension-structure :
    (c : suspension-structure X Y) →
    X → north-suspension-structure c ＝ south-suspension-structure c
  meridian-suspension-structure c = (pr2 ∘ pr2) c
```

## Properties

### Equivalence between suspension structures and suspension cocones

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Y : UU l2}
  where

  suspension-cocone-suspension-structure :
    suspension-structure X Y → suspension-cocone X Y
  pr1 (suspension-cocone-suspension-structure (N , S , merid)) = point N
  pr1 (pr2 (suspension-cocone-suspension-structure (N , S , merid))) = point S
  pr2 (pr2 (suspension-cocone-suspension-structure (N , S , merid))) = merid

  suspension-structure-suspension-cocone :
    suspension-cocone X Y → suspension-structure X Y
  pr1 (suspension-structure-suspension-cocone (N , S , merid)) = N star
  pr1 (pr2 (suspension-structure-suspension-cocone (N , S , merid))) = S star
  pr2 (pr2 (suspension-structure-suspension-cocone (N , S , merid))) = merid

  is-equiv-suspension-cocone-suspension-structure :
    is-equiv suspension-cocone-suspension-structure
  is-equiv-suspension-cocone-suspension-structure =
    is-equiv-is-invertible
      ( suspension-structure-suspension-cocone)
      ( refl-htpy)
      ( refl-htpy)

  is-equiv-suspension-structure-suspension-cocone :
    is-equiv suspension-structure-suspension-cocone
  is-equiv-suspension-structure-suspension-cocone =
    is-equiv-is-invertible
      ( suspension-cocone-suspension-structure)
      ( refl-htpy)
      ( refl-htpy)

  equiv-suspension-structure-suspension-cocone :
    suspension-structure X Y ≃ suspension-cocone X Y
  pr1 equiv-suspension-structure-suspension-cocone =
    suspension-cocone-suspension-structure
  pr2 equiv-suspension-structure-suspension-cocone =
    is-equiv-suspension-cocone-suspension-structure

  equiv-suspension-cocone-suspension-structure :
    suspension-cocone X Y ≃ suspension-structure X Y
  pr1 equiv-suspension-cocone-suspension-structure =
    suspension-structure-suspension-cocone
  pr2 equiv-suspension-cocone-suspension-structure =
    is-equiv-suspension-structure-suspension-cocone
```

#### Characterization of equalities in `suspension-structure`

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2}
  where

  htpy-suspension-structure :
    (c c' : suspension-structure X Z) → UU (l1 ⊔ l2)
  htpy-suspension-structure c c' =
    Σ ( north-suspension-structure c ＝ north-suspension-structure c')
      ( λ p →
        Σ ( south-suspension-structure c ＝ south-suspension-structure c')
          ( λ q →
            ( x : X) →
            ( meridian-suspension-structure c x ∙ q) ＝
            ( p ∙ meridian-suspension-structure c' x)))

  north-htpy-suspension-structure :
    {c c' : suspension-structure X Z} →
    htpy-suspension-structure c c' →
    north-suspension-structure c ＝ north-suspension-structure c'
  north-htpy-suspension-structure = pr1

  south-htpy-suspension-structure :
    {c c' : suspension-structure X Z} →
    htpy-suspension-structure c c' →
    south-suspension-structure c ＝ south-suspension-structure c'
  south-htpy-suspension-structure = pr1 ∘ pr2

  meridian-htpy-suspension-structure :
    {c c' : suspension-structure X Z} →
    (h : htpy-suspension-structure c c') →
    ( x : X) →
    coherence-square-identifications
      ( north-htpy-suspension-structure h)
      ( meridian-suspension-structure c x)
      ( meridian-suspension-structure c' x)
      ( south-htpy-suspension-structure h)
  meridian-htpy-suspension-structure = pr2 ∘ pr2

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
  pr1 refl-htpy-suspension-structure = refl
  pr1 (pr2 refl-htpy-suspension-structure) = refl
  pr2 (pr2 refl-htpy-suspension-structure) = right-unit-htpy

  is-refl-refl-htpy-suspension-structure :
    refl-htpy-suspension-structure ＝ htpy-eq-suspension-structure refl
  is-refl-refl-htpy-suspension-structure = refl

  extensionality-suspension-structure-refl-htpy-suspension-structure :
    eq-htpy-suspension-structure refl-htpy-suspension-structure ＝ refl
  extensionality-suspension-structure-refl-htpy-suspension-structure =
    is-injective-equiv
      ( extensionality-suspension-structure c c)
      ( is-section-map-inv-equiv
        ( extensionality-suspension-structure c c)
        ( refl-htpy-suspension-structure))

module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2} {c : suspension-structure X Z}
  where

  ind-htpy-suspension-structure :
    { l : Level}
    ( P :
      (c' : suspension-structure X Z) → htpy-suspension-structure c c' → UU l) →
    ( P c refl-htpy-suspension-structure) →
    ( c' : suspension-structure X Z)
    ( H : htpy-suspension-structure c c') →
    P c' H
  ind-htpy-suspension-structure P =
    pr1
      ( is-identity-system-is-torsorial
        ( c)
        ( refl-htpy-suspension-structure)
        ( is-contr-equiv
          ( Σ (suspension-structure X Z) (λ c' → c ＝ c'))
          ( inv-equiv
            ( equiv-tot (extensionality-suspension-structure c)))
          ( is-torsorial-Id c))
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
      ( ap
        ( ap pr1)
        ( is-retraction-map-inv-equiv
          ( extensionality-suspension-structure c c)
          ( refl)))

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

### Characterization of equalities in `htpy-suspension-structure`

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2}
  {c c' : suspension-structure X Z}
  where

  htpy-in-htpy-suspension-structure :
    htpy-suspension-structure c c' →
    htpy-suspension-structure c c' → UU (l1 ⊔ l2)
  htpy-in-htpy-suspension-structure (n , s , h) (n' , s' , h') =
    Σ ( n ＝ n')
      ( λ p →
        Σ ( s ＝ s')
          ( λ q →
            (x : X) →
            coherence-square-identifications
              ( h x)
              ( left-whisker-concat
                ( meridian-suspension-structure c x)
                ( q))
              ( right-whisker-concat
                ( p)
                ( meridian-suspension-structure c' x))
              ( h' x)))

  extensionality-htpy-suspension-structure :
    (h h' : htpy-suspension-structure c c') →
      (h ＝ h') ≃ htpy-in-htpy-suspension-structure h h'
  extensionality-htpy-suspension-structure (n , s , h) =
    extensionality-Σ
      ( λ y p →
        Σ ( s ＝ pr1 y)
          ( λ q →
            (x : X) →
            coherence-square-identifications
              ( h x)
              ( left-whisker-concat
                ( meridian-suspension-structure c x)
                ( q))
              ( right-whisker-concat
                ( p)
                ( meridian-suspension-structure c' x))
              ( pr2 y x)))
      ( refl)
      ( refl , inv-htpy right-unit-htpy)
      ( λ n' → id-equiv)
      ( extensionality-Σ
        ( λ h' q →
          (x : X) →
          coherence-square-identifications
            ( h x)
            ( left-whisker-concat (meridian-suspension-structure c x) q)
            ( right-whisker-concat
              ( refl)
              ( meridian-suspension-structure c' x))
            ( h' x))
        ( refl)
        ( inv-htpy right-unit-htpy)
        ( λ q → id-equiv)
        ( λ h' →
          ( inv-equiv (equiv-concat-htpy' h' (right-unit-htpy))) ∘e
          ( equiv-inv-htpy h h') ∘e
          ( equiv-funext {f = h} {g = h'})))

  north-htpy-in-htpy-suspension-structure :
    {h h' : htpy-suspension-structure c c'} →
    htpy-in-htpy-suspension-structure h h' →
    ( north-htpy-suspension-structure h) ＝
    ( north-htpy-suspension-structure h')
  north-htpy-in-htpy-suspension-structure = pr1

  south-htpy-in-htpy-suspension-structure :
    {h h' : htpy-suspension-structure c c'} →
    htpy-in-htpy-suspension-structure h h' →
    ( south-htpy-suspension-structure h) ＝
    ( south-htpy-suspension-structure h')
  south-htpy-in-htpy-suspension-structure = pr1 ∘ pr2

  meridian-htpy-in-htpy-suspension-structure :
    {h h' : htpy-suspension-structure c c'} →
    (H : htpy-in-htpy-suspension-structure h h') →
    (x : X) →
      coherence-square-identifications
        ( meridian-htpy-suspension-structure h x)
        ( left-whisker-concat
          ( meridian-suspension-structure c x)
          ( south-htpy-in-htpy-suspension-structure H))
        ( right-whisker-concat
          ( north-htpy-in-htpy-suspension-structure H)
          ( meridian-suspension-structure c' x))
        ( meridian-htpy-suspension-structure h' x)
  meridian-htpy-in-htpy-suspension-structure = pr2 ∘ pr2

module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2}
  {c c' : suspension-structure X Z} {h h' : htpy-suspension-structure c c'}
  where

  htpy-eq-htpy-suspension-structure :
    h ＝ h' → htpy-in-htpy-suspension-structure h h'
  htpy-eq-htpy-suspension-structure =
    map-equiv (extensionality-htpy-suspension-structure h h')

  eq-htpy-in-htpy-suspension-structure :
    htpy-in-htpy-suspension-structure h h' → h ＝ h'
  eq-htpy-in-htpy-suspension-structure =
    map-inv-equiv (extensionality-htpy-suspension-structure h h')
```
