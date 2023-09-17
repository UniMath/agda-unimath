# Suspension Structures

```agda
module synthetic-homotopy-theory.suspension-structures where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
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
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
```

</details>

## Idea

The suspension of `X` is the [pushout](synthetic-homotopy-theory.pushouts.md) of
the span `unit <-- X --> unit`. A
[cocone under such a span](synthetic-homotopy-theory.dependent-cocones-under-spans.md)
is called a `suspension-cocone`. Explicitly, a suspension cocone with nadir `Y`
consists of functions

```text
f : unit → Y
g : unit → Y
```

and a homotopy

```text
h : (x : X) → (f ∘ (const X unit star)) x ＝ (g ∘ (const X unit star)) x
```

Using the
[universal property of `unit`](foundation.universal-property-unit-type.md), we
can characterize suspension cocones as equivalent to a selection of "north" and
"south" poles

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
cocone-suspension-structure :
  {l1 l2 : Level} (X : UU l1) (Y : UU l2) →
  suspension-structure X Y → suspension-cocone X Y
cocone-suspension-structure X Y (pair N (pair S merid)) =
  pair
    ( const unit Y N)
    ( pair
      ( const unit Y S)
      ( merid))

equiv-suspension-structure-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  suspension-cocone X Z ≃ suspension-structure X Z
equiv-suspension-structure-suspension-cocone X Z =
  equiv-Σ
    ( λ z1 → Σ Z (λ z2 → (x : X) → Id z1 z2))
    ( equiv-universal-property-unit Z)
    ( λ z1 →
      equiv-Σ
        ( λ z2 → (x : X) → Id (z1 star) z2)
        ( equiv-universal-property-unit Z)
        ( λ z2 → id-equiv))

map-equiv-suspension-structure-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  suspension-cocone X Z → suspension-structure X Z
map-equiv-suspension-structure-suspension-cocone X Z =
  map-equiv (equiv-suspension-structure-suspension-cocone X Z)

is-equiv-map-equiv-suspension-structure-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  is-equiv (map-equiv-suspension-structure-suspension-cocone X Z)
is-equiv-map-equiv-suspension-structure-suspension-cocone X Z =
  is-equiv-map-equiv (equiv-suspension-structure-suspension-cocone X Z)

map-inv-equiv-suspension-structure-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  suspension-structure X Z → suspension-cocone X Z
map-inv-equiv-suspension-structure-suspension-cocone X Z =
  map-inv-equiv (equiv-suspension-structure-suspension-cocone X Z)

is-equiv-map-inv-equiv-suspension-structure-suspension-cocone :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
  is-equiv (map-inv-equiv-suspension-structure-suspension-cocone X Z)
is-equiv-map-inv-equiv-suspension-structure-suspension-cocone X Z =
  is-equiv-map-inv-equiv (equiv-suspension-structure-suspension-cocone X Z)

htpy-comparison-suspension-cocone-suspension-structure :
  {l1 l2 : Level} (X : UU l1) (Z : UU l2) →
    ( map-inv-equiv-suspension-structure-suspension-cocone X Z)
  ~
    ( cocone-suspension-structure X Z)
htpy-comparison-suspension-cocone-suspension-structure
  ( X)
  ( Z)
  ( s) =
  is-injective-map-equiv
    ( equiv-suspension-structure-suspension-cocone X Z)
    ( is-section-map-inv-equiv
      ( equiv-suspension-structure-suspension-cocone X Z)
      ( s))
```

#### Characterization of equalities in `suspension-structure`

```agda
module _
  {l1 l2 : Level} {X : UU l1} {Z : UU l2}
  where

  htpy-suspension-structure :
    (c c' : suspension-structure X Z) → UU (l1 ⊔ l2)
  htpy-suspension-structure c c' =
    Σ ( (north-suspension-structure c) ＝ (north-suspension-structure c'))
      ( λ p →
        Σ ( ( south-suspension-structure c) ＝ ( south-suspension-structure c'))
          ( λ q →
            ( x : X) →
            ( meridian-suspension-structure c x ∙ q) ＝
            ( p ∙ meridian-suspension-structure c' x)))

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
      ( is-identity-system-is-torsorial
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
