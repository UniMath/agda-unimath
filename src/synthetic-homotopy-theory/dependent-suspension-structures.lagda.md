# Dependent suspension structures

```agda
module synthetic-homotopy-theory.dependent-suspension-structures where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-identifications
open import foundation.constant-maps
open import foundation.dependent-identifications
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-extensionality
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.injective-maps
open import foundation.structure-identity-principle
open import foundation.transport-along-identifications
open import foundation.unit-type
open import foundation.universal-property-unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.dependent-cocones-under-spans
open import synthetic-homotopy-theory.suspension-structures
```

</details>

## Idea

This is the dependent analog of
[suspension structures](synthetic-homotopy-theory.suspension-structures.md). The
relation between
[suspension structures](synthetic-homotopy-theory.suspension-structures.md) and
dependent suspension structures mirrors the relation between
[cocones under a span](synthetic-homotopy-theory.cocones-under-spans.md) and
[dependent cocones under a span](synthetic-homotopy-theory.dependent-cocones-under-spans.md).

Fix a type `X` and consider a suspension cocone `(f , g , h)` with nadir `Y`.
Given a type family `P : Y → UU`, a dependent suspension cocone on `P` over
`(f , g , h)` consists of dependent functions

```text
north : (t : unit) → P (f t)

south : (t : unit) → P (g t)
```

together with a family of dependent identifications

```text
merid : (x : X) → dependent-identification P (h x) ((north ∘ (terminal-map X)) x) (south ∘ (terminal-map X) x)
```

Using the [universal property of `unit`](foundation.unit-type.md) and the
previous characterization of suspension cocones (to be found in the file
[`synthetic-homotopy-theory.suspension-structures`](synthetic-homotopy-theory.suspension-structures.md)),
we can characterize dependent cocones over a suspension cocone as equivalent to
the following:

For a suspension structure `(N , S , m)`, a dependent suspension structure in
`P` over `(N , S , m)` is given by points

```text
north : P N

south : P S
```

and a family of dependent identifications

```text
meridian : (x : X) → dependent-identification P (m x) north south
```

## Definition

### Dependent Suspension Cocones

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  (c : suspension-cocone X Y)
  where

  dependent-suspension-cocone : UU (l1 ⊔ l3)
  dependent-suspension-cocone =
    dependent-cocone
      ( terminal-map X)
      ( terminal-map X)
      ( c)
      ( B)
```

### Dependent Suspension Structures

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2}
  (B : Y → UU l3)
  (c : suspension-structure X Y)
  where

  dependent-suspension-structure : UU (l1 ⊔ l3)
  dependent-suspension-structure =
    Σ ( B (north-suspension-structure c))
      ( λ N →
        Σ ( B (south-suspension-structure c))
          ( λ S →
            (x : X) →
            dependent-identification
              ( B)
              ( meridian-suspension-structure c x)
              ( N)
              ( S)))

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} {B : Y → UU l3}
  {c : suspension-structure X Y}
  (d : dependent-suspension-structure B c)
  where

  north-dependent-suspension-structure : B (north-suspension-structure c)
  north-dependent-suspension-structure = pr1 (d)

  south-dependent-suspension-structure : B (south-suspension-structure c)
  south-dependent-suspension-structure = (pr1 ∘ pr2) (d)

  meridian-dependent-suspension-structure :
    (x : X) →
    dependent-identification
      ( B)
      ( meridian-suspension-structure c x)
      ( north-dependent-suspension-structure)
      ( south-dependent-suspension-structure)
  meridian-dependent-suspension-structure = (pr2 ∘ pr2) (d)
```

## Properties

#### Equivalence between dependent suspension structures and dependent suspension cocones

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (c : suspension-structure X Y)
  (B : Y → UU l3)
  where

  dependent-cocone-dependent-suspension-structure :
    dependent-suspension-structure B c →
    dependent-suspension-cocone B (suspension-cocone-suspension-structure c)
  pr1 (dependent-cocone-dependent-suspension-structure d) t =
    north-dependent-suspension-structure d
  pr1 (pr2 (dependent-cocone-dependent-suspension-structure d)) t =
    south-dependent-suspension-structure d
  pr2 (pr2 (dependent-cocone-dependent-suspension-structure d)) x =
    meridian-dependent-suspension-structure d x

  equiv-dependent-suspension-structure-suspension-cocone :
    ( dependent-suspension-cocone
      ( B)
      ( suspension-cocone-suspension-structure c)) ≃
    ( dependent-suspension-structure B c)
  equiv-dependent-suspension-structure-suspension-cocone =
    ( equiv-Σ
      ( λ n →
        Σ ( B (south-suspension-structure c))
          ( λ s →
            (x : X) →
            ( dependent-identification
              ( B)
              ( meridian-suspension-structure c x)
              ( n)
              ( s))))
      ( equiv-dependent-universal-property-unit
        ( λ x → B (north-suspension-structure c)))
      ( λ north-suspension-c →
        ( equiv-Σ
          ( λ s →
            (x : X) →
            ( dependent-identification
              ( B)
              ( meridian-suspension-structure c x)
              ( map-equiv
                ( equiv-dependent-universal-property-unit
                  ( λ _ → B (north-suspension-structure c)))
                ( north-suspension-c))
              ( s)))
          ( equiv-dependent-universal-property-unit
            ( point (B (south-suspension-structure c))))
          ( λ south-suspension-c → id-equiv))))

  htpy-map-inv-equiv-dependent-suspension-structure-suspension-cocone-cocone-dependent-cocone-dependent-suspension-structure :
    map-inv-equiv equiv-dependent-suspension-structure-suspension-cocone ~
    dependent-cocone-dependent-suspension-structure
  htpy-map-inv-equiv-dependent-suspension-structure-suspension-cocone-cocone-dependent-cocone-dependent-suspension-structure
    ( d) =
      is-injective-equiv
        ( equiv-dependent-suspension-structure-suspension-cocone)
        ( is-section-map-inv-equiv
          ( equiv-dependent-suspension-structure-suspension-cocone)
          ( d))
```

#### Characterizing equality of dependent suspension structures

```agda
module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  {c : suspension-structure X Y}
  (d d' : dependent-suspension-structure B c)
  where

  htpy-dependent-suspension-structure : UU (l1 ⊔ l3)
  htpy-dependent-suspension-structure =
    Σ ( north-dependent-suspension-structure d ＝
        north-dependent-suspension-structure d')
      ( λ N-htpy →
        Σ ( south-dependent-suspension-structure d ＝
            south-dependent-suspension-structure d')
          ( λ S-htpy →
            (x : X) →
            coherence-square-identifications
              ( ap
                ( tr B (meridian-suspension-structure c x))
                ( N-htpy))
              ( meridian-dependent-suspension-structure d x)
              ( meridian-dependent-suspension-structure d' x)
              ( S-htpy)))

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  {susp-str : suspension-structure X Y}
  {d-susp-str0 d-susp-str1 : dependent-suspension-structure B susp-str}
  where

  north-htpy-dependent-suspension-structure :
    htpy-dependent-suspension-structure B d-susp-str0 d-susp-str1 →
    north-dependent-suspension-structure d-susp-str0 ＝
    north-dependent-suspension-structure d-susp-str1
  north-htpy-dependent-suspension-structure = pr1

  south-htpy-dependent-suspension-structure :
    htpy-dependent-suspension-structure B d-susp-str0 d-susp-str1 →
    south-dependent-suspension-structure d-susp-str0 ＝
    south-dependent-suspension-structure d-susp-str1
  south-htpy-dependent-suspension-structure = (pr1 ∘ pr2)

  meridian-htpy-dependent-suspension-structure :
    ( d-susp-str :
      htpy-dependent-suspension-structure B d-susp-str0 d-susp-str1) →
    ( x : X) →
    coherence-square-identifications
      ( ap
        ( tr B (meridian-suspension-structure susp-str x))
        ( north-htpy-dependent-suspension-structure d-susp-str))
      ( meridian-dependent-suspension-structure d-susp-str0 x)
      ( meridian-dependent-suspension-structure d-susp-str1 x)
      ( south-htpy-dependent-suspension-structure d-susp-str)
  meridian-htpy-dependent-suspension-structure = pr2 ∘ pr2

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  {c : suspension-structure X Y}
  (d : dependent-suspension-structure B c)
  where

  extensionality-dependent-suspension-structure :
    ( d' : dependent-suspension-structure B c) →
    ( d ＝ d') ≃
    ( htpy-dependent-suspension-structure B d d')
  extensionality-dependent-suspension-structure =
    extensionality-Σ
      ( λ (S , m) (N-htpy) →
        Σ (south-dependent-suspension-structure d ＝ S)
          ( λ S-htpy →
            (x : X) →
            coherence-square-identifications
              ( ap (tr B (meridian-suspension-structure c x)) N-htpy)
              ( meridian-dependent-suspension-structure d x)
              ( m x)
              ( S-htpy)))
      ( refl)
      ( refl , λ x → right-unit)
      ( λ N → id-equiv)
      ( extensionality-Σ
        ( λ m S-htpy →
          (x : X) →
          ( meridian-dependent-suspension-structure d x ∙ S-htpy) ＝
          ( m x))
        ( refl)
        ( λ x → right-unit)
        ( λ S → id-equiv)
        ( λ m →
          equiv-concat-htpy right-unit-htpy m ∘e inv-equiv equiv-eq-htpy))

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  {c : suspension-structure X Y}
  {d d' : dependent-suspension-structure B c}
  where

  htpy-eq-dependent-suspension-structure :
    (d ＝ d') →
    htpy-dependent-suspension-structure B d d'
  htpy-eq-dependent-suspension-structure =
    map-equiv
      ( extensionality-dependent-suspension-structure B d d')

  eq-htpy-dependent-suspension-structure :
    htpy-dependent-suspension-structure B d d' →
    d ＝ d'
  eq-htpy-dependent-suspension-structure =
    map-inv-equiv
      ( extensionality-dependent-suspension-structure B d d')

module _
  {l1 l2 l3 : Level} {X : UU l1} {Y : UU l2} (B : Y → UU l3)
  {c : suspension-structure X Y}
  (d : dependent-suspension-structure B c)
  where

  refl-htpy-dependent-suspension-structure :
    htpy-dependent-suspension-structure B d d
  pr1 refl-htpy-dependent-suspension-structure = refl
  pr1 (pr2 refl-htpy-dependent-suspension-structure) = refl
  pr2 (pr2 refl-htpy-dependent-suspension-structure) x = right-unit

  is-refl-refl-htpy-dependent-suspension-structure :
    refl-htpy-dependent-suspension-structure ＝
    htpy-eq-dependent-suspension-structure B refl
  is-refl-refl-htpy-dependent-suspension-structure = refl
```
