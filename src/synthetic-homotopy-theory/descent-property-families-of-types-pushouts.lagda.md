# The descent property for families of types over pushouts

```agda
module synthetic-homotopy-theory.descent-property-families-of-types-pushouts where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalence-extensionality
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-types
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.retractions
open import foundation.sections
open import foundation.span-diagrams
open import foundation.transport-along-identifications
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-span-diagrams
open import synthetic-homotopy-theory.equivalences-families-of-types-pushouts
open import synthetic-homotopy-theory.families-of-types-pushouts
open import synthetic-homotopy-theory.operations-cocones-under-span-diagrams
open import synthetic-homotopy-theory.universal-property-pushouts
```

</details>

## Idea

## Definitions

### The structure of a type family over a pushout obtained from a type family over a cocone

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X)
  (P : X → UU l5)
  where

  left-type-family-descent-data-type-family-pushout :
    domain-span-diagram s → UU l5
  left-type-family-descent-data-type-family-pushout =
    P ∘ left-map-cocone-span-diagram s c

  right-type-family-descent-data-type-family-pushout :
    codomain-span-diagram s → UU l5
  right-type-family-descent-data-type-family-pushout =
    P ∘ right-map-cocone-span-diagram s c

  matching-equiv-descent-data-type-family-pushout :
    (x : spanning-type-span-diagram s) →
    left-type-family-descent-data-type-family-pushout
      ( left-map-span-diagram s x) ≃
    right-type-family-descent-data-type-family-pushout
      ( right-map-span-diagram s x)
  matching-equiv-descent-data-type-family-pushout x =
    equiv-tr P (coherence-square-cocone-span-diagram s c x)

  descent-data-type-family-pushout :
    structure-type-family-pushout l5 s
  pr1 descent-data-type-family-pushout =
    left-type-family-descent-data-type-family-pushout
  pr1 (pr2 descent-data-type-family-pushout) =
    right-type-family-descent-data-type-family-pushout
  pr2 (pr2 descent-data-type-family-pushout) =
    matching-equiv-descent-data-type-family-pushout
```

## Theorem

### Theorem 18.2.3

```agda
structure-type-family-pushout-cocone-UU :
  {l1 l2 l3 : Level} (l : Level) (s : span-diagram l1 l2 l3) →
  cocone-span-diagram s (UU l) → structure-type-family-pushout l s
structure-type-family-pushout-cocone-UU l s =
  tot (λ PA → (tot (λ PB H s → equiv-eq (H s))))

is-equiv-structure-type-family-pushout-cocone-UU :
  {l1 l2 l3 : Level} (l : Level) (s : span-diagram l1 l2 l3) →
  is-equiv (structure-type-family-pushout-cocone-UU l s)
is-equiv-structure-type-family-pushout-cocone-UU l s =
  is-equiv-tot-is-fiberwise-equiv
    ( λ PA →
      is-equiv-tot-is-fiberwise-equiv
        ( λ PB →
          is-equiv-map-Π-is-fiberwise-equiv
            ( λ x →
              univalence
                ( PA (left-map-span-diagram s x))
                ( PB (right-map-span-diagram s x)))))

htpy-equiv-eq-ap-fam :
  {l1 l2 : Level} {A : UU l1} (B : A → UU l2) {x y : A}
  (p : x ＝ y) → htpy-equiv (equiv-tr B p) (equiv-eq (ap B p))
htpy-equiv-eq-ap-fam B {x} {.x} refl =
  refl-htpy-equiv id-equiv

module _
  {l1 l2 l3 l4 l5 : Level} (s : span-diagram l1 l2 l3)
  {X : UU l4} (c : cocone-span-diagram s X)
  where

  triangle-descent-data-type-family-pushout :
    coherence-triangle-maps
      ( descent-data-type-family-pushout {l5 = l5} s c)
      ( structure-type-family-pushout-cocone-UU l5 s)
      ( cocone-map-span-diagram s {Y = UU l5} c)
  triangle-descent-data-type-family-pushout P =
    eq-equiv-structure-type-family-pushout s
      ( descent-data-type-family-pushout s c P)
      ( structure-type-family-pushout-cocone-UU l5 s
        ( cocone-map-span-diagram s c P))
      ( pair
        ( λ a → id-equiv)
        ( pair
          ( λ b → id-equiv)
          ( λ x →
            htpy-equiv-eq-ap-fam P
              ( coherence-square-cocone-span-diagram s c x))))

  is-equiv-descent-data-type-family-pushout :
    universal-property-pushout s c →
    is-equiv (descent-data-type-family-pushout {l5 = l5} s c)
  is-equiv-descent-data-type-family-pushout up-c =
    is-equiv-left-map-triangle
      ( descent-data-type-family-pushout s c)
      ( structure-type-family-pushout-cocone-UU l5 s)
      ( cocone-map-span-diagram s c)
      ( triangle-descent-data-type-family-pushout)
      ( up-c (UU l5))
      ( is-equiv-structure-type-family-pushout-cocone-UU l5 s)

  equiv-descent-data-type-family-pushout :
    universal-property-pushout s c →
    (X → UU l5) ≃ structure-type-family-pushout l5 s
  pr1 (equiv-descent-data-type-family-pushout up-c) =
    descent-data-type-family-pushout s c
  pr2 (equiv-descent-data-type-family-pushout up-c) =
    is-equiv-descent-data-type-family-pushout up-c
```

## Properties

### Corollary 18.2.4

```agda
module _
  {l1 l2 l3 l4 l : Level} (s : span-diagram l1 l2 l3) {X : UU l4} (c : cocone-span-diagram s X)
  (U : universal-property-pushout s c)
  where

  uniqueness-structure-type-family-pushout :
    (P : structure-type-family-pushout l s) →
    is-contr
      ( Σ ( X → UU l)
          ( λ Q →
            equiv-structure-type-family-pushout s P
              ( descent-data-type-family-pushout s c Q)))
  uniqueness-structure-type-family-pushout P =
    is-contr-equiv'
      ( fiber (descent-data-type-family-pushout s c) P)
      ( equiv-tot
        ( λ Q →
          ( equiv-equiv-structure-type-family-pushout s P
            ( descent-data-type-family-pushout s c Q)) ∘e
        ( equiv-inv (descent-data-type-family-pushout s c Q) P)))
      ( is-contr-map-is-equiv
        ( is-equiv-descent-data-type-family-pushout s c U)
        ( P))

  fam-structure-type-family-pushout :
    structure-type-family-pushout l s → X → UU l
  fam-structure-type-family-pushout P =
    pr1 (center (uniqueness-structure-type-family-pushout P))

  is-section-fam-structure-type-family-pushout :
    is-section
      ( descent-data-type-family-pushout {l5 = l} s c)
      ( fam-structure-type-family-pushout)
  is-section-fam-structure-type-family-pushout P =
    inv
      ( eq-equiv-structure-type-family-pushout s
      ( P)
      ( descent-data-type-family-pushout s c
        ( fam-structure-type-family-pushout P))
      ( pr2 (center (uniqueness-structure-type-family-pushout P))))

  compute-left-fam-structure-type-family-pushout :
    (P : structure-type-family-pushout l s) →
    (a : domain-span-diagram s) →
    pr1 P a ≃ fam-structure-type-family-pushout P (pr1 c a)
  compute-left-fam-structure-type-family-pushout P =
    pr1 (pr2 (center (uniqueness-structure-type-family-pushout P)))

  compute-right-fam-structure-type-family-pushout :
    (P : structure-type-family-pushout l s) (b : codomain-span-diagram s) →
    pr1 (pr2 P) b ≃ fam-structure-type-family-pushout P (pr1 (pr2 c) b)
  compute-right-fam-structure-type-family-pushout P =
    pr1 (pr2 (pr2 (center (uniqueness-structure-type-family-pushout P))))

  compute-path-fam-structure-type-family-pushout :
    ( P : structure-type-family-pushout l s) →
    ( x : spanning-type-span-diagram s) →
      ( ( map-equiv
          ( compute-right-fam-structure-type-family-pushout P
            ( right-map-span-diagram s x))) ∘
        ( map-equiv (pr2 (pr2 P) x))) ~
      ( ( tr
          ( fam-structure-type-family-pushout P)
          ( pr2 (pr2 c) x)) ∘
        ( map-equiv
          ( compute-left-fam-structure-type-family-pushout P
            ( left-map-span-diagram s x))))
  compute-path-fam-structure-type-family-pushout P =
    pr2 (pr2 (pr2 (center (uniqueness-structure-type-family-pushout P))))
```
