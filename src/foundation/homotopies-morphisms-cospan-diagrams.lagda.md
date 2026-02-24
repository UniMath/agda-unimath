# Homotopies of morphisms of cospan diagrams

```agda
module foundation.homotopies-morphisms-cospan-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-homotopies
open import foundation.cospan-diagrams
open import foundation.dependent-pair-types
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.morphisms-cospan-diagrams
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.cartesian-product-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.homotopies
```

</details>

## Idea

Given two [cospan diagrams](foundation.cospan-diagrams.md) `𝒮` and `𝒯`, and two
[morphisms](foundation.morphisms-cospan-diagrams.md) between them `h` and `h'`,

```text
         f             g                             f             g
  A ----------> X <---------- B               A ----------> X <---------- B
  |             |             |               |             |             |
  | hA   H      | hX   K      | hB   and      | hA'  H'     | hX'  K'     | hB'
  ∨             ∨             ∨               ∨             ∨             ∨
  A' ---------> X' <--------- B'              A' ---------> X' <--------- B',
         f'            g'                            f'            g'
```

a
{{#concept "homotopy" Disambiguation="of morphisms of cospan diagrams of types" Agda=htpy-hom-cospan-diagram}}
`h ~ h'` consists of pairwise homotopies of the vertical maps, such that the
left and right diagrams commute:

```text
  f' ∘ hA --------> f' ∘ hA'        g' ∘ hB --------> g' ∘ hB'
     |                 |               |                 |
   H |                 | H'   and    K |                 | K'
     ∨                 ∨               ∨                 ∨
  hX ∘ f --------> hX' ∘ f          hX ∘ g --------> hX' ∘ g.
```

## Definitions

### Homotopies of morphisms of cospan diagrams

```agda
module _
  {l1 l2 l3 l1' l2' l3' : Level}
  (𝒮 : cospan-diagram l1 l2 l3)
  (𝒯 : cospan-diagram l1' l2' l3')
  where

  left-square-coherence-htpy-hom-cospan-diagram :
    (h h' : hom-cospan-diagram 𝒮 𝒯) →
    map-domain-hom-cospan-diagram 𝒮 𝒯 h ~
    map-domain-hom-cospan-diagram 𝒮 𝒯 h' →
    cospanning-map-hom-cospan-diagram 𝒮 𝒯 h ~
    cospanning-map-hom-cospan-diagram 𝒮 𝒯 h' → UU (l1 ⊔ l3')
  left-square-coherence-htpy-hom-cospan-diagram h h' L C =
    coherence-square-homotopies
      ( left-map-cospan-diagram 𝒯 ·l L)
      ( left-square-hom-cospan-diagram 𝒮 𝒯 h)
      ( left-square-hom-cospan-diagram 𝒮 𝒯 h')
      ( C ·r left-map-cospan-diagram 𝒮)

  right-square-coherence-htpy-hom-cospan-diagram :
    (h h' : hom-cospan-diagram 𝒮 𝒯) →
    map-codomain-hom-cospan-diagram 𝒮 𝒯 h ~
    map-codomain-hom-cospan-diagram 𝒮 𝒯 h' →
    cospanning-map-hom-cospan-diagram 𝒮 𝒯 h ~
    cospanning-map-hom-cospan-diagram 𝒮 𝒯 h' → UU (l2 ⊔ l3')
  right-square-coherence-htpy-hom-cospan-diagram h h' R C =
    coherence-square-homotopies
      ( right-map-cospan-diagram 𝒯 ·l R)
      ( right-square-hom-cospan-diagram 𝒮 𝒯 h)
      ( right-square-hom-cospan-diagram 𝒮 𝒯 h')
      ( C ·r right-map-cospan-diagram 𝒮)

  coherence-htpy-hom-cospan-diagram :
    (h h' : hom-cospan-diagram 𝒮 𝒯) →
    map-domain-hom-cospan-diagram 𝒮 𝒯 h ~
    map-domain-hom-cospan-diagram 𝒮 𝒯 h' →
    map-codomain-hom-cospan-diagram 𝒮 𝒯 h ~
    map-codomain-hom-cospan-diagram 𝒮 𝒯 h' →
    cospanning-map-hom-cospan-diagram 𝒮 𝒯 h ~
    cospanning-map-hom-cospan-diagram 𝒮 𝒯 h' → UU (l1 ⊔ l2 ⊔ l3')
  coherence-htpy-hom-cospan-diagram h h' L R C =
    ( left-square-coherence-htpy-hom-cospan-diagram h h' L C) ×
    ( right-square-coherence-htpy-hom-cospan-diagram h h' R C)

  htpy-hom-cospan-diagram :
    (h h' : hom-cospan-diagram 𝒮 𝒯) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l1' ⊔ l2' ⊔ l3')
  htpy-hom-cospan-diagram h h' =
    Σ ( map-domain-hom-cospan-diagram 𝒮 𝒯 h ~
        map-domain-hom-cospan-diagram 𝒮 𝒯 h')
      ( λ L →
        Σ ( map-codomain-hom-cospan-diagram 𝒮 𝒯 h ~
            map-codomain-hom-cospan-diagram 𝒮 𝒯 h')
          ( λ R →
            Σ ( cospanning-map-hom-cospan-diagram 𝒮 𝒯 h ~
                cospanning-map-hom-cospan-diagram 𝒮 𝒯 h')
              ( λ C → coherence-htpy-hom-cospan-diagram h h' L R C)))

module _
  {l1 l2 l3 l1' l2' l3' : Level}
  (𝒮 : cospan-diagram l1 l2 l3)
  (𝒯 : cospan-diagram l1' l2' l3')
  (h h' : hom-cospan-diagram 𝒮 𝒯)
  (H : htpy-hom-cospan-diagram 𝒮 𝒯 h h')
  where

  htpy-left-map-htpy-hom-cospan-diagram :
    map-domain-hom-cospan-diagram 𝒮 𝒯 h ~
    map-domain-hom-cospan-diagram 𝒮 𝒯 h'
  htpy-left-map-htpy-hom-cospan-diagram = pr1 H

  htpy-right-map-htpy-hom-cospan-diagram :
    map-codomain-hom-cospan-diagram 𝒮 𝒯 h ~
    map-codomain-hom-cospan-diagram 𝒮 𝒯 h'
  htpy-right-map-htpy-hom-cospan-diagram = pr1 (pr2 H)

  htpy-cospanning-map-htpy-hom-cospan-diagram :
    cospanning-map-hom-cospan-diagram 𝒮 𝒯 h ~
    cospanning-map-hom-cospan-diagram 𝒮 𝒯 h'
  htpy-cospanning-map-htpy-hom-cospan-diagram = pr1 (pr2 (pr2 H))

  coh-htpy-hom-cospan-diagram :
    coherence-htpy-hom-cospan-diagram 𝒮 𝒯 h h'
      ( htpy-left-map-htpy-hom-cospan-diagram)
      ( htpy-right-map-htpy-hom-cospan-diagram)
      ( htpy-cospanning-map-htpy-hom-cospan-diagram)
  coh-htpy-hom-cospan-diagram = pr2 (pr2 (pr2 H))

  left-square-coh-htpy-hom-cospan-diagram :
    left-square-coherence-htpy-hom-cospan-diagram 𝒮 𝒯 h h'
      ( htpy-left-map-htpy-hom-cospan-diagram)
      ( htpy-cospanning-map-htpy-hom-cospan-diagram)
  left-square-coh-htpy-hom-cospan-diagram = pr1 coh-htpy-hom-cospan-diagram

  right-square-coh-htpy-hom-cospan-diagram :
    right-square-coherence-htpy-hom-cospan-diagram 𝒮 𝒯 h h'
      ( htpy-right-map-htpy-hom-cospan-diagram)
      ( htpy-cospanning-map-htpy-hom-cospan-diagram)
  right-square-coh-htpy-hom-cospan-diagram = pr2 coh-htpy-hom-cospan-diagram
```

## Properties

### Homotopies of morphisms of cospan diagrams characterize identifications of morphisms of cospan diagrams

```agda
module _
  {l1 l2 l3 l1' l2' l3' : Level}
  (𝒮 : cospan-diagram l1 l2 l3)
  (𝒯 : cospan-diagram l1' l2' l3')
  where

  refl-htpy-hom-cospan-diagram :
    (h : hom-cospan-diagram 𝒮 𝒯) → htpy-hom-cospan-diagram 𝒮 𝒯 h h
  refl-htpy-hom-cospan-diagram h =
    ( refl-htpy , refl-htpy , refl-htpy , right-unit-htpy , right-unit-htpy)

  htpy-eq-hom-cospan-diagram :
    (h h' : hom-cospan-diagram 𝒮 𝒯) → h ＝ h' → htpy-hom-cospan-diagram 𝒮 𝒯 h h'
  htpy-eq-hom-cospan-diagram h .h refl = refl-htpy-hom-cospan-diagram h

  is-torsorial-htpy-hom-cospan-diagram :
    (h : hom-cospan-diagram 𝒮 𝒯) → is-torsorial (htpy-hom-cospan-diagram 𝒮 𝒯 h)
  is-torsorial-htpy-hom-cospan-diagram h =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (map-domain-hom-cospan-diagram 𝒮 𝒯 h))
      ( map-domain-hom-cospan-diagram 𝒮 𝒯 h , refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-torsorial-htpy (map-codomain-hom-cospan-diagram 𝒮 𝒯 h))
        ( map-codomain-hom-cospan-diagram 𝒮 𝒯 h , refl-htpy)
        ( is-torsorial-Eq-structure
          ( is-torsorial-htpy (cospanning-map-hom-cospan-diagram 𝒮 𝒯 h))
          ( cospanning-map-hom-cospan-diagram 𝒮 𝒯 h , refl-htpy)
          ( is-torsorial-Eq-structure
            ( is-torsorial-htpy
              ( left-square-hom-cospan-diagram 𝒮 𝒯 h ∙h refl-htpy))
            ( left-square-hom-cospan-diagram 𝒮 𝒯 h ∙h refl-htpy , refl-htpy)
            ( is-torsorial-htpy
              ( right-square-hom-cospan-diagram 𝒮 𝒯 h ∙h refl-htpy)))))

  is-equiv-htpy-eq-hom-cospan-diagram :
    (h h' : hom-cospan-diagram 𝒮 𝒯) → is-equiv (htpy-eq-hom-cospan-diagram h h')
  is-equiv-htpy-eq-hom-cospan-diagram h =
    fundamental-theorem-id
      ( is-torsorial-htpy-hom-cospan-diagram h)
      ( htpy-eq-hom-cospan-diagram h)

  extensionality-hom-cospan-diagram :
    (h h' : hom-cospan-diagram 𝒮 𝒯) →
    (h ＝ h') ≃ htpy-hom-cospan-diagram 𝒮 𝒯 h h'
  extensionality-hom-cospan-diagram h h' =
    ( htpy-eq-hom-cospan-diagram h h' ,
      is-equiv-htpy-eq-hom-cospan-diagram h h')

  eq-htpy-hom-cospan-diagram :
    (h h' : hom-cospan-diagram 𝒮 𝒯) → htpy-hom-cospan-diagram 𝒮 𝒯 h h' → h ＝ h'
  eq-htpy-hom-cospan-diagram h h' =
    map-inv-is-equiv (is-equiv-htpy-eq-hom-cospan-diagram h h')
```
