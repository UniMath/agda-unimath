# Descent property of coequalizers

```agda
module synthetic-homotopy-theory.descent-property-coequalizers where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-maps
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equality-dependent-pair-types
open import foundation.equivalences
open import foundation.fibers-of-maps
open import foundation.function-extensionality
open import foundation.functoriality-dependent-function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.identity-types
open import foundation.univalence
open import foundation.universe-levels

open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.descent-data-coequalizers
open import synthetic-homotopy-theory.equivalences-descent-data-coequalizers
open import synthetic-homotopy-theory.families-descent-data-coequalizers
open import synthetic-homotopy-theory.universal-property-coequalizers
```

</details>

## Idea

The
{{#concept "descent property" Disambiguation="coequalizers" Agda=uniqueness-descent-data-coequalizer}}
of [coequalizers](synthetic-homotopy-theory.coequalizers.md) characterizes type
families over coequalizers as
[descent data](synthetic-homotopy-theory.descent-data-coequalizers.md) over the
base [double arrow](foundation.double-arrows.md).

Given a double arrow `f, g : A → B` and a
[cofork](synthetic-homotopy-theory.coforks.md) with vertex `X`, there is a
[commuting triangle](foundation.commuting-triangles-of-maps.md)

```text
          cofork-map
  (X → 𝒰) ---------> cofork A 𝒰
           \       /
            \     /
             \   /
              ∨ ∨
         descent-data A .
```

From [univalence](foundation-core.univalence.md) it follows that the right map
is an equivalence. If `X` is a coequalizer of `f, g`, then we have that the top
map is an equivalence, which imples that the left map is an equivalence.

## Theorem

```agda
module _
  {l1 l2 : Level} {F : double-arrow l1 l2}
  where

  equiv-descent-data-cofork :
    {l3 : Level} → cofork F (UU l3) ≃ descent-data-coequalizer F l3
  equiv-descent-data-cofork =
    equiv-tot (λ P → equiv-Π-equiv-family (λ a → equiv-univalence))

  descent-data-cofork :
    {l3 : Level} → cofork F (UU l3) → descent-data-coequalizer F l3
  descent-data-cofork =
    map-equiv equiv-descent-data-cofork

  is-equiv-descent-data-cofork :
    {l3 : Level} → is-equiv (descent-data-cofork {l3})
  is-equiv-descent-data-cofork =
    is-equiv-map-equiv equiv-descent-data-cofork

module _
  {l1 l2 l3 : Level} {F : double-arrow l1 l2}
  {X : UU l3} (c : cofork F X)
  where

  triangle-descent-data-family-cofork :
    {l4 : Level} →
    coherence-triangle-maps
      ( descent-data-family-cofork c)
      ( descent-data-cofork)
      ( cofork-map c {Y = UU l4})
  triangle-descent-data-family-cofork P =
    eq-pair-eq-fiber
      ( eq-htpy (λ a → inv (compute-equiv-eq-ap (coh-cofork c a))))

module _
  {l1 l2 l3 : Level} {F : double-arrow l1 l2}
  {X : UU l3} {c : cofork F X}
  (up-c : universal-property-coequalizer c)
  where

  is-equiv-descent-data-family-cofork :
    {l4 : Level} →
    is-equiv (descent-data-family-cofork c {l4})
  is-equiv-descent-data-family-cofork {l4} =
    is-equiv-left-map-triangle
      ( descent-data-family-cofork c)
      ( descent-data-cofork)
      ( cofork-map c)
      ( triangle-descent-data-family-cofork c)
      ( up-c (UU l4))
      ( is-equiv-descent-data-cofork)

module _
  {l1 l2 l3 l4 : Level} {F : double-arrow l1 l2}
  {X : UU l3} {c : cofork F X}
  (up-c : universal-property-coequalizer c)
  (P : descent-data-coequalizer F l4)
  where

  abstract
    uniqueness-descent-data-coequalizer :
      is-contr
        ( Σ ( X → UU l4)
            ( λ Q →
              equiv-descent-data-coequalizer
                ( descent-data-family-cofork c Q)
                ( P)))
    uniqueness-descent-data-coequalizer =
      is-contr-equiv'
        ( fiber (descent-data-family-cofork c) P)
        ( equiv-tot
          ( λ Q →
            extensionality-descent-data-coequalizer
              ( descent-data-family-cofork c Q)
              ( P)))
        ( is-contr-map-is-equiv
          ( is-equiv-descent-data-family-cofork up-c)
          ( P))

  family-cofork-descent-data-coequalizer : X → UU l4
  family-cofork-descent-data-coequalizer =
    pr1 (center uniqueness-descent-data-coequalizer)

  family-with-descent-data-coequalizer-descent-data-coequalizer :
    family-with-descent-data-coequalizer c l4
  pr1 family-with-descent-data-coequalizer-descent-data-coequalizer =
    family-cofork-descent-data-coequalizer
  pr1 (pr2 family-with-descent-data-coequalizer-descent-data-coequalizer) =
    P
  pr2 (pr2 family-with-descent-data-coequalizer-descent-data-coequalizer) =
    pr2 (center uniqueness-descent-data-coequalizer)
```
