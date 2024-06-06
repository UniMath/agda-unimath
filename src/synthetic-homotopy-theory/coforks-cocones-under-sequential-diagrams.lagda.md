# Correspondence between cocones under sequential diagrams and certain coforks

```agda
module synthetic-homotopy-theory.coforks-cocones-under-sequential-diagrams where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-prisms-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equivalences
open import foundation.equivalences-double-arrows
open import foundation.function-types
open import foundation.functoriality-dependent-pair-types
open import foundation.homotopies
open import foundation.morphisms-double-arrows
open import foundation.retractions
open import foundation.sections
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition
open import foundation.whiskering-homotopies-concatenation

open import synthetic-homotopy-theory.cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.coforks
open import synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams
open import synthetic-homotopy-theory.dependent-coforks
open import synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagrams
open import synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrows
open import synthetic-homotopy-theory.equivalences-sequential-diagrams
open import synthetic-homotopy-theory.morphisms-cocones-under-morphisms-sequential-diagrams
open import synthetic-homotopy-theory.morphisms-coforks-under-morphisms-double-arrows
open import synthetic-homotopy-theory.morphisms-sequential-diagrams
open import synthetic-homotopy-theory.sequential-diagrams
```

</details>

## Idea

A [sequential diagram](synthetic-homotopy-theory.sequential-diagrams.md)

```text
      a₀      a₁      a₂
  A₀ ───> A₁ ───> A₂ ───> ⋯
```

induces a [double arrow](foundation.double-arrows.md)

```text
  Σ (n : ℕ) Aₙ
      │ │
   id │ │ tot ₍₊₁₎ a
      │ │
      ∨ ∨
  Σ (n : ℕ) Aₙ
```

where `tot ₍₊₁₎ a` computes the successor on the base and applies the map
`aₙ : Aₙ → Aₙ₊₁` on the fiber.

[Morphisms](synthetic-homotopy-theory.morphisms-sequential-diagrams.md) and
[equivalences](synthetic-homotopy-theory.equivalences-sequential-diagrams.md) of
sequential diagrams induce [morphisms](foundation.morphisms-double-arrows.md)
and [equivalences](foundation.equivalences-double-arrows.md) of the
correseponding double arrows, respectively.

The data of a
[cocone](synthetic-homotopy-theory.cocones-under-sequential-diagrams.md) under
`A`:

```text
        aₙ
  Aₙ ──────> Aₙ₊₁
    ╲       ╱
     ╲  Hₙ ╱
   iₙ ╲   ╱ iₙ₊₁
       ∨ ∨
        X
```

can be [uncurried](foundation.dependent-pair-types.md) to get the equivalent
diagram comprising of the single triangle

```text
           tot ₍₊₁₎ a
  (Σ ℕ A) ────────────> (Σ ℕ A)
         ╲             ╱
           ╲         ╱
          i  ╲     ╱  i
               ∨ ∨
                X
```

which is exactly a [cofork](synthetic-homotopy-theory.coforks.md) of the
identity map and `tot ₍₊₁₎ a`.

Under this mapping
[sequential colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md)
correspond to
[coequalizers](synthetic-homotopy-theory.universal-property-coequalizers.md),
which is formalized in
[universal-property-sequential-colimits](synthetic-homotopy-theory.universal-property-sequential-colimits.md).

In the dependent setting,
[dependent cocones](synthetic-homotopy-theory.dependent-cocones-under-sequential-diagrams.md)
over a cocone `c` correspond to
[dependent coforks](synthetic-homotopy-theory.dependent-coforks.md) over the
cofork induced by `c`.

Additionally,
[morphisms](synthetic-homotopy-theory.morphisms-cocones-under-morphisms-sequential-diagrams.md)
of cocones under morphisms of sequential diagrams induce
[morphisms](synthetic-homotopy-theory.morphisms-coforks-under-morphisms-double-arrows.md)
of coforks under the induced morphisms of double arrows. It follows that
[equivalences](synthetic-homotopy-theory.equivalences-cocones-under-equivalences-sequential-diagrams.md)
of cocones under equivalences of sequential diagrams induce
[equivalences](synthetic-homotopy-theory.equivalences-coforks-under-equivalences-double-arrows.md)
of coforks under the induced equivalences of double arrows.

## Definitions

### Double arrows induced by sequential diagrams

```agda
module _
  {l1 : Level} (A : sequential-diagram l1)
  where

  left-map-cofork-cocone-sequential-diagram :
    Σ ℕ (family-sequential-diagram A) → Σ ℕ (family-sequential-diagram A)
  left-map-cofork-cocone-sequential-diagram = id

  right-map-cofork-cocone-sequential-diagram :
    Σ ℕ (family-sequential-diagram A) → Σ ℕ (family-sequential-diagram A)
  right-map-cofork-cocone-sequential-diagram (n , a) =
    (succ-ℕ n , map-sequential-diagram A n a)

  double-arrow-sequential-diagram : double-arrow l1 l1
  double-arrow-sequential-diagram =
    make-double-arrow
      ( left-map-cofork-cocone-sequential-diagram)
      ( right-map-cofork-cocone-sequential-diagram)
```

### Morphisms of double arrows induced by morphisms of sequential diagrams

```agda
module _
  {l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  where

  hom-double-arrow-hom-sequential-diagram :
    hom-sequential-diagram A B →
    hom-double-arrow
      ( double-arrow-sequential-diagram A)
      ( double-arrow-sequential-diagram B)
  pr1 (hom-double-arrow-hom-sequential-diagram h) =
    tot (map-hom-sequential-diagram B h)
  pr1 (pr2 (hom-double-arrow-hom-sequential-diagram h)) =
    tot (map-hom-sequential-diagram B h)
  pr1 (pr2 (pr2 (hom-double-arrow-hom-sequential-diagram h))) =
    refl-htpy
  pr2 (pr2 (pr2 (hom-double-arrow-hom-sequential-diagram h))) =
    coherence-square-maps-Σ
      ( family-sequential-diagram B)
      ( map-hom-sequential-diagram B h)
      ( map-sequential-diagram A)
      ( map-sequential-diagram B)
      ( map-hom-sequential-diagram B h)
      ( λ n → inv-htpy (naturality-map-hom-sequential-diagram B h n))
```

### Equivalences of double arrows induced by equivalences of sequential diagrams

```agda
module _
  {l1 l2 : Level} (A : sequential-diagram l1) (B : sequential-diagram l2)
  where

  equiv-double-arrow-equiv-sequential-diagram :
    equiv-sequential-diagram A B →
    equiv-double-arrow
      ( double-arrow-sequential-diagram A)
      ( double-arrow-sequential-diagram B)
  equiv-double-arrow-equiv-sequential-diagram e =
    equiv-hom-double-arrow
      ( double-arrow-sequential-diagram A)
      ( double-arrow-sequential-diagram B)
      ( hom-double-arrow-hom-sequential-diagram A B
        ( hom-equiv-sequential-diagram B e))
      ( is-equiv-tot-is-fiberwise-equiv
        ( is-equiv-map-equiv-sequential-diagram B e))
      ( is-equiv-tot-is-fiberwise-equiv
        ( is-equiv-map-equiv-sequential-diagram B e))
```

### Coforks induced by cocones under sequential diagrams

Further down we show that there is an inverse map, giving an equivalence between
cocones under a sequential diagram and coforks under the induced double arrow.

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  where

  cofork-cocone-sequential-diagram :
    cocone-sequential-diagram A X →
    cofork (double-arrow-sequential-diagram A) X
  pr1 (cofork-cocone-sequential-diagram c) =
    ind-Σ (map-cocone-sequential-diagram c)
  pr2 (cofork-cocone-sequential-diagram c) =
    ind-Σ (coherence-cocone-sequential-diagram c)
```

### Dependent coforks induced by dependent cocones under sequential diagrams

Further down we show that there is an inverse map, giving an equivalence between
dependent cocones over a cocone under a sequential diagram and dependent coforks
over the cofork induced by the base cocone.

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (P : X → UU l3)
  where

  dependent-cofork-dependent-cocone-sequential-diagram :
    dependent-cocone-sequential-diagram c P →
    dependent-cofork
      ( double-arrow-sequential-diagram A)
      ( cofork-cocone-sequential-diagram c)
      ( P)
  pr1 (dependent-cofork-dependent-cocone-sequential-diagram d) =
    ind-Σ (map-dependent-cocone-sequential-diagram P d)
  pr2 (dependent-cofork-dependent-cocone-sequential-diagram d) =
    ind-Σ (coherence-triangle-dependent-cocone-sequential-diagram P d)
```

### Morphisms of coforks under morphisms of double arrows induced by morphisms of cocones under morphisms of sequential diagrams

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : sequential-diagram l1} {X : UU l2} (c : cocone-sequential-diagram A X)
  {B : sequential-diagram l3} {Y : UU l4} (c' : cocone-sequential-diagram B Y)
  (h : hom-sequential-diagram A B)
  where

  coh-map-hom-cofork-hom-cocone-hom-sequential-diagram :
    (u : X → Y) →
    coherence-map-cocone-hom-cocone-hom-sequential-diagram c c' h u →
    coherence-map-cofork-hom-cofork-hom-double-arrow
      ( cofork-cocone-sequential-diagram c)
      ( cofork-cocone-sequential-diagram c')
      ( hom-double-arrow-hom-sequential-diagram A B h)
      ( u)
  coh-map-hom-cofork-hom-cocone-hom-sequential-diagram u H =
    inv-htpy (ind-Σ H)

  coh-hom-cofork-hom-cocone-hom-sequential-diagram :
    (u : X → Y) →
    (H : coherence-map-cocone-hom-cocone-hom-sequential-diagram c c' h u) →
    coherence-hom-cocone-hom-sequential-diagram c c' h u H →
    coherence-hom-cofork-hom-double-arrow
      ( cofork-cocone-sequential-diagram c)
      ( cofork-cocone-sequential-diagram c')
      ( hom-double-arrow-hom-sequential-diagram A B h)
      ( u)
      ( coh-map-hom-cofork-hom-cocone-hom-sequential-diagram u H)
  coh-hom-cofork-hom-cocone-hom-sequential-diagram u H K =
    ( right-whisker-concat-htpy
      ( right-unit-htpy)
      ( λ (n , a) →
        coherence-cocone-sequential-diagram c' n
          ( map-hom-sequential-diagram B h n a))) ∙h
    ( ind-Σ
      ( λ n →
        ( vertical-coherence-prism-inv-squares-maps-vertical-coherence-prism-maps
          ( map-cocone-sequential-diagram c n)
          ( map-cocone-sequential-diagram c (succ-ℕ n))
          ( map-sequential-diagram A n)
          ( map-cocone-sequential-diagram c' n)
          ( map-cocone-sequential-diagram c' (succ-ℕ n))
          ( map-sequential-diagram B n)
          ( map-hom-sequential-diagram B h n)
          ( map-hom-sequential-diagram B h (succ-ℕ n))
          ( u)
          ( coherence-cocone-sequential-diagram c n)
          ( H n)
          ( H (succ-ℕ n))
          ( naturality-map-hom-sequential-diagram B h n)
          ( coherence-cocone-sequential-diagram c' n)
          ( K n)) ∙h
        ( inv-htpy-assoc-htpy
          ( u ·l coherence-cocone-sequential-diagram c n)
          ( inv-htpy (H (succ-ℕ n) ·r map-sequential-diagram A n))
          ( ( map-cocone-sequential-diagram c' (succ-ℕ n)) ·l
            ( inv-htpy (naturality-map-hom-sequential-diagram B h n)))) ∙h
        ( left-whisker-concat-htpy _
          ( inv-htpy
            ( λ a →
              compute-ap-ind-Σ-eq-pair-eq-fiber
                ( map-cocone-sequential-diagram c')
                ( inv-htpy (naturality-map-hom-sequential-diagram B h n) a))))))

  hom-cofork-hom-cocone-hom-sequential-diagram :
    hom-cocone-hom-sequential-diagram c c' h →
    hom-cofork-hom-double-arrow
      ( cofork-cocone-sequential-diagram c)
      ( cofork-cocone-sequential-diagram c')
      ( hom-double-arrow-hom-sequential-diagram A B h)
  hom-cofork-hom-cocone-hom-sequential-diagram =
    tot
      ( λ u →
        map-Σ _
          ( coh-map-hom-cofork-hom-cocone-hom-sequential-diagram u)
          ( coh-hom-cofork-hom-cocone-hom-sequential-diagram u))
```

### Equivalences of coforks under equivalences of double arrows induced by equivalences of cocones under equivalences of sequential diagrams

```agda
module _
  {l1 l2 l3 l4 : Level}
  {A : sequential-diagram l1} {X : UU l2} (c : cocone-sequential-diagram A X)
  {B : sequential-diagram l3} {Y : UU l4} (c' : cocone-sequential-diagram B Y)
  (e : equiv-sequential-diagram A B)
  where

  equiv-cofork-equiv-cocone-equiv-sequential-diagram :
    equiv-cocone-equiv-sequential-diagram c c' e →
    equiv-cofork-equiv-double-arrow
      ( cofork-cocone-sequential-diagram c)
      ( cofork-cocone-sequential-diagram c')
      ( equiv-double-arrow-equiv-sequential-diagram A B e)
  equiv-cofork-equiv-cocone-equiv-sequential-diagram e' =
    equiv-hom-cofork-equiv-double-arrow
      ( cofork-cocone-sequential-diagram c)
      ( cofork-cocone-sequential-diagram c')
      ( equiv-double-arrow-equiv-sequential-diagram A B e)
      ( hom-cofork-hom-cocone-hom-sequential-diagram c c'
        ( hom-equiv-sequential-diagram B e)
        ( hom-equiv-cocone-equiv-sequential-diagram c c' e e'))
      ( is-equiv-map-equiv-cocone-equiv-sequential-diagram c c' e e')
```

## Properties

### The type of cocones under a sequential diagram is equivalent to the type of coforks under the induced double arrow

Furthermore, for every cocone `c` under `A` with vertex `X` there is a
[commuting triangle](foundation.commuting-triangles-of-maps.md)

```text
              cofork-map
      (X → Y) ──────────> cofork (double-arrow A) Y
            ╲             ╱
  cocone-map  ╲         ╱  cocone-cofork
                ╲     ╱
                 ∨   ∨
               cocone A Y .
```

```agda
module _
  {l1 l2 : Level} {A : sequential-diagram l1} {X : UU l2}
  where

  cocone-sequential-diagram-cofork :
    cofork (double-arrow-sequential-diagram A) X →
    cocone-sequential-diagram A X
  pr1 (cocone-sequential-diagram-cofork e) =
    ev-pair (map-cofork (double-arrow-sequential-diagram A) e)
  pr2 (cocone-sequential-diagram-cofork e) =
    ev-pair (coh-cofork (double-arrow-sequential-diagram A) e)

  abstract
    is-section-cocone-sequential-diagram-cofork :
      is-section
        ( cofork-cocone-sequential-diagram)
        ( cocone-sequential-diagram-cofork)
    is-section-cocone-sequential-diagram-cofork e =
      eq-htpy-cofork
        ( double-arrow-sequential-diagram A)
        ( cofork-cocone-sequential-diagram
          ( cocone-sequential-diagram-cofork e))
        ( e)
        ( refl-htpy-cofork _ _)

    is-retraction-cocone-sequential-diagram-cofork :
      is-retraction
        ( cofork-cocone-sequential-diagram)
        ( cocone-sequential-diagram-cofork)
    is-retraction-cocone-sequential-diagram-cofork c =
      eq-htpy-cocone-sequential-diagram A
        ( cocone-sequential-diagram-cofork
          ( cofork-cocone-sequential-diagram c))
        ( c)
        ( refl-htpy-cocone-sequential-diagram _ _)

  is-equiv-cocone-sequential-diagram-cofork :
    is-equiv cocone-sequential-diagram-cofork
  is-equiv-cocone-sequential-diagram-cofork =
    is-equiv-is-invertible
      ( cofork-cocone-sequential-diagram)
      ( is-retraction-cocone-sequential-diagram-cofork)
      ( is-section-cocone-sequential-diagram-cofork)

  equiv-cocone-sequential-diagram-cofork :
    cofork (double-arrow-sequential-diagram A) X ≃
    cocone-sequential-diagram A X
  pr1 equiv-cocone-sequential-diagram-cofork =
    cocone-sequential-diagram-cofork
  pr2 equiv-cocone-sequential-diagram-cofork =
    is-equiv-cocone-sequential-diagram-cofork

module _
  {l1 l2 : Level} {A : sequential-diagram l1}
  {X : UU l2} (c : cocone-sequential-diagram A X)
  where

  triangle-cocone-sequential-diagram-cofork :
    {l3 : Level} {Y : UU l3} →
    coherence-triangle-maps
      ( cocone-map-sequential-diagram c {Y = Y})
      ( cocone-sequential-diagram-cofork)
      ( cofork-map
        ( double-arrow-sequential-diagram A)
        ( cofork-cocone-sequential-diagram c))
  triangle-cocone-sequential-diagram-cofork h =
    eq-htpy-cocone-sequential-diagram A
      ( cocone-map-sequential-diagram c h)
      ( cocone-sequential-diagram-cofork
        ( cofork-map
          ( double-arrow-sequential-diagram A)
          ( cofork-cocone-sequential-diagram c)
          ( h)))
      ( refl-htpy-cocone-sequential-diagram _ _)
```

### The type of dependent cocones over a cocone is equivalent to the type of dependent coforks over the induced cofork

Furthermore, for every cocone `c` under `A` with vertex `X` there is a commuting
triangle

```text
                      dependent-cofork-map
      ((x : X) → P x) ───────────────────> dependent-cofork (cofork-cocone c) Y
                      ╲                  ╱
  dependent-cocone-map  ╲              ╱  dependent-cocone-dependent-cofork
                          ╲          ╱
                           ∨        ∨
                      dependent-cocone c P .
```

```agda
module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (P : X → UU l3)
  where

  dependent-cocone-sequential-diagram-dependent-cofork :
    dependent-cofork
      ( double-arrow-sequential-diagram A)
      ( cofork-cocone-sequential-diagram c)
      ( P) →
    dependent-cocone-sequential-diagram c P
  pr1 (dependent-cocone-sequential-diagram-dependent-cofork e) =
    ev-pair
      ( map-dependent-cofork
        ( double-arrow-sequential-diagram A)
        ( P)
        ( e))
  pr2 (dependent-cocone-sequential-diagram-dependent-cofork e) =
    ev-pair
      ( coherence-dependent-cofork
        ( double-arrow-sequential-diagram A)
        ( P)
        ( e))

  abstract
    is-section-dependent-cocone-sequential-diagram-dependent-cofork :
      is-section
        ( dependent-cofork-dependent-cocone-sequential-diagram P)
        ( dependent-cocone-sequential-diagram-dependent-cofork)
    is-section-dependent-cocone-sequential-diagram-dependent-cofork e =
      eq-htpy-dependent-cofork
        ( double-arrow-sequential-diagram A)
        ( P)
        ( dependent-cofork-dependent-cocone-sequential-diagram P
          ( dependent-cocone-sequential-diagram-dependent-cofork e))
        ( e)
        ( refl-htpy-dependent-cofork _ _ _)

    is-retraction-dependent-cocone-sequential-diagram-dependent-cofork :
      is-retraction
        ( dependent-cofork-dependent-cocone-sequential-diagram P)
        ( dependent-cocone-sequential-diagram-dependent-cofork)
    is-retraction-dependent-cocone-sequential-diagram-dependent-cofork d =
      eq-htpy-dependent-cocone-sequential-diagram P
        ( dependent-cocone-sequential-diagram-dependent-cofork
          ( dependent-cofork-dependent-cocone-sequential-diagram P d))
        ( d)
        ( refl-htpy-dependent-cocone-sequential-diagram _ _)

  is-equiv-dependent-cocone-sequential-diagram-dependent-cofork :
    is-equiv dependent-cocone-sequential-diagram-dependent-cofork
  is-equiv-dependent-cocone-sequential-diagram-dependent-cofork =
    is-equiv-is-invertible
      ( dependent-cofork-dependent-cocone-sequential-diagram P)
      ( is-retraction-dependent-cocone-sequential-diagram-dependent-cofork)
      ( is-section-dependent-cocone-sequential-diagram-dependent-cofork)

  equiv-dependent-cocone-sequential-diagram-dependent-cofork :
    dependent-cofork
      ( double-arrow-sequential-diagram A)
      ( cofork-cocone-sequential-diagram c)
      ( P) ≃
    dependent-cocone-sequential-diagram c P
  pr1 equiv-dependent-cocone-sequential-diagram-dependent-cofork =
    dependent-cocone-sequential-diagram-dependent-cofork
  pr2 equiv-dependent-cocone-sequential-diagram-dependent-cofork =
    is-equiv-dependent-cocone-sequential-diagram-dependent-cofork

module _
  {l1 l2 l3 : Level} {A : sequential-diagram l1}
  {X : UU l2} {c : cocone-sequential-diagram A X}
  (P : X → UU l3)
  where

  triangle-dependent-cocone-sequential-diagram-dependent-cofork :
    coherence-triangle-maps
      ( dependent-cocone-map-sequential-diagram c P)
      ( dependent-cocone-sequential-diagram-dependent-cofork P)
      ( dependent-cofork-map
        ( double-arrow-sequential-diagram A)
        ( cofork-cocone-sequential-diagram c))
  triangle-dependent-cocone-sequential-diagram-dependent-cofork h =
    eq-htpy-dependent-cocone-sequential-diagram P
      ( dependent-cocone-map-sequential-diagram c P h)
      ( dependent-cocone-sequential-diagram-dependent-cofork P
        ( dependent-cofork-map
          ( double-arrow-sequential-diagram A)
          ( cofork-cocone-sequential-diagram c)
          ( h)))
      ( refl-htpy-dependent-cocone-sequential-diagram _ _)
```
