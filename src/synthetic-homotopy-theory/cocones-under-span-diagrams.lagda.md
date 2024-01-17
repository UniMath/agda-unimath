# Cocones under span diagrams

```agda
module synthetic-homotopy-theory.cocones-under-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-homotopies
open import foundation.constant-span-diagrams
open import foundation.dependent-pair-types
open import foundation.equivalences-arrows
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.morphisms-arrows
open import foundation.morphisms-span-diagrams
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.universe-levels
open import foundation.whiskering-homotopies

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.function-extensionality
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
```

</details>

## Idea

A {{#concept "cocone" Agda=cocone-span-diagram Disambiguation="span diagram"}}
under a [span diagram](foundation.span-diagrams.md) `A <-f- S -g-> B` with
codomain `X` consists of two maps `i : A → X` and `j : B → X` equipped with a
[homotopy](foundation.homotopies.md) witnessing that the square

```text
        g
    S -----> B
    |        |
  f |        | j
    V        V
    A -----> X
        i
```

[commutes](foundation.commuting-squares-of-maps.md).

[Equivalently](foundation-core.equivalences.md), a cocone with codomain `X`
under a span diagram `𝒮` given by `A <-f- S -g-> B` can be described as a
[morphism of span diagrams](foundation.morphisms-span-diagrams.md) from `𝒮` into
the [constant span diagram](foundation.constant-span-diagrams.md) at `X`. In
other words, a cocone under `𝒮` with codomain `X` is a commuting diagram of the
form

```text
         f       g
    A <----- S -----> B
    |        |        |
  i |        | h      | j
    V        V        V
    X ====== X ====== X.
```

It is immediate from the definition of a cocone on a span that any commuting
square of maps, or any [morphism of arrows](foundation.morphisms-arrows.md) can
be presented equivalently as a cocone on a span.

## Definitions

### Cocones under span diagrams

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  where

  cocone-span-diagram :
    UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-span-diagram X =
    Σ ( domain-span-diagram 𝒮 → X)
      ( λ i →
        Σ ( codomain-span-diagram 𝒮 → X)
          ( λ j →
            coherence-square-maps
              ( right-map-span-diagram 𝒮)
              ( left-map-span-diagram 𝒮)
              ( j)
              ( i)))

  module _
    {X : UU l4} (c : cocone-span-diagram X)
    where

    left-map-cocone-span-diagram : domain-span-diagram 𝒮 → X
    left-map-cocone-span-diagram = pr1 c

    right-map-cocone-span-diagram : codomain-span-diagram 𝒮 → X
    right-map-cocone-span-diagram = pr1 (pr2 c)

    coherence-square-cocone-span-diagram :
      coherence-square-maps
        ( right-map-span-diagram 𝒮)
        ( left-map-span-diagram 𝒮)
        ( right-map-cocone-span-diagram)
        ( left-map-cocone-span-diagram)
    coherence-square-cocone-span-diagram = pr2 (pr2 c)
```

### Alternative definition of cocones under span diagrams

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3)
  where

  cocone-span-diagram' : UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-span-diagram' X = hom-span-diagram 𝒮 (constant-span-diagram X)
```

### Cocones obtained from morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : hom-arrow f g)
  where

  cocone-hom-arrow : cocone-span-diagram (span-diagram-hom-arrow f g h) Y
  pr1 cocone-hom-arrow = map-codomain-hom-arrow f g h
  pr1 (pr2 cocone-hom-arrow) = g
  pr2 (pr2 cocone-hom-arrow) = coh-hom-arrow f g h
```

### Cocones obtained from equivalences of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (e : equiv-arrow f g)
  where

  cocone-equiv-arrow : cocone-span-diagram (span-diagram-equiv-arrow f g e) Y
  cocone-equiv-arrow = cocone-hom-arrow f g (hom-equiv-arrow f g e)
```

### Homotopies of cocones under span diagrams

Given two cocones `c` and `c'` on a span diagram `𝒮`, both with the same
codomain `X`, we also introduce homotopies of cocones under span diagrams. A
{{#concept "homotopy of cocones under a span diagram" Agda=htpy-cocone-span-diagram}}
from `c := (i , j , H)` to `c' := (i' , j' , H')` under a span diagram
`A <-f- S -g-> B` consists of two homotopies `K : i ~ i'` and `L : j ~ j'` and a
homotopy `M` witnessing that the square of homotopies

```text
         K · f
  i ∘ f -------> i' ∘ f
    |               |
  H |      M        | H'
    V               V
  j ∘ g -------> j' ∘ g
         L · g
```

[commutes](foundation.commuting-squares-homotopies.md).

```agda
module _
  {l1 l2 l3 l4 : Level} (𝒮 : span-diagram l1 l2 l3) {X : UU l4}
  where

  statement-coherence-htpy-cocone-span-diagram :
    (c c' : cocone-span-diagram 𝒮 X) →
    (K :
      left-map-cocone-span-diagram 𝒮 c ~
      left-map-cocone-span-diagram 𝒮 c')
    (L :
      right-map-cocone-span-diagram 𝒮 c ~
      right-map-cocone-span-diagram 𝒮 c') →
    UU (l3 ⊔ l4)
  statement-coherence-htpy-cocone-span-diagram c c' K L =
    coherence-square-homotopies
      ( K ·r left-map-span-diagram 𝒮)
      ( coherence-square-cocone-span-diagram 𝒮 c)
      ( coherence-square-cocone-span-diagram 𝒮 c')
      ( L ·r right-map-span-diagram 𝒮)

  htpy-cocone-span-diagram :
    (c c' : cocone-span-diagram 𝒮 X) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-cocone-span-diagram c c' =
    Σ ( left-map-cocone-span-diagram 𝒮 c ~
        left-map-cocone-span-diagram 𝒮 c')
      ( λ K →
        Σ ( right-map-cocone-span-diagram 𝒮 c ~
            right-map-cocone-span-diagram 𝒮 c')
          ( statement-coherence-htpy-cocone-span-diagram c c' K))

  module _
    (c c' : cocone-span-diagram 𝒮 X) (H : htpy-cocone-span-diagram c c')
    where

    left-htpy-cocone-span-diagram :
      left-map-cocone-span-diagram 𝒮 c ~
      left-map-cocone-span-diagram 𝒮 c'
    left-htpy-cocone-span-diagram = pr1 H

    right-htpy-cocone-span-diagram :
      right-map-cocone-span-diagram 𝒮 c ~
      right-map-cocone-span-diagram 𝒮 c'
    right-htpy-cocone-span-diagram = pr1 (pr2 H)

    coherence-htpy-cocone-span-diagram :
      statement-coherence-htpy-cocone-span-diagram c c'
        ( left-htpy-cocone-span-diagram)
        ( right-htpy-cocone-span-diagram)
    coherence-htpy-cocone-span-diagram = pr2 (pr2 H)

  refl-htpy-cocone-span-diagram :
    (c : cocone-span-diagram 𝒮 X) → htpy-cocone-span-diagram c c
  pr1 (refl-htpy-cocone-span-diagram (i , j , H)) = refl-htpy
  pr1 (pr2 (refl-htpy-cocone-span-diagram (i , j , H))) = refl-htpy
  pr2 (pr2 (refl-htpy-cocone-span-diagram (i , j , H))) = right-unit-htpy

  htpy-eq-cocone-span-diagram :
    (c c' : cocone-span-diagram 𝒮 X) → c ＝ c' → htpy-cocone-span-diagram c c'
  htpy-eq-cocone-span-diagram c .c refl = refl-htpy-cocone-span-diagram c

  is-torsorial-htpy-cocone-span-diagram :
    (c : cocone-span-diagram 𝒮 X) → is-torsorial (htpy-cocone-span-diagram c)
  is-torsorial-htpy-cocone-span-diagram c =
    is-torsorial-Eq-structure
      ( is-torsorial-htpy (left-map-cocone-span-diagram 𝒮 c))
      ( left-map-cocone-span-diagram 𝒮 c , refl-htpy)
      ( is-torsorial-Eq-structure
        ( is-torsorial-htpy (right-map-cocone-span-diagram 𝒮 c))
        ( right-map-cocone-span-diagram 𝒮 c , refl-htpy)
        ( is-contr-is-equiv'
          ( Σ ( ( left-map-cocone-span-diagram 𝒮 c ∘
                  left-map-span-diagram 𝒮) ~
                ( right-map-cocone-span-diagram 𝒮 c ∘
                  right-map-span-diagram 𝒮))
              ( λ H' → coherence-square-cocone-span-diagram 𝒮 c ~ H'))
          ( tot (λ H' M → right-unit-htpy ∙h M))
          ( is-equiv-tot-is-fiberwise-equiv (λ H' → is-equiv-concat-htpy _ _))
          ( is-torsorial-htpy (coherence-square-cocone-span-diagram 𝒮 c))))

  is-equiv-htpy-eq-cocone-span-diagram :
    (c c' : cocone-span-diagram 𝒮 X) →
    is-equiv (htpy-eq-cocone-span-diagram c c')
  is-equiv-htpy-eq-cocone-span-diagram c =
    fundamental-theorem-id
      ( is-torsorial-htpy-cocone-span-diagram c)
      ( htpy-eq-cocone-span-diagram c)

  extensionality-cocone-span-diagram :
    (c c' : cocone-span-diagram 𝒮 X) → (c ＝ c') ≃ htpy-cocone-span-diagram c c'
  pr1 (extensionality-cocone-span-diagram c c') =
    htpy-eq-cocone-span-diagram c c'
  pr2 (extensionality-cocone-span-diagram c c') =
    is-equiv-htpy-eq-cocone-span-diagram c c'

  eq-htpy-cocone-span-diagram :
    (c c' : cocone-span-diagram 𝒮 X) → htpy-cocone-span-diagram c c' → c ＝ c'
  eq-htpy-cocone-span-diagram c c' =
    map-inv-is-equiv (is-equiv-htpy-eq-cocone-span-diagram c c')
```

## See also

- In
  [Operations on cocones under span diagrams](synthetic-homotopy-theory.operations-cocones-under-span-diagrams.md)
  we define several ways of constructing cocones under span diagrams from given
  cocones under span diagrams,
  [morphisms of arrows](foundation.morphisms-arrows.md),
  [equivalences of arrows](foundation.equivalences-arrows.md),
  [morphisms of span diagrams](foundation.morphisms-span-diagrams.md),
  [equivalences of span diagrams](foundation.equivalences-span-diagrams.md), and
  so on.
