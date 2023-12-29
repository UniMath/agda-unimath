# Cocones under spans

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

A {{#concept "cocone" Agda=cocone-span-diagram Disambiguation="span diagram"}} under a
[span diagram](foundation.span-diagrams.md) `A <-f- S -g-> B` with codomain `X` consists of two
maps `i : A → X` and `j : B → X` equipped with a
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
under a span diagram `s` given by `A <-f- S -g-> B` can be described as a
[morphism of span diagrams](foundation.morphisms-span-diagrams.md) from `s` into the [constant span diagram](foundation.constant-span-diagrams.md) at `X`. In other words, a cocone under `s` with codomain `X` is a commuting
diagram of the form

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
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  where

  cocone-span-diagram :
    UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-span-diagram X =
    Σ ( domain-span-diagram s → X)
      ( λ i →
        Σ ( codomain-span-diagram s → X)
          ( λ j →
            coherence-square-maps
              ( right-map-span-diagram s)
              ( left-map-span-diagram s)
              ( j)
              ( i)))

  module _
    {X : UU l4} (c : cocone-span-diagram X)
    where

    horizontal-map-cocone-span-diagram : domain-span-diagram s → X
    horizontal-map-cocone-span-diagram = pr1 c

    vertical-map-cocone-span-diagram : codomain-span-diagram s → X
    vertical-map-cocone-span-diagram = pr1 (pr2 c)

    coherence-square-cocone-span-diagram :
      coherence-square-maps
        ( right-map-span-diagram s)
        ( left-map-span-diagram s)
        ( vertical-map-cocone-span-diagram)
        ( horizontal-map-cocone-span-diagram)
    coherence-square-cocone-span-diagram = pr2 (pr2 c)
```

### Alternative definition of cocones under span diagrams

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3)
  where

  cocone-span-diagram' : UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-span-diagram' X = hom-span-diagram s (constant-span-diagram X)
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

Given two cocones `c` and `c'` on a span diagram `s`, both with the same codomain `X`,
we also introduce homotopies of cocones under span diagrams. A
{{#concept "homotopy of cocones under a span diagram" Agda=htpy-cocone-span-diagram}} from
`c := (i , j , H)` to `c' := (i' , j' , H')` under a span diagram `A <-f- S -g-> B`
consists of two homotopies `K : i ~ i'` and `L : j ~ j'` and a homotopy `M`
witnessing that the square of homotopies

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
  {l1 l2 l3 l4 : Level} (s : span-diagram l1 l2 l3) {X : UU l4}
  where

  statement-coherence-htpy-cocone-span-diagram :
    (c c' : cocone-span-diagram s X) →
    (K :
      horizontal-map-cocone-span-diagram s c ~
      horizontal-map-cocone-span-diagram s c')
    (L :
      vertical-map-cocone-span-diagram s c ~
      vertical-map-cocone-span-diagram s c') →
    UU (l3 ⊔ l4)
  statement-coherence-htpy-cocone-span-diagram c c' K L =
    coherence-square-homotopies
      ( K ·r left-map-span-diagram s)
      ( coherence-square-cocone-span-diagram s c)
      ( coherence-square-cocone-span-diagram s c')
      ( L ·r right-map-span-diagram s)

  htpy-cocone-span-diagram :
    (c c' : cocone-span-diagram s X) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-cocone-span-diagram c c' =
    Σ ( horizontal-map-cocone-span-diagram s c ~
        horizontal-map-cocone-span-diagram s c')
      ( λ K →
        Σ ( vertical-map-cocone-span-diagram s c ~
            vertical-map-cocone-span-diagram s c')
          ( statement-coherence-htpy-cocone-span-diagram c c' K))

  module _
    (c c' : cocone-span-diagram s X) (H : htpy-cocone-span-diagram c c')
    where

    horizontal-htpy-cocone-span-diagram :
      horizontal-map-cocone-span-diagram s c ~
      horizontal-map-cocone-span-diagram s c'
    horizontal-htpy-cocone-span-diagram = pr1 H

    vertical-htpy-cocone-span-diagram :
      vertical-map-cocone-span-diagram s c ~
      vertical-map-cocone-span-diagram s c'
    vertical-htpy-cocone-span-diagram = pr1 (pr2 H)

    coherence-htpy-cocone-span-diagram :
      statement-coherence-htpy-cocone-span-diagram c c'
        ( horizontal-htpy-cocone-span-diagram)
        ( vertical-htpy-cocone-span-diagram)
    coherence-htpy-cocone-span-diagram = pr2 (pr2 H)

  refl-htpy-cocone-span-diagram :
    (c : cocone-span-diagram s X) → htpy-cocone-span-diagram c c
  pr1 (refl-htpy-cocone-span-diagram (i , j , H)) = refl-htpy
  pr1 (pr2 (refl-htpy-cocone-span-diagram (i , j , H))) = refl-htpy
  pr2 (pr2 (refl-htpy-cocone-span-diagram (i , j , H))) = right-unit-htpy

  htpy-eq-cocone-span-diagram :
    (c c' : cocone-span-diagram s X) → c ＝ c' → htpy-cocone-span-diagram c c'
  htpy-eq-cocone-span-diagram c .c refl = refl-htpy-cocone-span-diagram c

  is-torsorial-htpy-cocone-span-diagram :
    (c : cocone-span-diagram s X) → is-torsorial (htpy-cocone-span-diagram c)
  is-torsorial-htpy-cocone-span-diagram c =
    is-torsorial-Eq-structure
      ( λ i' jH' K →
        Σ ( vertical-map-cocone-span-diagram s c ~ pr1 jH')
          ( statement-coherence-htpy-cocone-span-diagram c (i' , jH') K))
      ( is-torsorial-htpy (horizontal-map-cocone-span-diagram s c))
      ( horizontal-map-cocone-span-diagram s c , refl-htpy)
      ( is-torsorial-Eq-structure
        ( λ j' H' →
          statement-coherence-htpy-cocone-span-diagram c
            ( horizontal-map-cocone-span-diagram s c , j' , H')
            ( refl-htpy))
        ( is-torsorial-htpy (vertical-map-cocone-span-diagram s c))
        ( vertical-map-cocone-span-diagram s c , refl-htpy)
        ( is-contr-is-equiv'
          ( Σ ( ( horizontal-map-cocone-span-diagram s c ∘
                  left-map-span-diagram s) ~
                ( vertical-map-cocone-span-diagram s c ∘
                  right-map-span-diagram s))
              ( λ H' → coherence-square-cocone-span-diagram s c ~ H'))
          ( tot (λ H' M → right-unit-htpy ∙h M))
          ( is-equiv-tot-is-fiberwise-equiv (λ H' → is-equiv-concat-htpy _ _))
          ( is-torsorial-htpy (coherence-square-cocone-span-diagram s c))))

  is-equiv-htpy-eq-cocone-span-diagram :
    (c c' : cocone-span-diagram s X) →
    is-equiv (htpy-eq-cocone-span-diagram c c')
  is-equiv-htpy-eq-cocone-span-diagram c =
    fundamental-theorem-id
      ( is-torsorial-htpy-cocone-span-diagram c)
      ( htpy-eq-cocone-span-diagram c)

  extensionality-cocone-span-diagram :
    (c c' : cocone-span-diagram s X) → (c ＝ c') ≃ htpy-cocone-span-diagram c c'
  pr1 (extensionality-cocone-span-diagram c c') =
    htpy-eq-cocone-span-diagram c c'
  pr2 (extensionality-cocone-span-diagram c c') =
    is-equiv-htpy-eq-cocone-span-diagram c c'

  eq-htpy-cocone-span-diagram :
    (c c' : cocone-span-diagram s X) → htpy-cocone-span-diagram c c' → c ＝ c'
  eq-htpy-cocone-span-diagram c c' =
    map-inv-is-equiv (is-equiv-htpy-eq-cocone-span-diagram c c')
```

## See also

- In
  [Operations on cocones under span diagrams](synthetic-homotopy-theory.operations-cocones-under-span-diagrams.md)
  we define several ways of constructing cocones under span diagrams from given cocones
  under span diagrams, [morphisms of arrows](foundation.morphisms-arrows.md),
  [equivalences of arrows](foundation.equivalences-arrows.md),
  [morphisms of span diagrams](foundation.morphisms-span-diagrams.md),
  [equivalences of span diagrams](foundation.equivalences-span-diagrams.md), and so on.
