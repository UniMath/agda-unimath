# Cocones under spans

```agda
module synthetic-homotopy-theory.cocones-under-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-squares-of-homotopies
open import foundation.dependent-pair-types
open import foundation.equivalences-arrows
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.morphisms-arrows
open import foundation.morphisms-spans
open import foundation.spans
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

A {{#concept "cocone" Agda=cocone-span Disambiguation="span"}} under a [span](foundation.spans.md) `A <-f- S -g-> B` with codomain
`X` consists of two maps `i : A → X` and `j : B → X` equipped with a
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

[Equivalently](foundation-core.equivalences.md), a cocone with codomain `X` under a span `s` given by
`A <-f- S -g-> B` can be described as a
[morphism of spans](foundation.morphisms-spans.md) from `s` into the constant
span at `X`. In other words, a cocone under `s` with codomain `X` is a commuting
diagram of the form

```text
         f       g
    A <----- S -----> B
    |        |        |
  i |        | h      | j
    V        V        V
    X ====== X ====== X.
```

It is immediate from the definition of a cocone on a span that any commuting square of maps, or any [morphism of arrows](foundation.morphisms-arrows.md) can be presented equivalently as a cocone on a span.

## Definitions

### Cocones under spans

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3)
  where

  cocone-span :
    UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-span X =
    Σ ( domain-span s → X)
      ( λ i →
        Σ ( codomain-span s → X)
          ( λ j →
            coherence-square-maps (right-map-span s) (left-map-span s) j i))

  module _
    {X : UU l4} (c : cocone-span X)
    where

    horizontal-map-cocone-span : domain-span s → X
    horizontal-map-cocone-span = pr1 c

    vertical-map-cocone-span : codomain-span s → X
    vertical-map-cocone-span = pr1 (pr2 c)

    coherence-square-cocone-span :
      coherence-square-maps
        ( right-map-span s)
        ( left-map-span s)
        ( vertical-map-cocone-span)
        ( horizontal-map-cocone-span)
    coherence-square-cocone-span = pr2 (pr2 c)
```

### Alternative definition of cocones under spans

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3)
  where

  cocone-span' : UU l4 → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  cocone-span' X = hom-span s (constant-span X)
```

### Cocones obtained from morphisms of arrows

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : UU l2} {X : UU l3} {Y : UU l4}
  (f : A → B) (g : X → Y) (h : hom-arrow f g)
  where

  cocone-hom-arrow : cocone-span (span-hom-arrow f g h) Y
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

  cocone-equiv-arrow : cocone-span (span-equiv-arrow f g e) Y
  cocone-equiv-arrow = cocone-hom-arrow f g (hom-equiv-arrow f g e)
```

### Homotopies of cocones under spans

Given two cocones `c` and `c'` on a span `s`, both with the same codomain `X`, we also introduce homotopies of cocones under spans. A {{#concept "homotopy of cocones under a span" Agda=htpy-cocone-span}} from `c := (i , j , H)` to `c' := (i' , j' , H')` under a span `A <-f- S -g-> B` consists of two homotopies `K : i ~ i'` and `L : j ~ j'` and a homotopy `M` witnessing that the square of homotopies

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
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) {X : UU l4}
  where

  statement-coherence-htpy-cocone-span :
    (c c' : cocone-span s X) →
    (K : horizontal-map-cocone-span s c ~ horizontal-map-cocone-span s c')
    (L : vertical-map-cocone-span s c ~ vertical-map-cocone-span s c') →
    UU (l3 ⊔ l4)
  statement-coherence-htpy-cocone-span c c' K L =
    coherence-square-homotopies
      ( K ·r left-map-span s)
      ( coherence-square-cocone-span s c)
      ( coherence-square-cocone-span s c')
      ( L ·r right-map-span s)

  htpy-cocone-span : (c c' : cocone-span s X) → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  htpy-cocone-span c c' =
    Σ ( horizontal-map-cocone-span s c ~ horizontal-map-cocone-span s c')
      ( λ K →
        Σ ( vertical-map-cocone-span s c ~ vertical-map-cocone-span s c')
          ( statement-coherence-htpy-cocone-span c c' K))

  module _
    (c c' : cocone-span s X) (H : htpy-cocone-span c c')
    where

    horizontal-htpy-cocone-span :
      horizontal-map-cocone-span s c ~ horizontal-map-cocone-span s c'
    horizontal-htpy-cocone-span = pr1 H

    vertical-htpy-cocone-span :
      vertical-map-cocone-span s c ~ vertical-map-cocone-span s c'
    vertical-htpy-cocone-span = pr1 (pr2 H)

    coherence-htpy-cocone-span :
      statement-coherence-htpy-cocone-span c c'
        ( horizontal-htpy-cocone-span)
        ( vertical-htpy-cocone-span)
    coherence-htpy-cocone-span = pr2 (pr2 H)

  refl-htpy-cocone-span :
    (c : cocone-span s X) → htpy-cocone-span c c
  pr1 (refl-htpy-cocone-span (i , j , H)) = refl-htpy
  pr1 (pr2 (refl-htpy-cocone-span (i , j , H))) = refl-htpy
  pr2 (pr2 (refl-htpy-cocone-span (i , j , H))) = right-unit-htpy

  htpy-eq-cocone-span :
    (c c' : cocone-span s X) → c ＝ c' → htpy-cocone-span c c'
  htpy-eq-cocone-span c .c refl = refl-htpy-cocone-span c

  is-torsorial-htpy-cocone-span :
    (c : cocone-span s X) → is-torsorial (htpy-cocone-span c)
  is-torsorial-htpy-cocone-span c =
    is-torsorial-Eq-structure
      ( λ i' jH' K →
        Σ ( vertical-map-cocone-span s c ~ pr1 jH')
          ( statement-coherence-htpy-cocone-span c (i' , jH') K))
      ( is-torsorial-htpy (horizontal-map-cocone-span s c))
      ( horizontal-map-cocone-span s c , refl-htpy)
      ( is-torsorial-Eq-structure
        ( λ j' H' →
          statement-coherence-htpy-cocone-span c
            ( horizontal-map-cocone-span s c , j' , H')
            ( refl-htpy))
        ( is-torsorial-htpy (vertical-map-cocone-span s c))
        ( vertical-map-cocone-span s c , refl-htpy)
        ( is-contr-is-equiv'
          ( Σ ( ( horizontal-map-cocone-span s c ∘ left-map-span s) ~
                ( vertical-map-cocone-span s c ∘ right-map-span s))
              ( λ H' → coherence-square-cocone-span s c ~ H'))
          ( tot (λ H' M → right-unit-htpy ∙h M))
          ( is-equiv-tot-is-fiberwise-equiv (λ H' → is-equiv-concat-htpy _ _))
          ( is-torsorial-htpy (coherence-square-cocone-span s c))))

  is-equiv-htpy-eq-cocone-span :
    (c c' : cocone-span s X) → is-equiv (htpy-eq-cocone-span c c')
  is-equiv-htpy-eq-cocone-span c =
    fundamental-theorem-id
      ( is-torsorial-htpy-cocone-span c)
      ( htpy-eq-cocone-span c)

  extensionality-cocone-span :
    (c c' : cocone-span s X) → (c ＝ c') ≃ htpy-cocone-span c c'
  pr1 (extensionality-cocone-span c c') = htpy-eq-cocone-span c c'
  pr2 (extensionality-cocone-span c c') = is-equiv-htpy-eq-cocone-span c c'

  eq-htpy-cocone-span :
    (c c' : cocone-span s X) → htpy-cocone-span c c' → c ＝ c'
  eq-htpy-cocone-span c c' =
    map-inv-is-equiv (is-equiv-htpy-eq-cocone-span c c')
```

## See also

- In [Operations on cocones under spans](synthetic-homotopy-theory.operations-cocones-under-spans.md) we define several ways of constructing cocones under spans from given cocones under spans, [morphisms of arrows](foundation.morphisms-arrows.md), [equivalences of arrows](foundation.equivalences-arrows.md), [morphisms of spans](foundation.morphisms-spans.md), [equivalences of spans](foundation.equivalences-spans.md), and so on.
