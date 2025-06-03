# Coforks

```agda
module synthetic-homotopy-theory.coforks where
```

<details><summary>Imports</summary>

```agda
open import foundation.codiagonal-maps-of-types
open import foundation.commuting-squares-of-maps
open import foundation.commuting-triangles-of-maps
open import foundation.contractible-types
open import foundation.coproduct-types
open import foundation.dependent-pair-types
open import foundation.double-arrows
open import foundation.equivalences
open import foundation.equivalences-double-arrows
open import foundation.equivalences-span-diagrams
open import foundation.function-types
open import foundation.functoriality-coproduct-types
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.identity-types
open import foundation.morphisms-double-arrows
open import foundation.morphisms-span-diagrams
open import foundation.span-diagrams
open import foundation.structure-identity-principle
open import foundation.torsorial-type-families
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import synthetic-homotopy-theory.cocones-under-spans
```

</details>

## Idea

A {{#concept "cofork" Disambiguation="of types" Agda=cofork}} of a
[double arrow](foundation.double-arrows.md) `f, g : A → B` with vertext `X` is a
map `e : B → X` together with a [homotopy](foundation.homotopies.md)
`H : e ∘ f ~ e ∘ g`. The name comes from the diagram

```text
     g
   ----->     e
 A -----> B -----> X
     f
```

which looks like a fork if you flip the arrows, hence a cofork.

Coforks are an analog of
[cocones under spans](synthetic-homotopy-theory.cocones-under-spans.md) for
double arrows. The universal cofork of a double arrow is their
[coequalizer](synthetic-homotopy-theory.coequalizers.md).

## Definitions

### Coforks

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2)
  where

  coherence-cofork : {X : UU l3} → (codomain-double-arrow a → X) → UU (l1 ⊔ l3)
  coherence-cofork e =
    e ∘ left-map-double-arrow a ~
    e ∘ right-map-double-arrow a

  cofork : UU l3 → UU (l1 ⊔ l2 ⊔ l3)
  cofork X =
    Σ (codomain-double-arrow a → X) (coherence-cofork)

  module _
    {X : UU l3} (e : cofork X)
    where

    map-cofork : codomain-double-arrow a → X
    map-cofork = pr1 e

    coh-cofork : coherence-cofork map-cofork
    coh-cofork = pr2 e
```

### Homotopies of coforks

A homotopy between coforks with the same vertex is given by a homotopy between
the two maps, together with a coherence datum asserting that we may apply the
given homotopy and the appropriate cofork homotopy in either order.

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2) {X : UU l3}
  where

  coherence-htpy-cofork :
    (e e' : cofork a X) →
    (K : map-cofork a e ~ map-cofork a e') →
    UU (l1 ⊔ l3)
  coherence-htpy-cofork e e' K =
    ( (coh-cofork a e) ∙h (K ·r right-map-double-arrow a)) ~
    ( (K ·r left-map-double-arrow a) ∙h (coh-cofork a e'))

  htpy-cofork : cofork a X → cofork a X → UU (l1 ⊔ l2 ⊔ l3)
  htpy-cofork e e' =
    Σ ( map-cofork a e ~ map-cofork a e')
      ( coherence-htpy-cofork e e')
```

### Postcomposing coforks

Given a cofork `e : B → X` and a map `h : X → Y`, we may compose the two to get
a new cofork `h ∘ e`.

```text
     g
   ----->     e        h
 A -----> B -----> X -----> Y
     f
```

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : cofork a X)
  where

  cofork-map : {l : Level} {Y : UU l} → (X → Y) → cofork a Y
  pr1 (cofork-map h) = h ∘ map-cofork a e
  pr2 (cofork-map h) = h ·l (coh-cofork a e)
```

## Properties

### Characterization of identity types of coforks

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2) {X : UU l3}
  where

  refl-htpy-cofork : (e : cofork a X) → htpy-cofork a e e
  pr1 (refl-htpy-cofork e) = refl-htpy
  pr2 (refl-htpy-cofork e) = right-unit-htpy

  htpy-cofork-eq :
    (e e' : cofork a X) → (e ＝ e') → htpy-cofork a e e'
  htpy-cofork-eq e .e refl = refl-htpy-cofork e

  abstract
    is-torsorial-htpy-cofork :
      (e : cofork a X) → is-torsorial (htpy-cofork a e)
    is-torsorial-htpy-cofork e =
      is-torsorial-Eq-structure
        ( is-torsorial-htpy (map-cofork a e))
        ( map-cofork a e , refl-htpy)
        ( is-contr-is-equiv'
          ( Σ ( coherence-cofork a (map-cofork a e))
              ( λ K → coh-cofork a e ~ K))
          ( tot (λ K M → right-unit-htpy ∙h M))
          ( is-equiv-tot-is-fiberwise-equiv
            ( is-equiv-concat-htpy right-unit-htpy))
          ( is-torsorial-htpy (coh-cofork a e)))

    is-equiv-htpy-cofork-eq :
      (e e' : cofork a X) → is-equiv (htpy-cofork-eq e e')
    is-equiv-htpy-cofork-eq e =
      fundamental-theorem-id (is-torsorial-htpy-cofork e) (htpy-cofork-eq e)

  eq-htpy-cofork : (e e' : cofork a X) → htpy-cofork a e e' → e ＝ e'
  eq-htpy-cofork e e' = map-inv-is-equiv (is-equiv-htpy-cofork-eq e e')
```

### Postcomposing a cofork by identity is the identity

```agda
module _
  {l1 l2 l3 : Level} (a : double-arrow l1 l2) {X : UU l3}
  (e : cofork a X)
  where

  cofork-map-id : cofork-map a e id ＝ e
  cofork-map-id =
    eq-htpy-cofork a
      ( cofork-map a e id)
      ( e)
      ( ( refl-htpy) ,
        ( right-unit-htpy ∙h left-unit-law-left-whisker-comp (coh-cofork a e)))
```

### Postcomposing coforks distributes over function composition

```text
     g
   ----->     e        h        k
 A -----> B -----> X -----> Y -----> Z
     f
```

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (a : double-arrow l1 l2)
  {X : UU l3} {Y : UU l4} {Z : UU l5}
  (e : cofork a X)
  where

  cofork-map-comp :
    (h : X → Y) (k : Y → Z) →
    cofork-map a e (k ∘ h) ＝ cofork-map a (cofork-map a e h) k
  cofork-map-comp h k =
    eq-htpy-cofork a
      ( cofork-map a e (k ∘ h))
      ( cofork-map a (cofork-map a e h) k)
      ( ( refl-htpy) ,
        ( ( right-unit-htpy) ∙h
          ( inv-preserves-comp-left-whisker-comp k h (coh-cofork a e))))
```

### Coforks are special cases of cocones under spans

The type of coforks of a double arrow `f, g : A → B` is equivalent to the type
of [cocones](synthetic-homotopy-theory.cocones-under-spans.md) under the span

```text
     ∇         [f,g]
A <----- A + A -----> B.
```

```agda
module _
  {l1 l2 : Level} (a : double-arrow l1 l2)
  where

  vertical-map-span-cocone-cofork :
    domain-double-arrow a + domain-double-arrow a → domain-double-arrow a
  vertical-map-span-cocone-cofork = codiagonal (domain-double-arrow a)

  horizontal-map-span-cocone-cofork :
    domain-double-arrow a + domain-double-arrow a → codomain-double-arrow a
  horizontal-map-span-cocone-cofork (inl x) = left-map-double-arrow a x
  horizontal-map-span-cocone-cofork (inr x) = right-map-double-arrow a x

  span-diagram-cofork : span-diagram l1 l2 l1
  span-diagram-cofork =
    make-span-diagram
      ( vertical-map-span-cocone-cofork)
      ( horizontal-map-span-cocone-cofork)

  module _
    {l3 : Level} {X : UU l3}
    where

    cofork-cocone-codiagonal :
      cocone
        ( vertical-map-span-cocone-cofork)
        ( horizontal-map-span-cocone-cofork)
        ( X) →
      cofork a X
    pr1 (cofork-cocone-codiagonal c) =
      vertical-map-cocone
        ( vertical-map-span-cocone-cofork)
        ( horizontal-map-span-cocone-cofork)
        ( c)
    pr2 (cofork-cocone-codiagonal c) =
      ( ( inv-htpy
          ( coherence-square-cocone
            ( vertical-map-span-cocone-cofork)
            ( horizontal-map-span-cocone-cofork)
            ( c))) ·r
        ( inl)) ∙h
      ( ( coherence-square-cocone
          ( vertical-map-span-cocone-cofork)
          ( horizontal-map-span-cocone-cofork)
          ( c)) ·r
        ( inr))

    horizontal-map-cocone-cofork : cofork a X → domain-double-arrow a → X
    horizontal-map-cocone-cofork e = map-cofork a e ∘ left-map-double-arrow a

    vertical-map-cocone-cofork : cofork a X → codomain-double-arrow a → X
    vertical-map-cocone-cofork e = map-cofork a e

    coherence-square-cocone-cofork :
      (e : cofork a X) →
      coherence-square-maps
        ( horizontal-map-span-cocone-cofork)
        ( vertical-map-span-cocone-cofork)
        ( vertical-map-cocone-cofork e)
        ( horizontal-map-cocone-cofork e)
    coherence-square-cocone-cofork e (inl x) = refl
    coherence-square-cocone-cofork e (inr x) = coh-cofork a e x

    cocone-codiagonal-cofork :
      cofork a X →
      cocone
        ( vertical-map-span-cocone-cofork)
        ( horizontal-map-span-cocone-cofork)
        ( X)
    pr1 (cocone-codiagonal-cofork e) = horizontal-map-cocone-cofork e
    pr1 (pr2 (cocone-codiagonal-cofork e)) = vertical-map-cocone-cofork e
    pr2 (pr2 (cocone-codiagonal-cofork e)) = coherence-square-cocone-cofork e

    abstract
      is-section-cocone-codiagonal-cofork :
        cofork-cocone-codiagonal ∘ cocone-codiagonal-cofork ~ id
      is-section-cocone-codiagonal-cofork e =
        eq-htpy-cofork a
          ( cofork-cocone-codiagonal (cocone-codiagonal-cofork e))
          ( e)
          ( refl-htpy , right-unit-htpy)

      is-retraction-cocone-codiagonal-fork :
        cocone-codiagonal-cofork ∘ cofork-cocone-codiagonal ~ id
      is-retraction-cocone-codiagonal-fork c =
        eq-htpy-cocone
          ( vertical-map-span-cocone-cofork)
          ( horizontal-map-span-cocone-cofork)
          ( cocone-codiagonal-cofork (cofork-cocone-codiagonal c))
          ( c)
          ( ( ( inv-htpy
                ( coherence-square-cocone
                  ( vertical-map-span-cocone-cofork)
                  ( horizontal-map-span-cocone-cofork)
                  ( c))) ·r
              ( inl)) ,
            ( refl-htpy) ,
            ( ind-coproduct _
              ( inv-htpy-left-inv-htpy
                ( ( coherence-square-cocone
                    ( vertical-map-span-cocone-cofork)
                    ( horizontal-map-span-cocone-cofork)
                    ( c)) ·r
                  ( inl)))
              ( right-unit-htpy)))

    is-equiv-cofork-cocone-codiagonal :
      is-equiv cofork-cocone-codiagonal
    is-equiv-cofork-cocone-codiagonal =
      is-equiv-is-invertible
        ( cocone-codiagonal-cofork)
        ( is-section-cocone-codiagonal-cofork)
        ( is-retraction-cocone-codiagonal-fork)

    equiv-cocone-codiagonal-cofork :
      cocone
        ( vertical-map-span-cocone-cofork)
        ( horizontal-map-span-cocone-cofork)
        ( X) ≃
      cofork a X
    pr1 equiv-cocone-codiagonal-cofork = cofork-cocone-codiagonal
    pr2 equiv-cocone-codiagonal-cofork = is-equiv-cofork-cocone-codiagonal

  triangle-cofork-cocone :
    {l3 l4 : Level} {X : UU l3} {Y : UU l4} →
    (e : cofork a X) →
    coherence-triangle-maps
      ( cofork-map a e {Y = Y})
      ( cofork-cocone-codiagonal)
      ( cocone-map
        ( vertical-map-span-cocone-cofork)
        ( horizontal-map-span-cocone-cofork)
        ( cocone-codiagonal-cofork e))
  triangle-cofork-cocone e h =
    eq-htpy-cofork a
      ( cofork-map a e h)
      ( cofork-cocone-codiagonal
        ( cocone-map
          ( vertical-map-span-cocone-cofork)
          ( horizontal-map-span-cocone-cofork)
          ( cocone-codiagonal-cofork e)
          ( h)))
      ( refl-htpy ,
        right-unit-htpy)
```

### Morphisms between double arrows induce morphisms between cofork span diagrams

A [morphism of double arrows](foundation.morphisms-double-arrows.md)

```text
           i
     A --------> X
    | |         | |
  f | | g     h | | k
    | |         | |
    ∨ ∨         ∨ ∨
     B --------> Y
           j
```

induces a [morphism of span diagrams](foundation.morphisms-span-diagrams.md)

```text
          ∇           [f,g]
    A <------- A + A -------> B
    |            |            |
  i |            | i + i      | j
    ∨            ∨            ∨
    X <------- X + X -------> Y
          ∇           [h,k]
```

```agda
module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) (a' : double-arrow l3 l4)
  (h : hom-double-arrow a a')
  where

  spanning-map-hom-span-diagram-cofork-hom-double-arrow :
    domain-double-arrow a + domain-double-arrow a →
    domain-double-arrow a' + domain-double-arrow a'
  spanning-map-hom-span-diagram-cofork-hom-double-arrow =
    map-coproduct
      ( domain-map-hom-double-arrow a a' h)
      ( domain-map-hom-double-arrow a a' h)

  left-square-hom-span-diagram-cofork-hom-double-arrow :
    coherence-square-maps'
      ( vertical-map-span-cocone-cofork a)
      ( spanning-map-hom-span-diagram-cofork-hom-double-arrow)
      ( domain-map-hom-double-arrow a a' h)
      ( vertical-map-span-cocone-cofork a')
  left-square-hom-span-diagram-cofork-hom-double-arrow =
    ind-coproduct _ refl-htpy refl-htpy

  right-square-hom-span-diagram-cofork-hom-double-arrow :
    coherence-square-maps'
      ( horizontal-map-span-cocone-cofork a)
      ( spanning-map-hom-span-diagram-cofork-hom-double-arrow)
      ( codomain-map-hom-double-arrow a a' h)
      ( horizontal-map-span-cocone-cofork a')
  right-square-hom-span-diagram-cofork-hom-double-arrow =
    ind-coproduct _
      ( left-square-hom-double-arrow a a' h)
      ( right-square-hom-double-arrow a a' h)

  hom-span-diagram-cofork-hom-double-arrow :
    hom-span-diagram
      ( span-diagram-cofork a)
      ( span-diagram-cofork a')
  pr1 (hom-span-diagram-cofork-hom-double-arrow) =
    domain-map-hom-double-arrow a a' h
  pr1 (pr2 (hom-span-diagram-cofork-hom-double-arrow)) =
    codomain-map-hom-double-arrow a a' h
  pr1 (pr2 (pr2 (hom-span-diagram-cofork-hom-double-arrow))) =
    spanning-map-hom-span-diagram-cofork-hom-double-arrow
  pr1 (pr2 (pr2 (pr2 (hom-span-diagram-cofork-hom-double-arrow)))) =
    left-square-hom-span-diagram-cofork-hom-double-arrow
  pr2 (pr2 (pr2 (pr2 (hom-span-diagram-cofork-hom-double-arrow)))) =
    right-square-hom-span-diagram-cofork-hom-double-arrow
```

### Equivalences between double arrows induce equivalences between cofork span diagrams

An [equivalence of double arrows](foundation.equivalences-double-arrows.md)

```text
           i
     A --------> X
    | |    ≃    | |
  f | | g     h | | k
    | |         | |
    ∨ ∨    ≃    ∨ ∨
     B --------> Y
           j
```

induces an
[equivalence of span diagrams](foundation.equivalences-span-diagrams.md)

```text
          ∇           [f,g]
    A <------- A + A -------> B
    |            |            |
  i | ≃        ≃ | i + i    ≃ | j
    ∨            ∨            ∨
    X <------- X + X -------> Y
          ∇           [h,k]
```

```agda
module _
  {l1 l2 l3 l4 : Level} (a : double-arrow l1 l2) (a' : double-arrow l3 l4)
  (e : equiv-double-arrow a a')
  where

  spanning-equiv-equiv-span-diagram-cofork-equiv-double-arrow :
    domain-double-arrow a + domain-double-arrow a ≃
    domain-double-arrow a' + domain-double-arrow a'
  spanning-equiv-equiv-span-diagram-cofork-equiv-double-arrow =
    equiv-coproduct
      ( domain-equiv-equiv-double-arrow a a' e)
      ( domain-equiv-equiv-double-arrow a a' e)

  left-square-equiv-span-diagram-cofork-equiv-double-arrow :
    coherence-square-maps'
      ( vertical-map-span-cocone-cofork a)
      ( map-equiv spanning-equiv-equiv-span-diagram-cofork-equiv-double-arrow)
      ( domain-map-equiv-double-arrow a a' e)
      ( vertical-map-span-cocone-cofork a')
  left-square-equiv-span-diagram-cofork-equiv-double-arrow =
    ind-coproduct _ refl-htpy refl-htpy

  right-square-equiv-span-diagram-cofork-equiv-double-arrow :
    coherence-square-maps'
      ( horizontal-map-span-cocone-cofork a)
      ( map-equiv spanning-equiv-equiv-span-diagram-cofork-equiv-double-arrow)
      ( codomain-map-equiv-double-arrow a a' e)
      ( horizontal-map-span-cocone-cofork a')
  right-square-equiv-span-diagram-cofork-equiv-double-arrow =
    ind-coproduct _
      ( left-square-equiv-double-arrow a a' e)
      ( right-square-equiv-double-arrow a a' e)

  equiv-span-diagram-cofork-equiv-double-arrow :
    equiv-span-diagram
      ( span-diagram-cofork a)
      ( span-diagram-cofork a')
  pr1 (equiv-span-diagram-cofork-equiv-double-arrow) =
    domain-equiv-equiv-double-arrow a a' e
  pr1 (pr2 (equiv-span-diagram-cofork-equiv-double-arrow)) =
    codomain-equiv-equiv-double-arrow a a' e
  pr1 (pr2 (pr2 (equiv-span-diagram-cofork-equiv-double-arrow))) =
    spanning-equiv-equiv-span-diagram-cofork-equiv-double-arrow
  pr1 (pr2 (pr2 (pr2 (equiv-span-diagram-cofork-equiv-double-arrow)))) =
    left-square-equiv-span-diagram-cofork-equiv-double-arrow
  pr2 (pr2 (pr2 (pr2 (equiv-span-diagram-cofork-equiv-double-arrow)))) =
    right-square-equiv-span-diagram-cofork-equiv-double-arrow
```
