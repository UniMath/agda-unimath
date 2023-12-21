# Cocones under spans

```agda
module synthetic-homotopy-theory.cocones-under-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.commuting-squares-of-homotopies
open import foundation.dependent-pair-types
open import foundation.extensions-spans
open import foundation.function-extensionality
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.homotopy-induction
open import foundation.morphisms-arrows
open import foundation.morphisms-spans
open import foundation.spans
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import foundation-core.commuting-squares-of-maps
open import foundation-core.contractible-types
open import foundation-core.equality-dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
open import foundation-core.whiskering-homotopies
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

### Postcomposing cocones under spans with maps

Consider a span `A <-f- S -g-> B`. equipped with a cocone `c := (i , j , H)` as indicated in the diagram

```text
        g
    S -----> B
    |        |
  f |   H    | j
    V        V
    A -----> X.
        i
```

Then any map `h : X → Y` induces a cocone

```text
         g
    S -------> B
    |          |
  f |  h · H   | h ∘ j
    V          V
    A -------> Y.
       h ∘ i
```

This way of extending cocones by maps is used to express the [universal property of pushouts](synthetic-homotopy-theory.universal-property-pushouts.md).

```agda
module _
  {l1 l2 l3 l4 l5 : Level} (s : span l1 l2 l3) {X : UU l4} {Y : UU l5}
  where

  cocone-span-map : cocone-span s X → (X → Y) → cocone-span s Y
  pr1 (cocone-span-map c h) = h ∘ horizontal-map-cocone-span s c
  pr1 (pr2 (cocone-span-map c h)) = h ∘ vertical-map-cocone-span s c
  pr2 (pr2 (cocone-span-map c h)) = h ·l coherence-square-cocone-span s c

module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) {X : UU l4}
  where

  cocone-span-map-id :
    (c : cocone-span s X) → cocone-span-map s c id ＝ c
  cocone-span-map-id c =
    eq-pair-Σ refl
      ( eq-pair-Σ refl (eq-htpy (ap-id ∘ coherence-square-cocone-span s c)))

module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3)
  {X : UU l4} {Y : UU l5} {Z : UU l6}
  where

  cocone-span-map-comp :
    (c : cocone-span s X) (h : X → Y) (k : Y → Z) →
    cocone-span-map s c (k ∘ h) ＝ cocone-span-map s (cocone-span-map s c h) k
  cocone-span-map-comp (i , j , H) h k =
    eq-pair-Σ refl (eq-pair-Σ refl (eq-htpy (ap-comp k h ∘ H)))
```

### Horizontal composition of cocones under spans

Consider a span `s := A <-f- S -g-> B` and a moprhism `h : B → C`. Then we can
**compose** any cocone `c := (i , j , H)` with codomain `X` under the span
`s` **horizontally** with a cocone `d` under the span
`X <-j- B -h-> C` as indicated in the diagram

```text
        g       h
    S ----> B ----> C
    |       |       |
  f |       |       |
    v       v       v
    A ----> X ----> Y
```

to obtain a cocone under the span `A <-f- S -h∘g-> C`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3)
  {C : UU l4} {X : UU l5} {Y : UU l6} (h : codomain-span s → C)
  (c : cocone-span s X)
  (d : cocone-span (make-span (vertical-map-cocone-span s c) h) Y)
  where

  horizontal-map-horizontal-comp-cocone-span : domain-span s → Y
  horizontal-map-horizontal-comp-cocone-span =
    horizontal-map-cocone-span (make-span (vertical-map-cocone-span s c) h) d ∘
    horizontal-map-cocone-span s c

  vertical-map-horizontal-comp-cocone-span : C → Y
  vertical-map-horizontal-comp-cocone-span =
    vertical-map-cocone-span (make-span (vertical-map-cocone-span s c) h) d

  coherence-square-horizontal-comp-cocone-span :
    coherence-square-maps
      ( h ∘ right-map-span s)
      ( left-map-span s)
      ( vertical-map-horizontal-comp-cocone-span)
      ( horizontal-map-horizontal-comp-cocone-span)
  coherence-square-horizontal-comp-cocone-span =
    pasting-horizontal-coherence-square-maps
      ( right-map-span s)
      ( h)
      ( left-map-span s)
      ( vertical-map-cocone-span s c)
      ( vertical-map-cocone-span (make-span (vertical-map-cocone-span s c) h) d)
      ( horizontal-map-cocone-span s c)
      ( horizontal-map-cocone-span
        ( make-span (vertical-map-cocone-span s c) h)
        ( d))
      ( coherence-square-cocone-span s c)
      ( coherence-square-cocone-span
        ( make-span (vertical-map-cocone-span s c) h)
        ( d))

  horizontal-comp-cocone-span :
    cocone-span (right-extend-span s h) Y
  pr1 horizontal-comp-cocone-span =
    horizontal-map-horizontal-comp-cocone-span
  pr1 (pr2 horizontal-comp-cocone-span) =
    vertical-map-horizontal-comp-cocone-span
  pr2 (pr2 horizontal-comp-cocone-span) =
    coherence-square-horizontal-comp-cocone-span
```

### Horizontal composition of cocones under spans with morphisms of arrows

Consider a span `s := A <-f- S -g-> B` and a [moprhism of arrows](foundation.morphisms-arrows.md) `h : hom-arrow f' f` for some map `f : S' → A'`, as indicated in the diagram

```text
          h₀       g
     S' -----> S -----> B
     |         |        |
  f' |       f |        | j
     v         v        v
     A' -----> A -----> X
          h₁       i
```

Then we obtain a new cocone on the outer span `A' <- S' -> B`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3)
  {S' : UU l4} {A' : UU l5} (f' : S' → A') {X : UU l6}
  where

  horizontal-comp-hom-arrow-cocone-span :
    (h : hom-arrow f' (left-map-span s)) → cocone-span s X →
    cocone-span (left-extend-hom-arrow-span s f' h) X
  horizontal-comp-hom-arrow-cocone-span h c =
    horizontal-comp-cocone-span
      ( span-hom-arrow f' (left-map-span s) h)
      ( right-map-span s)
      ( cocone-hom-arrow f' (left-map-span s) h)
      ( c)
```

A variation on the above:

```text
        g       h
    S ----> B ----> C
    |       |       |
  f |     j |       | k
    v       v       v
    A ----> X ----> Y
        i
```

```text
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3)
  {C : UU l4} {X : UU l5} {Y : UU l6} (h : codomain-span s → C)
  (j : codomain-span s → X) (i : domain-span s → X)
  where

  horizontal-comp-cocone-span' :
    cocone-span (make-span j h) Y →
    coherence-square-maps (right-map-span s) (left-map-span s) j i →
    cocone-span (right-extend-span s h) Y
  horizontal-comp-cocone-span' c coh =
    horizontal-comp-cocone-span s h (i , j , coh) c
```

### Vertical composition of cocones under spans

Consider a span `s := A <-f- S -g-> B` and a map `h : A → C`. Then we can **compose** a cocone `c := (i , j , H)` under `s` **vertically** with a cocone `d` under the span `C <-h- A -i-> X` as indicated in the diagram

```text
        g
    S -----> B
    |        |
  f |        |
    v        v
    A -----> X
    |        |
  h |        |
    v        v
    C -----> Y
```

to obtain a cocone under the span `C <-h∘f- S -g-> B`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3)
  {C : UU l4} (h : domain-span s → C) {X : UU l5} {Y : UU l6}
  (c : cocone-span s X)
  (d : cocone-span (make-span h (horizontal-map-cocone-span s c)) Y)
  where

  horizontal-map-vertical-comp-cocone-span : C → Y
  horizontal-map-vertical-comp-cocone-span =
    horizontal-map-cocone-span (make-span h (horizontal-map-cocone-span s c)) d

  vertical-map-vertical-comp-cocone-span : codomain-span s → Y
  vertical-map-vertical-comp-cocone-span =
    vertical-map-cocone-span (make-span h (horizontal-map-cocone-span s c)) d ∘
    vertical-map-cocone-span s c

  coherence-square-vertical-comp-cocone-span :
    coherence-square-maps
      ( right-map-span s)
      ( h ∘ left-map-span s)
      ( vertical-map-vertical-comp-cocone-span)
      ( horizontal-map-vertical-comp-cocone-span)
  coherence-square-vertical-comp-cocone-span =
    pasting-vertical-coherence-square-maps
      ( right-map-span s)
      ( left-map-span s)
      ( vertical-map-cocone-span s c)
      ( horizontal-map-cocone-span s c)
      ( h)
      ( vertical-map-cocone-span
        ( make-span h (horizontal-map-cocone-span s c))
        ( d))
      ( horizontal-map-cocone-span
        ( make-span h (horizontal-map-cocone-span s c))
        ( d))
      ( coherence-square-cocone-span s c)
      ( coherence-square-cocone-span
        ( make-span h (horizontal-map-cocone-span s c))
        ( d))

  vertical-comp-cocone-span :
    cocone-span (left-extend-span s h) Y
  pr1 vertical-comp-cocone-span =
    horizontal-map-vertical-comp-cocone-span
  pr1 (pr2 vertical-comp-cocone-span) =
    vertical-map-vertical-comp-cocone-span
  pr2 (pr2 vertical-comp-cocone-span) =
    coherence-square-vertical-comp-cocone-span
```

### Composing cocones with morphisms of arrows on the right

Consider a span `s := A <-f- S -g-> B` and a map `g' : S' → B'`.
Then we can **compose** a morphism of arrows `h : hom-arrow g' g` with a cocone `c := (i , j , H)` under `s`, as indicated in the diagram

```text
         g'
     S' ----> B'
     |        |
  h₀ |        | h₁
     v   g    v
     S -----> B
     |        |
   f |        |
     v        v
     A -----> X
```

to obtain a cocone under the span `A <- S' -> B'`.

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3)
  {S' : UU l4} {B' : UU l5} (g' : S' → B')
  (h : hom-arrow g' (right-map-span s))
  {X : UU l6} (c : cocone-span s X)
  where

  vertical-comp-hom-arrow-cocone-span :
    cocone-span (right-extend-hom-arrow-span s g' h) X
  vertical-comp-hom-arrow-cocone-span =
    vertical-comp-cocone-span
      ( span-hom-arrow
        ( map-domain-hom-arrow g' (right-map-span s) h)
        ( map-codomain-hom-arrow g' (right-map-span s) h)
        ( transpose-hom-arrow g' (right-map-span s) h))
      ( left-map-span s)
      ( cocone-hom-arrow
        ( map-domain-hom-arrow g' (right-map-span s) h)
        ( map-codomain-hom-arrow g' (right-map-span s) h)
        ( transpose-hom-arrow g' (right-map-span s) h))
      ( c)
```

A variation on the above:

```text
        g
    S -----> B
    |        |
  f |        | j
    v   i    v
    A -----> X
    |        |
  h |        |
    v        v
    C -----> Y
```

```text
module _
  {l1 l2 l3 l4 l5 l6 : Level} (s : span l1 l2 l3)
  {C : UU l4} {X : UU l5} {Y : UU l6} (h : domain-span s → C)
  (i : domain-span s → X) (j : codomain-span s → X)
  where

  vertical-comp-cocone-span' :
    cocone-span (make-span h i) Y →
    coherence-square-maps (right-map-span s) (left-map-span s) j i →
    cocone-span (left-extend-span s h) Y
  vertical-comp-cocone-span' c coh =
    vertical-comp-cocone-span s h (i , j , coh) c
```

### Composition of cocones and morphisms of spans

Given a commutative diagram of the form

```text
          g'
     S' -----> B'
     |\         \
     | \ k       \ j
     v  v     g   v
     A'  S ------> B
      \  |         |
     i \ | f       |
        vv         v
         A ------> X
```

we can compose both vertically and horizontally to get the following cocone:

```text
   S' ---> B'
   |       |
   |       |
   v       v
   A' ---> X
```

Notice that the triple `(i,j,k)` is really a morphism of spans. So the resulting
cocone arises as a composition of the original cocone with this morphism of
spans.

**Note:** In the following definition we parenthesize the coherence explicitly,
because the parenthesization is relevant in future computations.

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  (s' : span l1 l2 l3) (s : span l4 l5 l6) (h : hom-span s' s)
  {X : UU l7} (c : cocone-span s X)
  where

  horizontal-map-comp-cocone-span-hom-span : domain-span s' → X
  horizontal-map-comp-cocone-span-hom-span =
    horizontal-map-cocone-span s c ∘ map-domain-hom-span s' s h

  vertical-map-comp-cocone-span-hom-span : codomain-span s' → X
  vertical-map-comp-cocone-span-hom-span =
    vertical-map-cocone-span s c ∘ map-codomain-hom-span s' s h

  coherence-square-comp-span-hom-span :
    coherence-square-maps
      ( right-map-span s')
      ( left-map-span s')
      ( vertical-map-comp-cocone-span-hom-span)
      ( horizontal-map-comp-cocone-span-hom-span)
  coherence-square-comp-span-hom-span =
    ( ( horizontal-map-cocone-span s c ·l left-square-hom-span s' s h) ∙h
      ( coherence-square-cocone-span s c ·r spanning-map-hom-span s' s h)) ∙h
    ( inv-htpy (vertical-map-cocone-span s c ·l right-square-hom-span s' s h))

  comp-cocone-span-hom-span : cocone-span s' X
  pr1 comp-cocone-span-hom-span = horizontal-map-comp-cocone-span-hom-span
  pr1 (pr2 comp-cocone-span-hom-span) = vertical-map-comp-cocone-span-hom-span
  pr2 (pr2 comp-cocone-span-hom-span) = coherence-square-comp-span-hom-span
```

### The diagonal cocone on a span of identical maps

Consider a span of the form

```text
       f       f
  B <----- A -----> B.
```

Then any map `g : B → X` induces a {{#concept "diagonal cocone" Agda=diagonal-cocone-span Disambiguation="span"}}

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (f : A → B) (X : UU l3)
  where

  diagonal-cocone-span : (B → X) → cocone-span (make-span f f) X
  pr1 (diagonal-cocone-span g) = g
  pr1 (pr2 (diagonal-cocone-span g)) = g
  pr2 (pr2 (diagonal-cocone-span g)) = refl-htpy
```

### The swapping function on cocones over spans

Any cocone

```text
        g
    S -----> B
    |        |
  f |        | j
    V        V
    A -----> X
        i
```

induces a cocone

```text
        f
    S -----> A
    |        |
  g |        | i
    V        V
    B -----> X.
        j
```

This **swapping operation** on cocones is an
[involution](foundation.involutions.md).

```agda
module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) (X : UU l4)
  where

  swap-cocone-span : cocone-span s X → cocone-span (opposite-span s) X
  pr1 (swap-cocone-span c) = vertical-map-cocone-span s c
  pr1 (pr2 (swap-cocone-span c)) = horizontal-map-cocone-span s c
  pr2 (pr2 (swap-cocone-span c)) = inv-htpy (coherence-square-cocone-span s c)

module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) (X : UU l4)
  where

  is-involution-swap-cocone-span :
    swap-cocone-span (opposite-span s) X ∘ swap-cocone-span s X ~ id
  is-involution-swap-cocone-span c =
    eq-htpy-cocone-span s
      ( swap-cocone-span (opposite-span s) X (swap-cocone-span s X c))
      ( c)
      ( ( refl-htpy) ,
        ( refl-htpy) ,
        ( λ t →
          concat
            ( right-unit)
            ( coherence-square-cocone-span s c t)
            ( inv-inv (coherence-square-cocone-span s c t))))

module _
  {l1 l2 l3 l4 : Level} (s : span l1 l2 l3) (X : UU l4)
  where

  is-equiv-swap-cocone-span : is-equiv (swap-cocone-span s X)
  is-equiv-swap-cocone-span =
    is-equiv-is-invertible
      ( swap-cocone-span (opposite-span s) X)
      ( is-involution-swap-cocone-span (opposite-span s) X)
      ( is-involution-swap-cocone-span s X)

  equiv-swap-cocone-span : cocone-span s X ≃ cocone-span (opposite-span s) X
  pr1 equiv-swap-cocone-span = swap-cocone-span s X
  pr2 equiv-swap-cocone-span = is-equiv-swap-cocone-span
```
