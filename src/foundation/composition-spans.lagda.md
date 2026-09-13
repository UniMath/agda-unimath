# Composition of spans

```agda
module foundation.composition-spans where
```

<details><summary>Imports</summary>

```agda
open import foundation.commuting-triangles-of-maps
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.equivalences-spans
open import foundation.homotopies
open import foundation.identity-types
open import foundation.morphisms-arrows
open import foundation.morphisms-spans
open import foundation.pullbacks
open import foundation.spans
open import foundation.standard-pullbacks
open import foundation.type-arithmetic-standard-pullbacks
open import foundation.universe-levels

open import foundation-core.equivalences-arrows
open import foundation-core.function-types
```

</details>

## Idea

Given two [spans](foundation.spans.md) `F` and `G` such that the source of `G`
is the target of `F`

```text
           F                 G

  A <----- S -----> B <----- T -----> C,
```

then we may
{{#concept "compose" Disambiguation="spans of types" Agda=comp-span}} the two
spans by forming the [pullback](foundation.standard-pullbacks.md) of the middle
[cospan diagram](foundation.cospan-diagrams.md)

```text
  ∙ ------> T ------> C
  | ⌟       |
  |         |    G
  ∨         ∨
  S ------> B
  |
  |    F
  ∨
  A
```

giving us a span `G ∘ F` from `A` to `C`. This operation is unital and
associative.

## Definitions

### Composition of spans

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  (G : span l4 B C) (F : span l5 A B)
  where

  spanning-type-comp-span : UU (l2 ⊔ l4 ⊔ l5)
  spanning-type-comp-span =
    standard-pullback (right-map-span F) (left-map-span G)

  left-map-comp-span : spanning-type-comp-span → A
  left-map-comp-span = left-map-span F ∘ vertical-map-standard-pullback

  right-map-comp-span : spanning-type-comp-span → C
  right-map-comp-span = right-map-span G ∘ horizontal-map-standard-pullback

  comp-span : span (l2 ⊔ l4 ⊔ l5) A C
  comp-span = spanning-type-comp-span , left-map-comp-span , right-map-comp-span
```

## Properties

### Associativity of composition of spans

```agda
module _
  {l1 l2 l3 l4 l5 l6 l7 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3} {D : UU l4}
  (H : span l5 C D) (G : span l6 B C) (F : span l7 A B)
  where

  essentially-associative-spanning-type-comp-span :
    spanning-type-comp-span (comp-span H G) F ≃
    spanning-type-comp-span H (comp-span G F)
  essentially-associative-spanning-type-comp-span =
    inv-associative-standard-pullback
      ( right-map-span F)
      ( left-map-span G)
      ( right-map-span G)
      ( left-map-span H)

  essentially-associative-comp-span :
    equiv-span (comp-span (comp-span H G) F) (comp-span H (comp-span G F))
  essentially-associative-comp-span =
    ( essentially-associative-spanning-type-comp-span , refl-htpy , refl-htpy)

  associative-comp-span :
    comp-span (comp-span H G) F ＝ comp-span H (comp-span G F)
  associative-comp-span =
    eq-equiv-span
      ( comp-span (comp-span H G) F)
      ( comp-span H (comp-span G F))
      ( essentially-associative-comp-span)
```

### The left unit law for composition of spans

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (F : span l3 A B)
  where

  left-unit-law-comp-span' :
    equiv-span F (comp-span id-span F)
  left-unit-law-comp-span' =
    inv-right-unit-law-standard-pullback (right-map-span F) ,
    refl-htpy ,
    refl-htpy

  left-unit-law-comp-span :
    equiv-span (comp-span id-span F) F
  left-unit-law-comp-span =
    right-unit-law-standard-pullback (right-map-span F) ,
    refl-htpy ,
    inv-htpy coherence-square-standard-pullback
```

### The right unit law for composition of spans

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} (F : span l3 A B)
  where

  right-unit-law-comp-span' :
    equiv-span F (comp-span F id-span)
  right-unit-law-comp-span' =
    inv-left-unit-law-standard-pullback (left-map-span F) ,
    refl-htpy ,
    refl-htpy

  right-unit-law-comp-span :
    equiv-span (comp-span F id-span) F
  right-unit-law-comp-span =
    left-unit-law-standard-pullback (left-map-span F) ,
    coherence-square-standard-pullback ,
    refl-htpy
```
