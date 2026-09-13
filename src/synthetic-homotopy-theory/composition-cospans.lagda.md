# Composition of cospans

```agda
module synthetic-homotopy-theory.composition-cospans where
```

<details><summary>Imports</summary>

```agda
open import foundation.cospans
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import foundation-core.function-types

open import synthetic-homotopy-theory.pushouts
```

</details>

## Idea

Given two [cospans](foundation.cospans.md) `F` and `G` such that the source of
`G` is the target of `F`

```text
           F                 G

  A -----> S <----- B -----> T <----- C,
```

then we may
{{#concept "compose" Disambiguation="cospans of types" Agda=comp-cospan}} the
two cospans by forming the [pushout](synthetic-homotopy-theory.pushouts.md) of
the middle [cospan diagram](foundation.cospan-diagrams.md)

```text
                      C
                      |
                      |
                      ∨
            B ------> T
            |         |
            |         |
            ∨       ⌜ ∨
  A ------> S ------> ∙
```

giving us a cospan `G ∘ F` from `A` to `C`.

## Definitions

### Composition of cospans

```agda
module _
  {l1 l2 l3 l4 l5 : Level}
  {A : UU l1} {B : UU l2} {C : UU l3}
  (G : cospan l4 B C) (F : cospan l5 A B)
  where

  cospanning-type-comp-cospan : UU (l2 ⊔ l4 ⊔ l5)
  cospanning-type-comp-cospan =
    pushout (right-map-cospan F) (left-map-cospan G)

  left-map-comp-cospan : A → cospanning-type-comp-cospan
  left-map-comp-cospan =
    inl-pushout (right-map-cospan F) (left-map-cospan G) ∘ left-map-cospan F

  right-map-comp-cospan : C → cospanning-type-comp-cospan
  right-map-comp-cospan =
    inr-pushout (right-map-cospan F) (left-map-cospan G) ∘ right-map-cospan G

  comp-cospan : cospan (l2 ⊔ l4 ⊔ l5) A C
  comp-cospan =
    ( cospanning-type-comp-cospan ,
      left-map-comp-cospan ,
      right-map-comp-cospan)
```
