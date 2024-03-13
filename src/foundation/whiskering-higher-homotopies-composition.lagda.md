# Whiskering higher homotopies with respect to composition

```agda
module foundation.whiskering-higher-homotopies-composition where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.universe-levels
open import foundation.whiskering-homotopies-composition

open import foundation-core.homotopies
```

</details>

## Idea

Consider two dependent functions `f g : (x : A) → B x` equipped with two
[homotopies](foundation-core.homotopies.md) `H H' : f ~ g`, and consider a
family of maps `h : (x : A) → B x → C x`. Then we obtain a map

```text
  α ↦ ap h ·l α : H ~ H' → h ·l H ~ h ·l H'
```

This operation is called the
{{#concept "left whiskering" Disambiguation="`2`-homotopies with respect to composition" Agda=left-whisker-comp²}}.
Alternatively the left whiskering operation of `2`-homotopies can be defined
using the
[action on higher identifications of functions](foundation.action-on-higher-identifications-functions.md)
by

```text
  α x ↦ ap² h (α x).
```

Similarly, the
{{#concept "right whiskering" Disambiguation="2-homotopies with respect to composition" Agda=right-whisker-comp²}}
is defined to be the operation

```text
  (H ~ H') → (h : (x : A) → B x) → (H ·r h ~ H' ·r h)
```

given by

```text
  α h ↦ α ·r h,
```

for any pair of homotopies `H H' : f ~ g`, where
`f g : (x : A) (y : B x) → C x y`.

## Definitions

### Left whiskering higher homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : A → UU l3}
  {f g : (x : A) → B x}
  where

  left-whisker-comp² :
    (h : {x : A} → B x → C x) {H H' : f ~ g} (α : H ~ H') → h ·l H ~ h ·l H'
  left-whisker-comp² h α = ap h ·l α
```

### Right whiskering higher homotopies

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2} {C : (x : A) → B x → UU l3}
  {f g : {x : A} (y : B x) → C x y} {H H' : {x : A} → f {x} ~ g {x}}
  where

  right-whisker-comp² :
    (α : {x : A} → H {x} ~ H' {x}) (h : (x : A) → B x) → H ·r h ~ H' ·r h
  right-whisker-comp² α h = α ·r h
```

### Double whiskering higher homotopies

```agda
module _
  {l1 l2 l3 l4 : Level} {A : UU l1} {B : A → UU l2}
  {C : (x : A) → B x → UU l3} {D : (x : A) → B x → UU l4}
  {f g : {x : A} (y : B x) → C x y} {H H' : {x : A} → f {x} ~ g {x}}
  where

  double-whisker-comp² :
    (left : {x : A} {y : B x} → C x y → D x y)
    (α : {x : A} → H {x} ~ H' {x})
    (right : (x : A) → B x) →
    left ·l H ·r right ~ left ·l H' ·r right
  double-whisker-comp² left α right = double-whisker-comp (ap left) α right
```
