# Sections of dependent globular types

```agda
{-# OPTIONS --guardedness #-}

module globular-types.sections-dependent-globular-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels

open import globular-types.dependent-globular-types
open import globular-types.globular-types
```

</details>

## Idea

Consider a [dependent globular type](globular-types.dependent-globular-types.md)
`H` over a [globular type](globular-types.globular-types.md) `G`. A
{{#concept "section" Disambiguation="dependent globular type" Agda=section-Dependent-Globular-Type}}
`f` of `H` consists of

```text
  s₀ : (x : G₀) → H₀ x
  s' : {x y : G₀} (y : H₀ x) (y' : H₀ x') → section (H' y y').
```

## Definitions

### Sections of dependent globular types

```agda
record
  section-Dependent-Globular-Type
    {l1 l2 l3 l4 : Level} {G : Globular-Type l1 l2}
    (H : Dependent-Globular-Type l3 l4 G) : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  where
  coinductive

  field
    0-cell-section-Dependent-Globular-Type :
      (x : 0-cell-Globular-Type G) → 0-cell-Dependent-Globular-Type H x

  field
    1-cell-section-section-Dependent-Globular-Type :
      {x x' : 0-cell-Globular-Type G} →
      section-Dependent-Globular-Type
        ( 1-cell-dependent-globular-type-Dependent-Globular-Type H
          ( 0-cell-section-Dependent-Globular-Type x)
          ( 0-cell-section-Dependent-Globular-Type x'))

open section-Dependent-Globular-Type public

module _
  {l1 l2 l3 l4 : Level} {G : Globular-Type l1 l2}
  (H : Dependent-Globular-Type l3 l4 G)
  (s : section-Dependent-Globular-Type H)
  where

  1-cell-section-Dependent-Globular-Type :
    {x x' : 0-cell-Globular-Type G}
    (f : 1-cell-Globular-Type G x x') →
    1-cell-Dependent-Globular-Type H
      ( 0-cell-section-Dependent-Globular-Type s x)
      ( 0-cell-section-Dependent-Globular-Type s x')
      ( f)
  1-cell-section-Dependent-Globular-Type =
    0-cell-section-Dependent-Globular-Type
      ( 1-cell-section-section-Dependent-Globular-Type s)
```
