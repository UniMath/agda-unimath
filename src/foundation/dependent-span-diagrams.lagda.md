# Dependent span diagrams

```agda
module foundation.dependent-span-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.span-diagrams
open import foundation.spans
open import foundation.universe-levels
```

</details>

## Idea

Consider a [span diagram](foundation.span-diagrams.md) `𝒮 := `A <-f- S -g-> B`. A {{#concept "dependent span diagram"}} over `𝒮` consists of type families

```text
  P : A → 𝒰
  Q : B → 𝒰
  T : T → 𝒰
```

and two families of maps

```text
  h : (s : S) → T s → P (f s)
  k : (s : S) → T s → Q (g s).
```

## Definitions

### Dependent span diagrams

```agda
module _
  {l1 l2 l3 : Level} (l4 l5 l6 : Level) (𝒮 : span-diagram l1 l2 l3)
  where

  dependent-span-diagram :
    UU (l1 ⊔ l2 ⊔ l3 ⊔ lsuc l4 ⊔ lsuc l5 ⊔ lsuc l6)
  dependent-span-diagram =
    Σ ( domain-span-diagram 𝒮 → UU l4)
      ( λ P →
        Σ ( codomain-span-diagram 𝒮 → UU l5)
          ( λ Q →
            Σ ( spanning-type-span-diagram 𝒮 → UU l6)
              ( λ T →
                ( (s : spanning-type-span-diagram 𝒮) →
                  T s → P (left-map-span-diagram 𝒮 s)) ×
                ( (s : spanning-type-span-diagram 𝒮) →
                  T s → Q (right-map-span-diagram 𝒮 s)))))

module _
  {l1 l2 l3 l4 l5 l6 : Level} {𝒮 : span-diagram l1 l2 l3}
  (𝒯 : dependent-span-diagram l4 l5 l6 𝒮)
  where

  domain-dependent-span-diagram : domain-span-diagram 𝒮 → UU l4
  domain-dependent-span-diagram = pr1 𝒯

  codomain-dependent-span-diagram : codomain-span-diagram 𝒮 → UU l5
  codomain-dependent-span-diagram = pr1 (pr2 𝒯)

  spanning-type-dependent-span-diagram : spanning-type-span-diagram 𝒮 → UU l6
  spanning-type-dependent-span-diagram = pr1 (pr2 (pr2 𝒯))

  left-map-dependent-span-diagram :
    (s : spanning-type-span-diagram 𝒮) →
    spanning-type-dependent-span-diagram s →
    domain-dependent-span-diagram (left-map-span-diagram 𝒮 s)
  left-map-dependent-span-diagram = pr1 (pr2 (pr2 (pr2 𝒯)))

  right-map-dependent-span-diagram :
    (s : spanning-type-span-diagram 𝒮) →
    spanning-type-dependent-span-diagram s →
    codomain-dependent-span-diagram (right-map-span-diagram 𝒮 s)
  right-map-dependent-span-diagram = pr2 (pr2 (pr2 (pr2 𝒯)))
```

### Display span diagrams of dependent span diagrams

```agda
module _
  {l1 l2 l3 l4 l5 l6 : Level}
  (𝒮 : span-diagram l1 l2 l3) (𝒯 : dependent-span-diagram l4 l5 l6 𝒮)
  (s : spanning-type-span-diagram 𝒮)
  where

  domain-display-dependent-span-diagram : UU l4
  domain-display-dependent-span-diagram =
    domain-dependent-span-diagram 𝒯 (left-map-span-diagram 𝒮 s)

  codomain-display-dependent-span-diagram : UU l5
  codomain-display-dependent-span-diagram =
    codomain-dependent-span-diagram 𝒯 (right-map-span-diagram 𝒮 s)

  spanning-type-display-dependent-span-diagram : UU l6
  spanning-type-display-dependent-span-diagram =
    spanning-type-dependent-span-diagram 𝒯 s

  left-map-display-dependent-span-diagram :
    spanning-type-display-dependent-span-diagram →
    domain-display-dependent-span-diagram
  left-map-display-dependent-span-diagram =
    left-map-dependent-span-diagram 𝒯 s

  right-map-display-dependent-span-diagram :
    spanning-type-display-dependent-span-diagram →
    codomain-display-dependent-span-diagram
  right-map-display-dependent-span-diagram =
    right-map-dependent-span-diagram 𝒯 s

  span-display-dependent-span-diagram :
    span l6
      ( domain-display-dependent-span-diagram)
      ( codomain-display-dependent-span-diagram)
  pr1 span-display-dependent-span-diagram =
    spanning-type-display-dependent-span-diagram
  pr1 (pr2 span-display-dependent-span-diagram) =
    left-map-display-dependent-span-diagram
  pr2 (pr2 span-display-dependent-span-diagram) =
    right-map-display-dependent-span-diagram

  display-dependent-span-diagram : span-diagram l4 l5 l6
  pr1 display-dependent-span-diagram =
    domain-display-dependent-span-diagram
  pr1 (pr2 display-dependent-span-diagram) =
    codomain-display-dependent-span-diagram
  pr2 (pr2 display-dependent-span-diagram) =
    span-display-dependent-span-diagram
```
