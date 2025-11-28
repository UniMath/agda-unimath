# Cospan diagrams

```agda
module foundation.cospan-diagrams where
```

<details><summary>Imports</summary>

```agda
open import foundation.cospans
open import foundation.dependent-pair-types
open import foundation.universe-levels
```

</details>

## Idea

A {{#concept "cospan diagram" Agda=cospan-diagram}} consists of two types `A`
and `B` and a [cospan](foundation.cospans.md) `A -f-> X <-g- B` between them.

## Definitions

### Cospan diagrams

```agda
cospan-diagram :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
cospan-diagram l1 l2 l3 =
  Σ (UU l1) (λ A → Σ (UU l2) (cospan l3 A))

module _
  {l1 l2 l3 : Level} (c : cospan-diagram l1 l2 l3)
  where

  domain-cospan-diagram : UU l1
  domain-cospan-diagram = pr1 c

  codomain-cospan-diagram : UU l2
  codomain-cospan-diagram = pr1 (pr2 c)

  cospan-cospan-diagram :
    cospan l3 domain-cospan-diagram codomain-cospan-diagram
  cospan-cospan-diagram = pr2 (pr2 c)

  cospanning-type-cospan-diagram : UU l3
  cospanning-type-cospan-diagram = cospanning-type-cospan cospan-cospan-diagram

  left-map-cospan-diagram :
    domain-cospan-diagram → cospanning-type-cospan-diagram
  left-map-cospan-diagram = left-map-cospan cospan-cospan-diagram

  right-map-cospan-diagram :
    codomain-cospan-diagram → cospanning-type-cospan-diagram
  right-map-cospan-diagram = right-map-cospan cospan-cospan-diagram
```

### The identity cospan diagram

```agda
id-cospan-diagram : {l : Level} → UU l → cospan-diagram l l l
id-cospan-diagram A = (A , A , id-cospan A)
```

### The swapping operation on cospan diagrams

```agda
swap-cospan-diagram :
  {l1 l2 l3 : Level} → cospan-diagram l1 l2 l3 → cospan-diagram l2 l1 l3
swap-cospan-diagram (A , B , c) = (B , A , swap-cospan c)
```
