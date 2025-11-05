# Coalgebras of polynomial endofunctors

```agda
module trees.coalgebras-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import trees.polynomial-endofunctors
```

</details>

## Idea

{{#concept "Coalgebras" Disambiguation="of a polynomial endofunctor" Agda=coalgebra-polynomial-endofunctor}}
for a [polynomial endofunctor](trees.polynomial-endofunctors.md) `P` are types
`X` [equipped](foundation.structure.md) with a function `X → P(X)`.

## Definitions

```agda
module _
  {l1 l2 : Level} (l : Level) (P : polynomial-endofunctor l1 l2)
  where

  coalgebra-polynomial-endofunctor : UU (l1 ⊔ l2 ⊔ lsuc l)
  coalgebra-polynomial-endofunctor =
    Σ (UU l) (λ X → X → type-polynomial-endofunctor P X)

module _
  {l1 l2 l3 : Level} {P : polynomial-endofunctor l1 l2}
  (X : coalgebra-polynomial-endofunctor l3 P)
  where

  type-coalgebra-polynomial-endofunctor : UU l3
  type-coalgebra-polynomial-endofunctor = pr1 X

  structure-coalgebra-polynomial-endofunctor :
    type-coalgebra-polynomial-endofunctor →
    type-polynomial-endofunctor P type-coalgebra-polynomial-endofunctor
  structure-coalgebra-polynomial-endofunctor = pr2 X

  shape-coalgebra-polynomial-endofunctor :
    type-coalgebra-polynomial-endofunctor → shape-polynomial-endofunctor P
  shape-coalgebra-polynomial-endofunctor x =
    pr1 (structure-coalgebra-polynomial-endofunctor x)

  component-coalgebra-polynomial-endofunctor :
    (x : type-coalgebra-polynomial-endofunctor) →
    position-polynomial-endofunctor P
      ( shape-coalgebra-polynomial-endofunctor x) →
    type-coalgebra-polynomial-endofunctor
  component-coalgebra-polynomial-endofunctor x =
    pr2 (structure-coalgebra-polynomial-endofunctor x)
```
