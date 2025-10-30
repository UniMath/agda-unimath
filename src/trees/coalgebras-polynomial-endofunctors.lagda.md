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

**Coalgebras** for polynomial endofunctors are types `X` equipped with a
function

```text
  X → Σ (a : A), B a → X
```

## Definitions

```agda
module _
  {l1 l2 : Level} (l : Level) (A : UU l1) (B : A → UU l2)
  where

  coalgebra-polynomial-endofunctor : UU (l1 ⊔ l2 ⊔ lsuc l)
  coalgebra-polynomial-endofunctor =
    Σ (UU l) (λ X → X → type-polynomial-endofunctor' A B X)

module _
  {l1 l2 l3 : Level} {A : UU l1} {B : A → UU l2}
  (X : coalgebra-polynomial-endofunctor l3 A B)
  where

  type-coalgebra-polynomial-endofunctor : UU l3
  type-coalgebra-polynomial-endofunctor = pr1 X

  structure-coalgebra-polynomial-endofunctor :
    type-coalgebra-polynomial-endofunctor →
    type-polynomial-endofunctor' A B type-coalgebra-polynomial-endofunctor
  structure-coalgebra-polynomial-endofunctor = pr2 X

  shape-coalgebra-polynomial-endofunctor :
    type-coalgebra-polynomial-endofunctor → A
  shape-coalgebra-polynomial-endofunctor x =
    pr1 (structure-coalgebra-polynomial-endofunctor x)

  component-coalgebra-polynomial-endofunctor :
    (x : type-coalgebra-polynomial-endofunctor) →
    B (shape-coalgebra-polynomial-endofunctor x) →
    type-coalgebra-polynomial-endofunctor
  component-coalgebra-polynomial-endofunctor x =
    pr2 (structure-coalgebra-polynomial-endofunctor x)
```
