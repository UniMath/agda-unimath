# Algebras for polynomial endofunctors

```agda
module trees.algebras-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import trees.polynomial-endofunctors
```

</details>

## Idea

Given a [polynomial endofunctor](trees.polynomial-endofunctors.md) `P`, an
{{#concept "algebra" Disambiguation="of a polynomial endofunctor on types" Agda=algebra-polynomial-endofunctor}}
for `P` consists of a type `X` and a map `P(X) → X`.

## Definitions

### Algebras for polynomial endofunctors

```agda
algebra-polynomial-endofunctor :
  (l : Level) {l1 l2 : Level} →
  polynomial-endofunctor l1 l2 →
  UU (lsuc l ⊔ l1 ⊔ l2)
algebra-polynomial-endofunctor l P =
  Σ (UU l) (λ X → type-polynomial-endofunctor P X → X)

module _
  {l l1 l2 : Level} {P : polynomial-endofunctor l1 l2}
  where

  type-algebra-polynomial-endofunctor :
    algebra-polynomial-endofunctor l P → UU l
  type-algebra-polynomial-endofunctor X = pr1 X

  structure-algebra-polynomial-endofunctor :
    (X : algebra-polynomial-endofunctor l P) →
    type-polynomial-endofunctor P (type-algebra-polynomial-endofunctor X) →
    type-algebra-polynomial-endofunctor X
  structure-algebra-polynomial-endofunctor X = pr2 X
```
