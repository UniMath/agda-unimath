# Algebras for polynomial endofunctors

```agda
module trees.algebras-polynomial-endofunctors where
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.functions
open import foundation.functoriality-dependent-pair-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.homotopies
open import foundation.identity-types
open import foundation.structure-identity-principle
open import foundation.universe-levels

open import trees.polynomial-endofunctors
```

</details>

## Idea

Given a polynomial endofunctor `P A B`, an **algebra** for `P A B` conisists of
a type `X` and a map `P A B X → X`.

## Definitions

### Algebras for polynomial endofunctors

```agda
algebra-polynomial-endofunctor :
  (l : Level) {l1 l2 : Level} (A : UU l1) (B : A → UU l2) →
  UU (lsuc l ⊔ l1 ⊔ l2)
algebra-polynomial-endofunctor l A B =
  Σ (UU l) (λ X → type-polynomial-endofunctor A B X → X)

type-algebra-polynomial-endofunctor :
  {l l1 l2 : Level} {A : UU l1} {B : A → UU l2} →
  algebra-polynomial-endofunctor l A B → UU l
type-algebra-polynomial-endofunctor X = pr1 X

structure-algebra-polynomial-endofunctor :
  {l l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  (X : algebra-polynomial-endofunctor l A B) →
  type-polynomial-endofunctor A B (type-algebra-polynomial-endofunctor X) →
  type-algebra-polynomial-endofunctor X
structure-algebra-polynomial-endofunctor X = pr2 X
```
