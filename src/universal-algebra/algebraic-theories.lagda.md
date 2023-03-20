# Algebraic theories

```agda
module universal-algebra.algebraic-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import universal-algebra.abstract-equations
open import universal-algebra.signatures
```

</details>

## Idea

A theory is a family of abstract equations that should hold.

## Definitions

### Theories

```agda
module _ {l1 : Level} (Sig : signature l1) where

  Theory : (l2 : Level) → UU (l1 ⊔ lsuc l2)
  Theory l2 = Σ (UU l2) (λ B → (B → Abstract-Equation Sig))

  index-Theory : {l2 : Level} → Theory l2 → UU l2
  index-Theory = pr1

  index-Abstract-Equation-Theory :
    { l2 : Level}
    ( Th : Theory l2) →
    ( index-Theory Th) →
    Abstract-Equation Sig
  index-Abstract-Equation-Theory Th e = pr2 Th e
```
