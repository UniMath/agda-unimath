# Algebraic theories

```agda
module universal-algebra.algebraic-theories where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.universe-levels

open import universal-algebra.abstract-equations-over-signatures
open import universal-algebra.signatures
```

</details>

## Idea

An algebraic theory is a collection of abstract equations over a signature `σ`
that we consider to 'hold' in the theory. It is algebraic in the sense that we
only require equations involving function symbols from the signature, in
contrast to, say, requiring additional types of relations.

## Definitions

### Theories

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  Theory : (l2 : Level) → UU (l1 ⊔ lsuc l2)
  Theory l2 = Σ (UU l2) (λ B → (B → Abstract-Equation σ))

  index-Theory : {l2 : Level} → Theory l2 → UU l2
  index-Theory = pr1

  index-Abstract-Equation-Theory :
    { l2 : Level}
    ( Th : Theory l2) →
    ( index-Theory Th) →
    Abstract-Equation σ
  index-Abstract-Equation-Theory Th e = pr2 Th e
```
