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

An
{{#concept "algebraic theory" Disambiguation="single-sorted, finitary" WD="algebraic theory" WDID=Q4724020 Agda=Algebraic-Theory}}
is a [collection](foundation.dependent-pair-types.md) of
[abstract equations](universal-algebra.abstract-equations-over-signatures.md)
over a [(finitary) signature](universal-algebra.signatures.md) `σ` that we
consider to 'hold' in the theory. It is algebraic in the sense that we only
require equations involving function symbols from the signature, in contrast to,
say, requiring additional types of relations.

## Definitions

### Theories

```agda
module _
  {l1 : Level} (σ : signature l1)
  where

  Algebraic-Theory : (l2 : Level) → UU (l1 ⊔ lsuc l2)
  Algebraic-Theory l2 = Σ (UU l2) (λ B → (B → abstract-equation σ))

  index-Algebraic-Theory : {l2 : Level} → Algebraic-Theory l2 → UU l2
  index-Algebraic-Theory = pr1

  index-abstract-equation-Algebraic-Theory :
    {l2 : Level} (Th : Algebraic-Theory l2) →
    index-Algebraic-Theory Th → abstract-equation σ
  index-abstract-equation-Algebraic-Theory = pr2
```
