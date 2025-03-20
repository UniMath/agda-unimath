# Functoriality of the type of matrices

```agda
open import foundation.function-extensionality-axiom

module
  linear-algebra.functoriality-matrices
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.universe-levels

open import linear-algebra.functoriality-vectors funext
open import linear-algebra.matrices funext
```

</details>

## Idea

Any map `f : A → B` induces a map `matrix A m n → matrix B m n`.

## Definition

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2} (f : A → B)
  where

  map-matrix : {m n : ℕ} → matrix A m n → matrix B m n
  map-matrix = map-vec (map-vec f)
```

### Binar maps

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {B : UU l2} {C : UU l3} (f : A → B → C)
  where

  binary-map-matrix :
    {m n : ℕ} → matrix A m n → matrix B m n → matrix C m n
  binary-map-matrix = binary-map-vec (binary-map-vec f)
```
