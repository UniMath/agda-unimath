# Orientations of cubes

```agda
open import foundation.function-extensionality-axiom

module
  univalent-combinatorics.orientations-cubes
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.identity-types funext
open import foundation.iterating-functions funext
open import foundation.universe-levels

open import univalent-combinatorics.cubes funext
open import univalent-combinatorics.dependent-pair-types funext
open import univalent-combinatorics.equality-finite-types funext
open import univalent-combinatorics.finite-types funext
open import univalent-combinatorics.function-types funext
open import univalent-combinatorics.standard-finite-types funext
```

</details>

## Definition

```agda
orientation-cube : {k : ℕ} → cube k → UU (lzero)
orientation-cube {k} X =
  Σ ( vertex-cube k X → Fin 2)
    ( λ h →
      ( x y : vertex-cube k X) →
        Id
          ( iterate
            ( number-of-elements-is-finite
              ( is-finite-Σ
                ( is-finite-dim-cube k X)
                ( λ d →
                  is-finite-function-type
                    ( is-finite-eq
                      ( has-decidable-equality-is-finite
                        ( is-finite-axis-cube k X d))
                    { x d}
                    { y d})
                    ( is-finite-empty))))
            ( succ-Fin 2)
            ( h x))
          ( h y))
```
