# Tangent spheres

```agda
module synthetic-homotopy-theory.tangent-spheres where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.commuting-squares-of-maps
open import foundation.dependent-pair-types
open import foundation.mere-equivalences
open import foundation.unit-type
open import foundation.universe-levels

open import synthetic-homotopy-theory.cocones-under-spans
open import synthetic-homotopy-theory.mere-spheres
open import synthetic-homotopy-theory.pushouts
open import synthetic-homotopy-theory.spheres
```

</details>

## Idea

Consider a type `X` and a point `x : X`. We say that `x` **has a tangent
`n`-sphere** if we can construct the following data:

- A [mere sphere](synthetic-homotopy-theory.mere-spheres.md) `T`, which we also
  refer to as the **tangent sphere** of `x`.
- A type `C`, which we call the **complement** of `x`.
- A map `j : T → C` including the tangent sphere into the complement.
- A map `i : C → X` including the complement into the type `X`.
- A [homotopy](foundation-core.homotopies.md) witnessing that the square
  ```text
        j
    T -----> C
    |        |
    |        | i
    ∨      ⌜ ∨
    1 -----> X
        x
  ```
  [commutes](foundation.commuting-squares-of-maps.md), and is a
  [pushout](synthetic-homotopy-theory.pushouts.md).

In other words, a tangent `n`-sphere at a point `x` consistst of a mere sphere
and a complement such that the space `X` can be reconstructed by attaching the
point to the complement via the inclusion of the tangent sphere into the
complement.

## Definitions

### The predicate of having a tangent sphere

```agda
module _
  {l : Level} (n : ℕ) {X : UU l} (x : X)
  where

  has-tangent-sphere : UU (lsuc l)
  has-tangent-sphere =
    Σ ( mere-sphere lzero n)
      ( λ T →
        Σ ( UU l)
          ( λ C →
            Σ ( type-mere-sphere n T → C)
              ( λ j →
                Σ ( C → X)
                  ( λ i →
                    Σ ( coherence-square-maps
                        ( j)
                        ( terminal-map (type-mere-sphere n T))
                        ( i)
                        ( point x))
                      ( λ H →
                        is-pushout
                          ( terminal-map (type-mere-sphere n T))
                          ( j)
                          ( point x , i , H))))))

module _
  {l : Level} (n : ℕ) {X : UU l} {x : X} (T : has-tangent-sphere n x)
  where

  tangent-sphere-has-tangent-sphere : mere-sphere lzero n
  tangent-sphere-has-tangent-sphere = pr1 T

  type-tangent-sphere-has-tangent-sphere : UU lzero
  type-tangent-sphere-has-tangent-sphere =
    type-mere-sphere n tangent-sphere-has-tangent-sphere

  mere-equiv-tangent-sphere-has-tangent-sphere :
    mere-equiv (sphere n) type-tangent-sphere-has-tangent-sphere
  mere-equiv-tangent-sphere-has-tangent-sphere =
    mere-equiv-mere-sphere n tangent-sphere-has-tangent-sphere

  complement-has-tangent-sphere : UU l
  complement-has-tangent-sphere = pr1 (pr2 T)

  inclusion-tangent-sphere-has-tangent-sphere :
    type-tangent-sphere-has-tangent-sphere → complement-has-tangent-sphere
  inclusion-tangent-sphere-has-tangent-sphere = pr1 (pr2 (pr2 T))

  inclusion-complement-has-tangent-sphere :
    complement-has-tangent-sphere → X
  inclusion-complement-has-tangent-sphere = pr1 (pr2 (pr2 (pr2 T)))

  coherence-square-has-tangent-sphere :
    coherence-square-maps
      ( inclusion-tangent-sphere-has-tangent-sphere)
      ( terminal-map type-tangent-sphere-has-tangent-sphere)
      ( inclusion-complement-has-tangent-sphere)
      ( point x)
  coherence-square-has-tangent-sphere =
    pr1 (pr2 (pr2 (pr2 (pr2 T))))

  cocone-has-tangent-sphere :
    cocone
      ( terminal-map type-tangent-sphere-has-tangent-sphere)
      ( inclusion-tangent-sphere-has-tangent-sphere)
      ( X)
  pr1 cocone-has-tangent-sphere = point x
  pr1 (pr2 cocone-has-tangent-sphere) = inclusion-complement-has-tangent-sphere
  pr2 (pr2 cocone-has-tangent-sphere) = coherence-square-has-tangent-sphere

  is-pushout-has-tangent-sphere :
    is-pushout
      ( terminal-map type-tangent-sphere-has-tangent-sphere)
      ( inclusion-tangent-sphere-has-tangent-sphere)
      ( cocone-has-tangent-sphere)
  is-pushout-has-tangent-sphere =
    pr2 (pr2 (pr2 (pr2 (pr2 T))))
```
