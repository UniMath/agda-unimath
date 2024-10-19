# The Knaster–Tarski fixed point theorem

```agda
module order-theory.knaster-tarski-fixed-point-theorem where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.large-binary-relations
open import foundation.sets
open import foundation.logical-equivalences
open import foundation.fixed-points-endofunctions
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-large-posets
open import order-theory.large-meet-semilattices
open import order-theory.large-posets
open import order-theory.large-preorders
open import order-theory.large-suplattices
open import order-theory.order-preserving-maps-posets
open import order-theory.least-upper-bounds-large-posets
open import order-theory.meet-semilattices
open import order-theory.posets
open import order-theory.preorders
open import order-theory.suplattices
open import order-theory.top-elements-large-posets
open import order-theory.upper-bounds-large-posets
```

</details>

## Idea

The
{{#concept "Knaster–Tarski fixed point theorem" WD="Knaster–Tarski theorem" WDID=Q609612}}
states that every order preserving endomap `f : 𝒜 → 𝒜` on a complete lattice has
a least and a greatest [fixed point](foundation.fixed-points-endofunctions.md).

## Theorem

### The Knaster–Tarski fixed point theorem for suplattices

```agda
module _
  {l1 l2 l3 : Level}
  (𝒜 : Suplattice l1 l2 (l1 ⊔ l2))
  (f : type-Suplattice 𝒜 → type-Suplattice 𝒜)
  (F : preserves-order-Poset (poset-Suplattice 𝒜) (poset-Suplattice 𝒜) f)
  where

  indexing-type-family-of-elements-knaster-tarski-Suplattice : UU (l1 ⊔ l2)
  indexing-type-family-of-elements-knaster-tarski-Suplattice =
    Σ ( type-Suplattice 𝒜) (λ x → leq-Suplattice 𝒜 x (f x))

  family-of-elements-knaster-tarski-Suplattice :
    indexing-type-family-of-elements-knaster-tarski-Suplattice →
    type-Suplattice 𝒜
  family-of-elements-knaster-tarski-Suplattice = pr1

  point-knaster-tarski-Suplattice : type-Suplattice 𝒜
  point-knaster-tarski-Suplattice =
    sup-Suplattice 𝒜 family-of-elements-knaster-tarski-Suplattice

  leq-point-knaster-tarski-Suplattice :
    leq-Suplattice 𝒜
      ( point-knaster-tarski-Suplattice)
      ( f point-knaster-tarski-Suplattice)
  leq-point-knaster-tarski-Suplattice =
    forward-implication
      ( is-least-upper-bound-sup-Suplattice 𝒜
        ( family-of-elements-knaster-tarski-Suplattice)
        ( f point-knaster-tarski-Suplattice))
      ( λ w →
        transitive-leq-Suplattice 𝒜 _ _ _
          ( F ( pr1 w)
              ( point-knaster-tarski-Suplattice)
              ( leq-sup-Suplattice 𝒜 _ w))
          ( pr2 w))

  geq-point-knaster-tarski-Suplattice :
    leq-Suplattice 𝒜
      ( f point-knaster-tarski-Suplattice)
      ( point-knaster-tarski-Suplattice)
  geq-point-knaster-tarski-Suplattice =
    leq-sup-Suplattice 𝒜 family-of-elements-knaster-tarski-Suplattice
      ( f point-knaster-tarski-Suplattice ,
        F point-knaster-tarski-Suplattice
          ( f point-knaster-tarski-Suplattice)
          ( leq-point-knaster-tarski-Suplattice))

  is-fixed-point-knaster-tarski-Suplattice :
    f ( point-knaster-tarski-Suplattice) ＝
    point-knaster-tarski-Suplattice
  is-fixed-point-knaster-tarski-Suplattice =
    antisymmetric-leq-Suplattice 𝒜
      ( f (point-knaster-tarski-Suplattice))
      ( point-knaster-tarski-Suplattice)
      ( geq-point-knaster-tarski-Suplattice)
      ( leq-point-knaster-tarski-Suplattice)

  fixed-point-knaster-tarski-Suplattice : fixed-point f
  fixed-point-knaster-tarski-Suplattice =
    point-knaster-tarski-Suplattice ,
    is-fixed-point-knaster-tarski-Suplattice

  greatest-fixed-point-knaster-tarski-Suplattice :
    (x : fixed-point f) →
    leq-Suplattice 𝒜 (pr1 x) point-knaster-tarski-Suplattice
  greatest-fixed-point-knaster-tarski-Suplattice (x , p) =
    leq-sup-Suplattice 𝒜 _
      ( x ,
        concatenate-leq-eq-Poset
          ( poset-Suplattice 𝒜)
          ( refl-leq-Suplattice 𝒜 x)
          ( inv p))
```

## References

- <https://gist.github.com/TOTBWF/6890425f52066fa3bbfdd3e629565a4e> by Reed
  Mullanix

## External links

- [Knaster–Tarski theorem](https://en.wikipedia.org/wiki/Knaster%E2%80%93Tarski_theorem)
  at Wikipedia
- [Tarski's Fixed Point Theorem](https://mathworld.wolfram.com/TarskisFixedPointTheorem.html)
  at Wolfram MathWorld
