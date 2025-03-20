# Reflective Galois connections between large posets

```agda
open import foundation.function-extensionality-axiom

module
  order-theory.reflective-galois-connections-large-posets
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types funext
open import foundation.universe-levels

open import order-theory.galois-connections-large-posets funext
open import order-theory.large-posets funext
open import order-theory.order-preserving-maps-large-posets funext
```

</details>

## Idea

A **reflective galois connection** between
[large posets](order-theory.large-posets.md) `P` and `Q` is a
[Galois connection](order-theory.galois-connections-large-posets.md)
`f : P ⇆ Q : g` such that `f ∘ g : Q → P` is the identity map.

## Definitions

### The predicate of being a reflective Galois connection

```agda
module _
  {αP αQ γ δ : Level → Level} {βP βQ : Level → Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  (G : galois-connection-Large-Poset γ δ P Q)
  where

  private
    f = map-lower-adjoint-galois-connection-Large-Poset P Q G
    g = map-upper-adjoint-galois-connection-Large-Poset P Q G

  is-reflective-galois-connection-Large-Poset : UUω
  is-reflective-galois-connection-Large-Poset =
    {l : Level} (x : type-Large-Poset Q l) →
    leq-Large-Poset Q (f (g x)) x ×
    leq-Large-Poset Q x (f (g x))
```

### The type of reflective Galois connections

```agda
module _
  {αP αQ : Level → Level} {βP βQ : Level → Level → Level}
  {γ δ : Level → Level}
  (P : Large-Poset αP βP) (Q : Large-Poset αQ βQ)
  where

  record reflective-galois-connection-Large-Poset : UUω
    where
    field
      galois-connection-reflective-galois-connection-Large-Poset :
        galois-connection-Large-Poset γ δ P Q
      is-reflective-reflective-galois-connection-Large-Poset :
        is-reflective-galois-connection-Large-Poset P Q
          galois-connection-reflective-galois-connection-Large-Poset

  open reflective-galois-connection-Large-Poset public

  module _
    (G : reflective-galois-connection-Large-Poset)
    where

    lower-adjoint-reflective-galois-connection-Large-Poset :
      hom-Large-Poset γ P Q
    lower-adjoint-reflective-galois-connection-Large-Poset =
      lower-adjoint-galois-connection-Large-Poset
        ( galois-connection-reflective-galois-connection-Large-Poset G)
```
