# Galois connections

```agda
module order-theory.galois-connections where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.subtype-identity-principle
open import foundation.subtypes
open import foundation.universe-levels

open import order-theory.order-preserving-maps-posets
open import order-theory.posets
```

</details>

## Idea

A **Galois connection** between [posets](order-theory.posets.md) `P` and `Q` is
a pair of order preserving maps `f : P → Q` and `g : Q → P` such that the
[logical equivalence](foundation.logical-equivalences.md)

```text
  (f x ≤ y) ↔ (x ≤ g y)
```

holds for any `x : P` and `y : Q`.

## Definitions

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  adjoint-relation-galois-connection-Prop :
    hom-Poset P Q → hom-Poset Q P → Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  adjoint-relation-galois-connection-Prop f g =
    Π-Prop
      ( type-Poset P)
      ( λ x →
        Π-Prop
          ( type-Poset Q)
          ( λ y →
            iff-Prop
              ( leq-prop-Poset Q (map-hom-Poset P Q f x) y)
              ( leq-prop-Poset P x (map-hom-Poset Q P g y))))

  is-lower-adjoint-Galois-Connection :
    hom-Poset P Q → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-lower-adjoint-Galois-Connection f =
    type-subtype (adjoint-relation-galois-connection-Prop f)

  is-upper-adjoint-Galois-Connection :
    hom-Poset Q P → UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  is-upper-adjoint-Galois-Connection g =
    type-subtype (λ f → adjoint-relation-galois-connection-Prop f g)

  Galois-Connection : UU (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  Galois-Connection =
    Σ ( hom-Poset Q P) is-upper-adjoint-Galois-Connection

  module _
    (G : Galois-Connection)
    where

    upper-adjoint-Galois-Connection : hom-Poset Q P
    upper-adjoint-Galois-Connection = pr1 G

    map-upper-adjoint-Galois-Connection :
      type-Poset Q → type-Poset P
    map-upper-adjoint-Galois-Connection =
      map-hom-Poset Q P upper-adjoint-Galois-Connection

    preserves-order-upper-adjoint-Galois-Connection :
      preserves-order-Poset Q P map-upper-adjoint-Galois-Connection
    preserves-order-upper-adjoint-Galois-Connection =
      preserves-order-hom-Poset Q P upper-adjoint-Galois-Connection

    is-upper-adjoint-upper-adjoint-Galois-Connection :
      is-upper-adjoint-Galois-Connection upper-adjoint-Galois-Connection
    is-upper-adjoint-upper-adjoint-Galois-Connection = pr2 G

    lower-adjoint-Galois-Connection : hom-Poset P Q
    lower-adjoint-Galois-Connection =
      pr1 is-upper-adjoint-upper-adjoint-Galois-Connection

    map-lower-adjoint-Galois-Connection :
      type-Poset P → type-Poset Q
    map-lower-adjoint-Galois-Connection =
      map-hom-Poset P Q lower-adjoint-Galois-Connection

    preserves-order-lower-adjoint-Galois-Connection :
      preserves-order-Poset P Q map-lower-adjoint-Galois-Connection
    preserves-order-lower-adjoint-Galois-Connection =
      preserves-order-hom-Poset P Q lower-adjoint-Galois-Connection

    adjoint-relation-Galois-Connection :
      (x : type-Poset P) (y : type-Poset Q) →
      leq-Poset Q (map-lower-adjoint-Galois-Connection x) y ↔
      leq-Poset P x (map-upper-adjoint-Galois-Connection y)
    adjoint-relation-Galois-Connection =
      pr2 is-upper-adjoint-upper-adjoint-Galois-Connection

    map-adjoint-relation-Galois-Connection :
      (x : type-Poset P) (y : type-Poset Q) →
      leq-Poset Q (map-lower-adjoint-Galois-Connection x) y →
      leq-Poset P x (map-upper-adjoint-Galois-Connection y)
    map-adjoint-relation-Galois-Connection x y =
      forward-implication (adjoint-relation-Galois-Connection x y)

    map-inv-adjoint-relation-Galois-Connection :
      (x : type-Poset P) (y : type-Poset Q) →
      leq-Poset P x (map-upper-adjoint-Galois-Connection y) →
      leq-Poset Q (map-lower-adjoint-Galois-Connection x) y
    map-inv-adjoint-relation-Galois-Connection x y =
      backward-implication (adjoint-relation-Galois-Connection x y)

    is-lower-adjoint-lower-adjoint-Galois-Connection :
      is-lower-adjoint-Galois-Connection lower-adjoint-Galois-Connection
    pr1 is-lower-adjoint-lower-adjoint-Galois-Connection =
      upper-adjoint-Galois-Connection
    pr2 is-lower-adjoint-lower-adjoint-Galois-Connection =
      adjoint-relation-Galois-Connection
```

## Properties

### Being a lower adjoint of a Galois connection is a property

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (f : hom-Poset P Q)
  where

  htpy-is-lower-adjoint-Galois-Connection :
    (g h : is-lower-adjoint-Galois-Connection P Q f) → UU (l1 ⊔ l3)
  htpy-is-lower-adjoint-Galois-Connection (g , G) (h , H) =
    htpy-hom-Poset Q P g h

  refl-htpy-is-lower-adjoint-Galois-Connection :
    (g : is-lower-adjoint-Galois-Connection P Q f) →
    htpy-is-lower-adjoint-Galois-Connection g g
  refl-htpy-is-lower-adjoint-Galois-Connection (g , G) =
    refl-htpy-hom-Poset Q P g

  extensionality-is-lower-adjoint-Galois-Connection :
    (g h : is-lower-adjoint-Galois-Connection P Q f) →
    (g ＝ h) ≃ htpy-is-lower-adjoint-Galois-Connection g h
  extensionality-is-lower-adjoint-Galois-Connection (g , G) =
    extensionality-type-subtype
      ( adjoint-relation-galois-connection-Prop P Q f)
      ( G)
      ( refl-htpy-is-lower-adjoint-Galois-Connection (g , G))
      ( extensionality-hom-Poset Q P g)

  eq-htpy-is-lower-adjoint-Galois-Connection :
    (g h : is-lower-adjoint-Galois-Connection P Q f) →
    htpy-is-lower-adjoint-Galois-Connection g h → g ＝ h
  eq-htpy-is-lower-adjoint-Galois-Connection g h =
    map-inv-equiv (extensionality-is-lower-adjoint-Galois-Connection g h)

  all-elements-equal-is-lower-adjoint-Galois-Connection :
    (g h : is-lower-adjoint-Galois-Connection P Q f) → g ＝ h
  all-elements-equal-is-lower-adjoint-Galois-Connection (g , G) (h , H) =
    eq-htpy-is-lower-adjoint-Galois-Connection
      ( g , G)
      ( h , H)
      ( λ y →
        antisymmetric-leq-Poset P
          ( map-hom-Poset Q P g y)
          ( map-hom-Poset Q P h y)
          ( forward-implication
            ( H (map-hom-Poset Q P g y) y)
            ( backward-implication
              ( G (map-hom-Poset Q P g y) y)
              ( refl-leq-Poset P (map-hom-Poset Q P g y))))
          ( forward-implication
            ( G (map-hom-Poset Q P h y) y)
            ( backward-implication
              ( H (map-hom-Poset Q P h y) y)
              ( refl-leq-Poset P (map-hom-Poset Q P h y)))))

  is-prop-is-lower-adjoint-Galois-Connection :
    is-prop (is-lower-adjoint-Galois-Connection P Q f)
  is-prop-is-lower-adjoint-Galois-Connection =
    is-prop-all-elements-equal
      all-elements-equal-is-lower-adjoint-Galois-Connection

  is-lower-adjoint-galois-connection-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-lower-adjoint-galois-connection-Prop =
    is-lower-adjoint-Galois-Connection P Q f
  pr2 is-lower-adjoint-galois-connection-Prop =
    is-prop-is-lower-adjoint-Galois-Connection
```

### Being a upper adjoint of a Galois connection is a property

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (g : hom-Poset Q P)
  where

  htpy-is-upper-adjoint-Galois-Connection :
    (f h : is-upper-adjoint-Galois-Connection P Q g) → UU (l1 ⊔ l3)
  htpy-is-upper-adjoint-Galois-Connection (f , F) (h , H) =
    htpy-hom-Poset P Q f h

  refl-htpy-is-upper-adjoint-Galois-Connection :
    (f : is-upper-adjoint-Galois-Connection P Q g) →
    htpy-is-upper-adjoint-Galois-Connection f f
  refl-htpy-is-upper-adjoint-Galois-Connection (f , F) =
    refl-htpy-hom-Poset P Q f

  extensionality-is-upper-adjoint-Galois-Connection :
    (f h : is-upper-adjoint-Galois-Connection P Q g) →
    (f ＝ h) ≃ htpy-is-upper-adjoint-Galois-Connection f h
  extensionality-is-upper-adjoint-Galois-Connection (f , F) =
    extensionality-type-subtype
      ( λ u → adjoint-relation-galois-connection-Prop P Q u g)
      ( F)
      ( refl-htpy-is-upper-adjoint-Galois-Connection (f , F))
      ( extensionality-hom-Poset P Q f)

  eq-htpy-is-upper-adjoint-Galois-Connection :
    (f h : is-upper-adjoint-Galois-Connection P Q g) →
    htpy-is-upper-adjoint-Galois-Connection f h → f ＝ h
  eq-htpy-is-upper-adjoint-Galois-Connection f h =
    map-inv-equiv (extensionality-is-upper-adjoint-Galois-Connection f h)

  all-elements-equal-is-upper-adjoint-Galois-Connection :
    (f h : is-upper-adjoint-Galois-Connection P Q g) → f ＝ h
  all-elements-equal-is-upper-adjoint-Galois-Connection (f , F) (h , H) =
    eq-htpy-is-upper-adjoint-Galois-Connection
      ( f , F)
      ( h , H)
      ( λ x →
        antisymmetric-leq-Poset Q
          ( map-hom-Poset P Q f x)
          ( map-hom-Poset P Q h x)
          ( backward-implication
            ( F x (map-hom-Poset P Q h x))
            ( forward-implication
              ( H x (map-hom-Poset P Q h x))
              ( refl-leq-Poset Q (map-hom-Poset P Q h x))))
          ( backward-implication
            ( H x (map-hom-Poset P Q f x))
            ( forward-implication
              ( F x (map-hom-Poset P Q f x))
              ( refl-leq-Poset Q (map-hom-Poset P Q f x)))))

  is-prop-is-upper-adjoint-Galois-Connection :
    is-prop (is-upper-adjoint-Galois-Connection P Q g)
  is-prop-is-upper-adjoint-Galois-Connection =
    is-prop-all-elements-equal
      all-elements-equal-is-upper-adjoint-Galois-Connection

  is-upper-adjoint-galois-connection-Prop : Prop (l1 ⊔ l2 ⊔ l3 ⊔ l4)
  pr1 is-upper-adjoint-galois-connection-Prop =
    is-upper-adjoint-Galois-Connection P Q g
  pr2 is-upper-adjoint-galois-connection-Prop =
    is-prop-is-upper-adjoint-Galois-Connection
```

### Characterizing equalities of Galois connections

#### Characterizing equalities of Galois connections as homotopies of their upper adjoints

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  htpy-upper-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) → UU (l1 ⊔ l3)
  htpy-upper-adjoint-Galois-Connection G H =
    htpy-hom-Poset Q P
      ( upper-adjoint-Galois-Connection P Q G)
      ( upper-adjoint-Galois-Connection P Q H)

  is-prop-htpy-upper-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    is-prop (htpy-upper-adjoint-Galois-Connection G H)
  is-prop-htpy-upper-adjoint-Galois-Connection G H =
    is-prop-htpy-hom-Poset Q P
      ( upper-adjoint-Galois-Connection P Q G)
      ( upper-adjoint-Galois-Connection P Q H)

  extensionality-upper-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    (G ＝ H) ≃ htpy-upper-adjoint-Galois-Connection G H
  extensionality-upper-adjoint-Galois-Connection (g , G) =
    extensionality-type-subtype
      ( is-upper-adjoint-galois-connection-Prop P Q)
      ( G)
      ( refl-htpy-hom-Poset Q P g)
      ( extensionality-hom-Poset Q P g)

  eq-htpy-upper-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    htpy-upper-adjoint-Galois-Connection G H → G ＝ H
  eq-htpy-upper-adjoint-Galois-Connection G H =
    map-inv-equiv (extensionality-upper-adjoint-Galois-Connection G H)
```

#### Characterizing equalities of Galois connection by homotopies of their lower adjoints

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  where

  htpy-lower-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) → UU (l1 ⊔ l3)
  htpy-lower-adjoint-Galois-Connection G H =
    htpy-hom-Poset P Q
      ( lower-adjoint-Galois-Connection P Q G)
      ( lower-adjoint-Galois-Connection P Q H)

  is-prop-htpy-lower-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    is-prop (htpy-lower-adjoint-Galois-Connection G H)
  is-prop-htpy-lower-adjoint-Galois-Connection G H =
    is-prop-htpy-hom-Poset P Q
      ( lower-adjoint-Galois-Connection P Q G)
      ( lower-adjoint-Galois-Connection P Q H)

  htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    htpy-lower-adjoint-Galois-Connection G H →
    htpy-upper-adjoint-Galois-Connection P Q G H
  htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connection G H K y =
    antisymmetric-leq-Poset P
      ( map-upper-adjoint-Galois-Connection P Q G y)
      ( map-upper-adjoint-Galois-Connection P Q H y)
      ( map-adjoint-relation-Galois-Connection P Q H
        ( map-upper-adjoint-Galois-Connection P Q G y)
        ( y)
        ( concatenate-eq-leq-Poset Q
          ( inv (K (map-upper-adjoint-Galois-Connection P Q G y)))
          ( map-inv-adjoint-relation-Galois-Connection P Q G
            ( map-upper-adjoint-Galois-Connection P Q G y)
            ( y)
            ( refl-leq-Poset P (map-upper-adjoint-Galois-Connection P Q G y)))))
      ( map-adjoint-relation-Galois-Connection P Q G
        ( map-upper-adjoint-Galois-Connection P Q H y)
        ( y)
        ( concatenate-eq-leq-Poset Q
          ( K (map-upper-adjoint-Galois-Connection P Q H y))
          ( map-inv-adjoint-relation-Galois-Connection P Q H
            ( map-upper-adjoint-Galois-Connection P Q H y)
            ( y)
            ( refl-leq-Poset P (map-upper-adjoint-Galois-Connection P Q H y)))))

  htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    htpy-upper-adjoint-Galois-Connection P Q G H →
    htpy-lower-adjoint-Galois-Connection G H
  htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection G H K x =
    antisymmetric-leq-Poset Q
      ( map-lower-adjoint-Galois-Connection P Q G x)
      ( map-lower-adjoint-Galois-Connection P Q H x)
      ( map-inv-adjoint-relation-Galois-Connection P Q G x
        ( map-lower-adjoint-Galois-Connection P Q H x)
        ( concatenate-leq-eq-Poset P
          ( map-adjoint-relation-Galois-Connection P Q H x
            ( map-lower-adjoint-Galois-Connection P Q H x)
            ( refl-leq-Poset Q (map-lower-adjoint-Galois-Connection P Q H x)))
          ( inv (K (map-lower-adjoint-Galois-Connection P Q H x)))))
      ( map-inv-adjoint-relation-Galois-Connection P Q H x
        ( map-lower-adjoint-Galois-Connection P Q G x)
        ( concatenate-leq-eq-Poset P
          ( map-adjoint-relation-Galois-Connection P Q G x
            ( map-lower-adjoint-Galois-Connection P Q G x)
            ( refl-leq-Poset Q (map-lower-adjoint-Galois-Connection P Q G x)))
          ( K (map-lower-adjoint-Galois-Connection P Q G x))))

  is-equiv-htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    is-equiv (htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connection G H)
  is-equiv-htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connection G H =
    is-equiv-has-converse-is-prop
      ( is-prop-htpy-lower-adjoint-Galois-Connection G H)
      ( is-prop-htpy-upper-adjoint-Galois-Connection P Q G H)
      ( htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection G H)

  is-equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    is-equiv (htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection G H)
  is-equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection G H =
    is-equiv-has-converse-is-prop
      ( is-prop-htpy-upper-adjoint-Galois-Connection P Q G H)
      ( is-prop-htpy-lower-adjoint-Galois-Connection G H)
      ( htpy-upper-adjoint-htpy-lower-adjoint-Galois-Connection G H)

  equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    htpy-upper-adjoint-Galois-Connection P Q G H ≃
    htpy-lower-adjoint-Galois-Connection G H
  pr1 (equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection G H) =
    htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection G H
  pr2 (equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection G H) =
    is-equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection G H

  extensionality-lower-adjoint-Galois-Connection :
    (G H : Galois-Connection P Q) →
    (G ＝ H) ≃ htpy-lower-adjoint-Galois-Connection G H
  extensionality-lower-adjoint-Galois-Connection G H =
    equiv-htpy-lower-adjoint-htpy-upper-adjoint-Galois-Connection G H ∘e
    extensionality-upper-adjoint-Galois-Connection P Q G H
```

### `G y = GFG y` for any Galois connection `(G , F)`

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (G : Galois-Connection P Q)
  where

  compute-upper-lower-upper-adjoint-Galois-Connection :
    (y : type-Poset Q) →
    map-upper-adjoint-Galois-Connection P Q G y ＝
    map-upper-adjoint-Galois-Connection P Q G
      ( map-lower-adjoint-Galois-Connection P Q G
        ( map-upper-adjoint-Galois-Connection P Q G y))
  compute-upper-lower-upper-adjoint-Galois-Connection y =
    antisymmetric-leq-Poset P
      ( map-upper-adjoint-Galois-Connection P Q G y)
      ( map-upper-adjoint-Galois-Connection P Q G
        ( map-lower-adjoint-Galois-Connection P Q G
          ( map-upper-adjoint-Galois-Connection P Q G y)))
      ( map-adjoint-relation-Galois-Connection P Q G
        ( map-upper-adjoint-Galois-Connection P Q G y)
        ( map-lower-adjoint-Galois-Connection P Q G
          ( map-upper-adjoint-Galois-Connection P Q G y))
        ( refl-leq-Poset Q _))
      ( preserves-order-upper-adjoint-Galois-Connection P Q G
        ( map-lower-adjoint-Galois-Connection P Q G
          ( map-upper-adjoint-Galois-Connection P Q G y))
        ( y)
        ( map-inv-adjoint-relation-Galois-Connection P Q G
          ( map-upper-adjoint-Galois-Connection P Q G y)
          ( y)
          ( refl-leq-Poset P _)))
```

### `F x = FGF x` for any Galois connection `(G , F)`

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (G : Galois-Connection P Q)
  where

  compute-lower-upper-lower-adjoint-Galois-Connection :
    (x : type-Poset P) →
    map-lower-adjoint-Galois-Connection P Q G x ＝
    map-lower-adjoint-Galois-Connection P Q G
      ( map-upper-adjoint-Galois-Connection P Q G
        ( map-lower-adjoint-Galois-Connection P Q G x))
  compute-lower-upper-lower-adjoint-Galois-Connection x =
    antisymmetric-leq-Poset Q
      ( map-lower-adjoint-Galois-Connection P Q G x)
      ( map-lower-adjoint-Galois-Connection P Q G
        ( map-upper-adjoint-Galois-Connection P Q G
          ( map-lower-adjoint-Galois-Connection P Q G x)))
      ( preserves-order-lower-adjoint-Galois-Connection P Q G x
        ( map-upper-adjoint-Galois-Connection P Q G
          ( map-lower-adjoint-Galois-Connection P Q G x))
        ( map-adjoint-relation-Galois-Connection P Q G x
          ( map-lower-adjoint-Galois-Connection P Q G x)
          ( refl-leq-Poset Q _)))
      ( map-inv-adjoint-relation-Galois-Connection P Q G
        ( map-upper-adjoint-Galois-Connection P Q G
          ( map-lower-adjoint-Galois-Connection P Q G x))
        ( map-lower-adjoint-Galois-Connection P Q G x)
        ( refl-leq-Poset P _))
```

### The composite `FG` is idempotent for every Galois connection `(G , F)`

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (G : Galois-Connection P Q)
  where

  htpy-idempotent-lower-upper-Galois-Connection :
    htpy-hom-Poset Q Q
      ( comp-hom-Poset Q Q Q
        ( comp-hom-Poset Q P Q
          ( lower-adjoint-Galois-Connection P Q G)
          ( upper-adjoint-Galois-Connection P Q G))
        ( comp-hom-Poset Q P Q
          ( lower-adjoint-Galois-Connection P Q G)
          ( upper-adjoint-Galois-Connection P Q G)))
      ( comp-hom-Poset Q P Q
        ( lower-adjoint-Galois-Connection P Q G)
        ( upper-adjoint-Galois-Connection P Q G))
  htpy-idempotent-lower-upper-Galois-Connection x =
    ap
      ( map-lower-adjoint-Galois-Connection P Q G)
      ( inv
        ( compute-upper-lower-upper-adjoint-Galois-Connection P Q G x))
```

### The composite `GF` is idempotent for every Galois connection `(G , F)`

```agda
module _
  {l1 l2 l3 l4 : Level} (P : Poset l1 l2) (Q : Poset l3 l4)
  (G : Galois-Connection P Q)
  where

  htpy-idempotent-upper-lower-Galois-Connection :
    htpy-hom-Poset P P
      ( comp-hom-Poset P P P
        ( comp-hom-Poset P Q P
          ( upper-adjoint-Galois-Connection P Q G)
          ( lower-adjoint-Galois-Connection P Q G))
        ( comp-hom-Poset P Q P
          ( upper-adjoint-Galois-Connection P Q G)
          ( lower-adjoint-Galois-Connection P Q G)))
      ( comp-hom-Poset P Q P
        ( upper-adjoint-Galois-Connection P Q G)
        ( lower-adjoint-Galois-Connection P Q G))
  htpy-idempotent-upper-lower-Galois-Connection y =
    ap
      ( map-upper-adjoint-Galois-Connection P Q G)
      ( inv
        ( compute-lower-upper-lower-adjoint-Galois-Connection P Q G y))
```

## References

{{#bibliography}} {{#reference EKMS93}}
