# Suplattices

```agda
module order-theory.suplattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.least-upper-bounds-posets
open import order-theory.posets
open import order-theory.upper-bounds-posets
```

</details>

## Idea

Consider a [universe level](foundation.universe-levels.md) `l`. An
`l`-{{#concept "suplattice" Agda=Suplattice}} is a
[poset](order-theory.posets.md) which has all
[least upper bounds](order-theory.least-upper-bounds-posets.md) of families of
elements indexed by a type of universe level `l`.

## Definitions

### The predicate on posets of being an `l`-suplattice

```agda
module _
  {l1 l2 : Level} (l3 : Level) (P : Poset l1 l2)
  where

  is-suplattice-Poset-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-suplattice-Poset-Prop =
    Π-Prop
      (UU l3)
      ( λ I →
        Π-Prop
          ( I → type-Poset P)
          ( has-least-upper-bound-family-of-elements-prop-Poset P))

  is-suplattice-Poset : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-suplattice-Poset = type-Prop is-suplattice-Poset-Prop

  is-prop-is-suplattice-Poset : is-prop is-suplattice-Poset
  is-prop-is-suplattice-Poset = is-prop-type-Prop is-suplattice-Poset-Prop

module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) (H : is-suplattice-Poset l3 P)
  where

  sup-is-suplattice-Poset :
    {I : UU l3} → (I → type-Poset P) → type-Poset P
  sup-is-suplattice-Poset {I} x = pr1 (H I x)

  is-least-upper-bound-sup-is-suplattice-Poset :
    {I : UU l3} (x : I → type-Poset P) →
    is-least-upper-bound-family-of-elements-Poset P x
      ( sup-is-suplattice-Poset x)
  is-least-upper-bound-sup-is-suplattice-Poset {I} x = pr2 (H I x)
```

### `l`-Suplattices

```agda
Suplattice : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Suplattice l1 l2 l3 = Σ (Poset l1 l2) (λ P → is-suplattice-Poset l3 P)

module _
  {l1 l2 l3 : Level} (A : Suplattice l1 l2 l3)
  where

  poset-Suplattice : Poset l1 l2
  poset-Suplattice = pr1 A

  type-Suplattice : UU l1
  type-Suplattice = type-Poset poset-Suplattice

  leq-prop-Suplattice : (x y : type-Suplattice) → Prop l2
  leq-prop-Suplattice = leq-prop-Poset poset-Suplattice

  leq-Suplattice : (x y : type-Suplattice) → UU l2
  leq-Suplattice = leq-Poset poset-Suplattice

  is-prop-leq-Suplattice :
    (x y : type-Suplattice) → is-prop (leq-Suplattice x y)
  is-prop-leq-Suplattice = is-prop-leq-Poset poset-Suplattice

  refl-leq-Suplattice :
    (x : type-Suplattice) → leq-Suplattice x x
  refl-leq-Suplattice = refl-leq-Poset poset-Suplattice

  antisymmetric-leq-Suplattice : is-antisymmetric leq-Suplattice
  antisymmetric-leq-Suplattice =
    antisymmetric-leq-Poset poset-Suplattice

  transitive-leq-Suplattice : is-transitive leq-Suplattice
  transitive-leq-Suplattice = transitive-leq-Poset poset-Suplattice

  is-set-type-Suplattice : is-set type-Suplattice
  is-set-type-Suplattice = is-set-type-Poset poset-Suplattice

  set-Suplattice : Set l1
  set-Suplattice = set-Poset poset-Suplattice

  is-suplattice-Suplattice :
    is-suplattice-Poset l3 poset-Suplattice
  is-suplattice-Suplattice = pr2 A

  sup-Suplattice :
    {I : UU l3} → (I → type-Suplattice) → type-Suplattice
  sup-Suplattice =
    sup-is-suplattice-Poset
      ( poset-Suplattice)
      ( is-suplattice-Suplattice)

  is-least-upper-bound-sup-Suplattice :
    {I : UU l3} (x : I → type-Suplattice) →
    is-least-upper-bound-family-of-elements-Poset
      ( poset-Suplattice)
      ( x)
      ( sup-Suplattice x)
  is-least-upper-bound-sup-Suplattice =
    is-least-upper-bound-sup-is-suplattice-Poset
      ( poset-Suplattice)
      ( is-suplattice-Suplattice)

  is-upper-bound-family-of-elements-sup-Suplattice :
    {I : UU l3} (x : I → type-Suplattice) →
    is-upper-bound-family-of-elements-Poset
      ( poset-Suplattice)
      ( x)
      ( sup-Suplattice x)
  is-upper-bound-family-of-elements-sup-Suplattice x =
    backward-implication
      ( is-least-upper-bound-sup-Suplattice x (sup-Suplattice x))
      ( refl-leq-Suplattice (sup-Suplattice x))
```

## External links

- [suplattice](https://ncatlab.org/nlab/show/suplattice) at $n$Lab
