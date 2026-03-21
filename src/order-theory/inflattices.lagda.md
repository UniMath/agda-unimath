# Inflattices

```agda
module order-theory.inflattices where
```

<details><summary>Imports</summary>

```agda
open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.greatest-lower-bounds-posets
open import order-theory.lower-bounds-posets
open import order-theory.posets
```

</details>

## Idea

Consider a [universe level](foundation.universe-levels.md) `l`. An
`l`-{{#concept "inflattice" Agda=Inflattice}} is a
[poset](order-theory.posets.md) which has all
[greatest lower bounds](order-theory.greatest-lower-bounds-posets.md) of
families of elements indexed by a type at universe level `l`.

## Definitions

### The predicate on posets of being an `l`-inflattice

```agda
module _
  {l1 l2 : Level} (l3 : Level) (P : Poset l1 l2)
  where

  is-inflattice-Poset-Prop : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-inflattice-Poset-Prop =
    Π-Prop
      (UU l3)
      ( λ I →
        Π-Prop
          ( I → type-Poset P)
          ( λ f → has-greatest-lower-bound-family-of-elements-prop-Poset P f))

  is-inflattice-Poset : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-inflattice-Poset = type-Prop is-inflattice-Poset-Prop

  is-prop-inflattice-Poset : is-prop is-inflattice-Poset
  is-prop-inflattice-Poset = is-prop-type-Prop is-inflattice-Poset-Prop

module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) (H : is-inflattice-Poset l3 P)
  where

  inf-is-inflattice-Poset :
    {I : UU l3} → (I → type-Poset P) → type-Poset P
  inf-is-inflattice-Poset {I} x = pr1 (H I x)

  is-greatest-lower-bound-inf-is-inflattice-Poset :
    {I : UU l3} (x : I → type-Poset P) →
    is-greatest-lower-bound-family-of-elements-Poset P x
      ( inf-is-inflattice-Poset x)
  is-greatest-lower-bound-inf-is-inflattice-Poset {I} x = pr2 (H I x)
```

### `l`-Inflattices

```agda
Inflattice : (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Inflattice l1 l2 l3 = Σ (Poset l1 l2) (λ P → is-inflattice-Poset l3 P)

module _
  {l1 l2 l3 : Level} (A : Inflattice l1 l2 l3)
  where

  poset-Inflattice : Poset l1 l2
  poset-Inflattice = pr1 A

  type-Inflattice : UU l1
  type-Inflattice = type-Poset poset-Inflattice

  leq-prop-Inflattice : (x y : type-Inflattice) → Prop l2
  leq-prop-Inflattice = leq-prop-Poset poset-Inflattice

  leq-Inflattice : (x y : type-Inflattice) → UU l2
  leq-Inflattice = leq-Poset poset-Inflattice

  is-prop-leq-Inflattice :
    (x y : type-Inflattice) → is-prop (leq-Inflattice x y)
  is-prop-leq-Inflattice = is-prop-leq-Poset poset-Inflattice

  refl-leq-Inflattice :
    (x : type-Inflattice) → leq-Inflattice x x
  refl-leq-Inflattice = refl-leq-Poset poset-Inflattice

  antisymmetric-leq-Inflattice : is-antisymmetric leq-Inflattice
  antisymmetric-leq-Inflattice =
    antisymmetric-leq-Poset poset-Inflattice

  transitive-leq-Inflattice : is-transitive leq-Inflattice
  transitive-leq-Inflattice = transitive-leq-Poset poset-Inflattice

  is-set-type-Inflattice : is-set type-Inflattice
  is-set-type-Inflattice = is-set-type-Poset poset-Inflattice

  set-Inflattice : Set l1
  set-Inflattice = set-Poset poset-Inflattice

  is-inflattice-Inflattice :
    is-inflattice-Poset l3 poset-Inflattice
  is-inflattice-Inflattice = pr2 A

  inf-Inflattice :
    {I : UU l3} → (I → type-Inflattice) → type-Inflattice
  inf-Inflattice =
    inf-is-inflattice-Poset
      ( poset-Inflattice)
      ( is-inflattice-Inflattice)

  is-greatest-lower-bound-inf-Inflattice :
    {I : UU l3} (x : I → type-Inflattice) →
    is-greatest-lower-bound-family-of-elements-Poset
      ( poset-Inflattice)
      ( x)
      ( inf-Inflattice x)
  is-greatest-lower-bound-inf-Inflattice =
    is-greatest-lower-bound-inf-is-inflattice-Poset
      ( poset-Inflattice)
      ( is-inflattice-Inflattice)

  is-lower-bound-family-of-elements-inf-Inflattice :
    {I : UU l3} (x : I → type-Inflattice) →
    is-lower-bound-family-of-elements-Poset
      ( poset-Inflattice)
      ( x)
      ( inf-Inflattice x)
  is-lower-bound-family-of-elements-inf-Inflattice x =
    backward-implication
      ( is-greatest-lower-bound-inf-Inflattice x (inf-Inflattice x))
      ( refl-leq-Inflattice (inf-Inflattice x))
```

## External links

- [inflattice](https://ncatlab.org/nlab/show/inflattice) at $n$Lab
