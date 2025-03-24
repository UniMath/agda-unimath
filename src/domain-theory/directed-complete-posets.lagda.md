# Directed complete posets

```agda
open import foundation.truncations-exist
open import foundation-core.univalence
open import foundation.function-extensionality-axiom

module domain-theory.directed-complete-posets
  (funext : function-extensionality)
  (univalence : univalence-axiom)
  (truncations : truncations-exist)
  where
```

<details><summary>Imports</summary>

```agda
open import domain-theory.directed-families-posets funext univalence truncations

open import foundation.binary-relations funext univalence truncations
open import foundation.dependent-pair-types
open import foundation.dependent-products-propositions funext
open import foundation.equivalences funext
open import foundation.function-types funext
open import foundation.logical-equivalences funext
open import foundation.propositions funext univalence
open import foundation.sets funext univalence
open import foundation.universe-levels

open import order-theory.least-upper-bounds-posets funext univalence truncations
open import order-theory.posets funext univalence truncations
```

</details>

## Idea

A
{{#concept "directed complete poset" WD="complete partial order" WDID=Q3082805 Agda=Directed-Complete-Poset}}
is a [poset](order-theory.posets.md) such that all
[directed families](domain-theory.directed-families-posets.md) have
[least upper bounds](order-theory.least-upper-bounds-posets.md).

## Definitions

### The predicate on posets of being directed complete

```agda
module _
  {l1 l2 : Level} (l3 : Level) (P : Poset l1 l2)
  where

  is-directed-complete-prop-Poset : Prop (l1 ⊔ l2 ⊔ lsuc l3)
  is-directed-complete-prop-Poset =
    Π-Prop
      ( directed-family-Poset l3 P)
      ( λ F →
        has-least-upper-bound-family-of-elements-prop-Poset P
          ( family-directed-family-Poset P F))

  is-directed-complete-Poset : UU (l1 ⊔ l2 ⊔ lsuc l3)
  is-directed-complete-Poset =
    type-Prop is-directed-complete-prop-Poset

  is-prop-is-directed-complete-Poset : is-prop is-directed-complete-Poset
  is-prop-is-directed-complete-Poset =
    is-prop-type-Prop is-directed-complete-prop-Poset

module _
  {l1 l2 l3 : Level} (P : Poset l1 l2) (H : is-directed-complete-Poset l3 P)
  where

  sup-is-directed-complete-Poset : directed-family-Poset l3 P → type-Poset P
  sup-is-directed-complete-Poset F = pr1 (H F)

  is-least-upper-bound-sup-is-directed-complete-Poset :
    (x : directed-family-Poset l3 P) →
    is-least-upper-bound-family-of-elements-Poset P
      ( family-directed-family-Poset P x)
      ( sup-is-directed-complete-Poset x)
  is-least-upper-bound-sup-is-directed-complete-Poset F = pr2 (H F)
```

### Directed complete posets

```agda
Directed-Complete-Poset :
  (l1 l2 l3 : Level) → UU (lsuc l1 ⊔ lsuc l2 ⊔ lsuc l3)
Directed-Complete-Poset l1 l2 l3 =
  Σ (Poset l1 l2) (is-directed-complete-Poset l3)

module _
  {l1 l2 l3 : Level} (A : Directed-Complete-Poset l1 l2 l3)
  where

  poset-Directed-Complete-Poset : Poset l1 l2
  poset-Directed-Complete-Poset = pr1 A

  type-Directed-Complete-Poset : UU l1
  type-Directed-Complete-Poset =
    type-Poset poset-Directed-Complete-Poset

  leq-prop-Directed-Complete-Poset :
    (x y : type-Directed-Complete-Poset) → Prop l2
  leq-prop-Directed-Complete-Poset =
    leq-prop-Poset poset-Directed-Complete-Poset

  leq-Directed-Complete-Poset :
    (x y : type-Directed-Complete-Poset) → UU l2
  leq-Directed-Complete-Poset =
    leq-Poset poset-Directed-Complete-Poset

  is-prop-leq-Directed-Complete-Poset :
    (x y : type-Directed-Complete-Poset) →
    is-prop (leq-Directed-Complete-Poset x y)
  is-prop-leq-Directed-Complete-Poset =
    is-prop-leq-Poset poset-Directed-Complete-Poset

  refl-leq-Directed-Complete-Poset :
    (x : type-Directed-Complete-Poset) →
    leq-Directed-Complete-Poset x x
  refl-leq-Directed-Complete-Poset =
    refl-leq-Poset poset-Directed-Complete-Poset

  antisymmetric-leq-Directed-Complete-Poset :
    is-antisymmetric leq-Directed-Complete-Poset
  antisymmetric-leq-Directed-Complete-Poset =
    antisymmetric-leq-Poset poset-Directed-Complete-Poset

  transitive-leq-Directed-Complete-Poset :
    is-transitive leq-Directed-Complete-Poset
  transitive-leq-Directed-Complete-Poset =
    transitive-leq-Poset poset-Directed-Complete-Poset

  is-set-type-Directed-Complete-Poset :
    is-set type-Directed-Complete-Poset
  is-set-type-Directed-Complete-Poset =
    is-set-type-Poset poset-Directed-Complete-Poset

  set-Directed-Complete-Poset : Set l1
  set-Directed-Complete-Poset =
    set-Poset poset-Directed-Complete-Poset

  is-directed-complete-Directed-Complete-Poset :
    is-directed-complete-Poset l3 poset-Directed-Complete-Poset
  is-directed-complete-Directed-Complete-Poset = pr2 A

  sup-Directed-Complete-Poset :
    directed-family-Poset l3 poset-Directed-Complete-Poset →
    type-Directed-Complete-Poset
  sup-Directed-Complete-Poset =
    sup-is-directed-complete-Poset
      ( poset-Directed-Complete-Poset)
      ( is-directed-complete-Directed-Complete-Poset)

  is-least-upper-bound-sup-Directed-Complete-Poset :
    (x : directed-family-Poset l3 poset-Directed-Complete-Poset) →
    is-least-upper-bound-family-of-elements-Poset
      ( poset-Directed-Complete-Poset)
      ( family-directed-family-Poset poset-Directed-Complete-Poset x)
      ( sup-Directed-Complete-Poset x)
  is-least-upper-bound-sup-Directed-Complete-Poset =
    is-least-upper-bound-sup-is-directed-complete-Poset
      ( poset-Directed-Complete-Poset)
      ( is-directed-complete-Directed-Complete-Poset)

  is-upper-bound-sup-Directed-Complete-Poset :
    (x : directed-family-Poset l3 poset-Directed-Complete-Poset)
    (i : type-directed-family-Poset poset-Directed-Complete-Poset x) →
    leq-Directed-Complete-Poset
      ( family-directed-family-Poset poset-Directed-Complete-Poset x i)
      ( sup-Directed-Complete-Poset x)
  is-upper-bound-sup-Directed-Complete-Poset x =
    backward-implication
      ( is-least-upper-bound-sup-Directed-Complete-Poset
        ( x)
        ( sup-Directed-Complete-Poset x))
      ( refl-leq-Directed-Complete-Poset (sup-Directed-Complete-Poset x))
```

## External links

- [dcpo](https://ncatlab.org/nlab/show/dcpo) at $n$Lab
