# ω-Complete posets

```agda
module domain-theory.omega-complete-posets where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.decidable-total-order-natural-numbers
open import elementary-number-theory.inequality-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.binary-relations
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.function-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.least-upper-bounds-posets
open import order-theory.order-preserving-maps-posets
open import order-theory.posets
open import order-theory.upper-bounds-posets
```

</details>

## Idea

An
{{#concept "ω-complete poset" WD="complete partial order" WDID=Q3082805  Agda=ω-Complete-Poset}}
is a [poset](order-theory.posets.md) `P` such that every ascending
[chain](order-theory.chains-posets.md)

```text
  α₀ ≤ α₁ ≤ α₂ ≤ ⋯
```

in `P` has a [supremum](order-theory.least-upper-bounds--posets.md) in `P`.

## Definitions

### The predicate on posets of being an ω-complete poset

```agda
module _
  {l1 l2 : Level} (P : Poset l1 l2)
  where

  is-ω-complete-Poset-Prop : Prop (l1 ⊔ l2)
  is-ω-complete-Poset-Prop =
    Π-Prop
      ( hom-Poset ℕ-Poset P)
      ( λ F →
        has-least-upper-bound-family-of-elements-prop-Poset P
          ( map-hom-Poset ℕ-Poset P F))

  is-ω-complete-Poset : UU (l1 ⊔ l2)
  is-ω-complete-Poset =
    type-Prop is-ω-complete-Poset-Prop

  is-prop-is-ω-complete-Poset : is-prop is-ω-complete-Poset
  is-prop-is-ω-complete-Poset =
    is-prop-type-Prop is-ω-complete-Poset-Prop

module _
  {l1 l2 : Level} (P : Poset l1 l2) (H : is-ω-complete-Poset P)
  where

  sup-is-ω-complete-Poset : hom-Poset ℕ-Poset P → type-Poset P
  sup-is-ω-complete-Poset F = pr1 (H F)

  is-least-upper-bound-sup-is-ω-complete-Poset :
    (x : hom-Poset ℕ-Poset P) →
    is-least-upper-bound-family-of-elements-Poset P
      ( map-hom-Poset ℕ-Poset P x)
      ( sup-is-ω-complete-Poset x)
  is-least-upper-bound-sup-is-ω-complete-Poset F = pr2 (H F)
```

### ω-Complete posets

```agda
ω-Complete-Poset :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
ω-Complete-Poset l1 l2 =
  Σ (Poset l1 l2) (is-ω-complete-Poset)

module _
  {l1 l2 : Level} (A : ω-Complete-Poset l1 l2)
  where

  poset-ω-Complete-Poset : Poset l1 l2
  poset-ω-Complete-Poset = pr1 A

  type-ω-Complete-Poset : UU l1
  type-ω-Complete-Poset =
    type-Poset poset-ω-Complete-Poset

  leq-prop-ω-Complete-Poset :
    (x y : type-ω-Complete-Poset) → Prop l2
  leq-prop-ω-Complete-Poset =
    leq-prop-Poset poset-ω-Complete-Poset

  leq-ω-Complete-Poset :
    (x y : type-ω-Complete-Poset) → UU l2
  leq-ω-Complete-Poset =
    leq-Poset poset-ω-Complete-Poset

  is-prop-leq-ω-Complete-Poset :
    (x y : type-ω-Complete-Poset) →
    is-prop (leq-ω-Complete-Poset x y)
  is-prop-leq-ω-Complete-Poset =
    is-prop-leq-Poset poset-ω-Complete-Poset

  refl-leq-ω-Complete-Poset :
    (x : type-ω-Complete-Poset) →
    leq-ω-Complete-Poset x x
  refl-leq-ω-Complete-Poset =
    refl-leq-Poset poset-ω-Complete-Poset

  antisymmetric-leq-ω-Complete-Poset :
    is-antisymmetric leq-ω-Complete-Poset
  antisymmetric-leq-ω-Complete-Poset =
    antisymmetric-leq-Poset poset-ω-Complete-Poset

  transitive-leq-ω-Complete-Poset :
    is-transitive leq-ω-Complete-Poset
  transitive-leq-ω-Complete-Poset =
    transitive-leq-Poset poset-ω-Complete-Poset

  is-set-type-ω-Complete-Poset :
    is-set type-ω-Complete-Poset
  is-set-type-ω-Complete-Poset =
    is-set-type-Poset poset-ω-Complete-Poset

  set-ω-Complete-Poset : Set l1
  set-ω-Complete-Poset =
    set-Poset poset-ω-Complete-Poset

  is-ω-complete-ω-Complete-Poset :
    is-ω-complete-Poset poset-ω-Complete-Poset
  is-ω-complete-ω-Complete-Poset = pr2 A

  sup-ω-Complete-Poset :
    hom-Poset ℕ-Poset poset-ω-Complete-Poset →
    type-ω-Complete-Poset
  sup-ω-Complete-Poset =
    sup-is-ω-complete-Poset
      ( poset-ω-Complete-Poset)
      ( is-ω-complete-ω-Complete-Poset)

  is-least-upper-bound-sup-ω-Complete-Poset :
    (x : hom-Poset ℕ-Poset poset-ω-Complete-Poset) →
    is-least-upper-bound-family-of-elements-Poset
      ( poset-ω-Complete-Poset)
      ( map-hom-Poset ℕ-Poset poset-ω-Complete-Poset x)
      ( sup-ω-Complete-Poset x)
  is-least-upper-bound-sup-ω-Complete-Poset =
    is-least-upper-bound-sup-is-ω-complete-Poset
      ( poset-ω-Complete-Poset)
      ( is-ω-complete-ω-Complete-Poset)

  is-upper-bound-sup-ω-Complete-Poset :
    (x : hom-Poset ℕ-Poset poset-ω-Complete-Poset) →
    is-upper-bound-family-of-elements-Poset
      ( poset-ω-Complete-Poset)
      ( map-hom-Poset ℕ-Poset poset-ω-Complete-Poset x)
      ( sup-ω-Complete-Poset x)
  is-upper-bound-sup-ω-Complete-Poset x =
    is-upper-bound-is-least-upper-bound-family-of-elements-Poset
      ( poset-ω-Complete-Poset)
      ( is-least-upper-bound-sup-ω-Complete-Poset x)

  leq-sup-ω-Complete-Poset :
    (x : hom-Poset ℕ-Poset poset-ω-Complete-Poset)
    (i : ℕ) →
    leq-ω-Complete-Poset
      ( map-hom-Poset ℕ-Poset poset-ω-Complete-Poset x i)
      ( sup-ω-Complete-Poset x)
  leq-sup-ω-Complete-Poset x =
    backward-implication
      ( is-least-upper-bound-sup-ω-Complete-Poset
        ( x)
        ( sup-ω-Complete-Poset x))
      ( refl-leq-ω-Complete-Poset (sup-ω-Complete-Poset x))
```
