# Large suplattices

```agda
module order-theory.large-suplattices where
```

<detail><summary>Imports</summary>

```agda
open import foundation.identity-types
open import foundation.logical-equivalences
open import foundation.propositions
open import foundation.sets
open import foundation.universe-levels

open import order-theory.large-posets
```

</details>

## Idea

A **large suplattice** is a [large poset](order-theory.large-posets.md) `P` such
that for every family

```md
  x : I → type-Large-Poset P l1
```

indexed by `I : UU l2` there is an element `⋁ x : type-Large-Poset P (l1 ⊔ l2)`
such that the logical equivalence

```md
  (∀ᵢ xᵢ ≤ y) ↔ ((⋁ x) ≤ y)
```

holds for every element `y : type-Large-Poset P l3`.

## Definitions

### The predicate of being an upper bound of a family of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Poset P l2)
  where

  is-upper-bound-family-of-elements-Large-Poset-Prop :
    {l3 : Level} (y : type-Large-Poset P l3) → Prop (β l2 l3 ⊔ l1)
  is-upper-bound-family-of-elements-Large-Poset-Prop y =
    Π-Prop I (λ i → leq-Large-Poset-Prop P (x i) y)

  is-upper-bound-family-of-elements-Large-Poset :
    {l3 : Level} (y : type-Large-Poset P l3) → UU (β l2 l3 ⊔ l1)
  is-upper-bound-family-of-elements-Large-Poset y =
    type-Prop (is-upper-bound-family-of-elements-Large-Poset-Prop y)

  is-prop-is-upper-bound-family-of-elements-Large-Poset :
    {l3 : Level} (y : type-Large-Poset P l3) →
    is-prop (is-upper-bound-family-of-elements-Large-Poset y)
  is-prop-is-upper-bound-family-of-elements-Large-Poset y =
    is-prop-type-Prop (is-upper-bound-family-of-elements-Large-Poset-Prop y)
```

### The predicate on large-posets of being a least upper bound of a family of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 l3 : Level} {I : UU l1} (x : I → type-Large-Poset P l2)
  where

  is-least-upper-bound-family-of-elements-Large-Poset :
    type-Large-Poset P l3 → UUω
  is-least-upper-bound-family-of-elements-Large-Poset y =
    {l4 : Level} (z : type-Large-Poset P l4) →
    is-upper-bound-family-of-elements-Large-Poset P x y ↔ leq-Large-Poset P z y
```

### The predicate on large posets of having least upper bounds of families of elements

```agda
module _
  {α : Level → Level} {β : Level → Level → Level}
  (P : Large-Poset α β)
  {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Poset P l2)
  where

  record
    has-least-upper-bound-family-of-elements-Large-Poset : UUω
    where
    field
      sup-has-least-upper-bound-family-of-elements-Large-Poset :
        type-Large-Poset P (l1 ⊔ l2)
      is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Poset :
        is-least-upper-bound-family-of-elements-Large-Poset P x
          sup-has-least-upper-bound-family-of-elements-Large-Poset

  open has-least-upper-bound-family-of-elements-Large-Poset public
```

### Large suplattices

```agda
record
  Large-Suplattice (α : Level → Level) ( β : Level → Level → Level) : UUω
  where
  constructor
    make-Large-Suplattice
  field
    large-poset-Large-Suplattice : Large-Poset α β
    has-least-upper-bounds-Large-Suplattice :
      {l1 l2 : Level} {I : UU l1}
      (x : I → type-Large-Poset large-poset-Large-Suplattice l2) →
      has-least-upper-bound-family-of-elements-Large-Poset
        ( large-poset-Large-Suplattice)
        ( x)

open Large-Suplattice public

module _
  {α : Level → Level} {β : Level → Level → Level}
  (L : Large-Suplattice α β)
  where

  set-Large-Suplattice : (l : Level) → Set (α l)
  set-Large-Suplattice = set-Large-Poset (large-poset-Large-Suplattice L)

  type-Large-Suplattice : (l : Level) → UU (α l)
  type-Large-Suplattice = type-Large-Poset (large-poset-Large-Suplattice L)

  is-set-type-Large-Suplattice : {l : Level} → is-set (type-Large-Suplattice l)
  is-set-type-Large-Suplattice =
    is-set-type-Large-Poset (large-poset-Large-Suplattice L)

  leq-Large-Suplattice-Prop :
    {l1 l2 : Level}
    (x : type-Large-Suplattice l1) (y : type-Large-Suplattice l2) →
    Prop (β l1 l2)
  leq-Large-Suplattice-Prop =
    leq-Large-Poset-Prop (large-poset-Large-Suplattice L)

  leq-Large-Suplattice :
    {l1 l2 : Level}
    (x : type-Large-Suplattice l1) (y : type-Large-Suplattice l2) →
    UU (β l1 l2)
  leq-Large-Suplattice = leq-Large-Poset (large-poset-Large-Suplattice L)

  is-prop-leq-Large-Suplattice :
    {l1 l2 : Level}
    (x : type-Large-Suplattice l1) (y : type-Large-Suplattice l2) →
    is-prop (leq-Large-Suplattice x y)
  is-prop-leq-Large-Suplattice =
    is-prop-leq-Large-Poset (large-poset-Large-Suplattice L)

  refl-leq-Large-Suplattice :
    {l1 : Level} (x : type-Large-Suplattice l1) →
    leq-Large-Suplattice x x
  refl-leq-Large-Suplattice =
    refl-leq-Large-Poset (large-poset-Large-Suplattice L)

  antisymmetric-leq-Large-Suplattice :
    {l1 : Level}
    (x : type-Large-Suplattice l1) (y : type-Large-Suplattice l1) →
    leq-Large-Suplattice x y → leq-Large-Suplattice y x → x ＝ y
  antisymmetric-leq-Large-Suplattice =
    antisymmetric-leq-Large-Poset (large-poset-Large-Suplattice L)

  transitive-leq-Large-Suplattice :
    {l1 l2 l3 : Level}
    (x : type-Large-Suplattice l1)
    (y : type-Large-Suplattice l2)
    (z : type-Large-Suplattice l3) →
    leq-Large-Suplattice y z → leq-Large-Suplattice x y →
    leq-Large-Suplattice x z
  transitive-leq-Large-Suplattice =
    transitive-leq-Large-Poset (large-poset-Large-Suplattice L)

  sup-Large-Suplattice :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Suplattice l2) →
    type-Large-Suplattice (l1 ⊔ l2)
  sup-Large-Suplattice x =
    sup-has-least-upper-bound-family-of-elements-Large-Poset
      ( has-least-upper-bounds-Large-Suplattice L x)

  is-upper-bound-family-of-elements-Large-Suplattice :
    {l1 l2 l3 : Level} {I : UU l1} (x : I → type-Large-Suplattice l2)
    (y : type-Large-Suplattice l3) → UU (β l2 l3 ⊔ l1)
  is-upper-bound-family-of-elements-Large-Suplattice x y =
    is-upper-bound-family-of-elements-Large-Poset
      ( large-poset-Large-Suplattice L)
      ( x)
      ( y)

  is-least-upper-bound-family-of-elements-Large-Suplattice :
    {l1 l2 l3 : Level} {I : UU l1} (x : I → type-Large-Suplattice l2) →
    type-Large-Suplattice l3 → UUω
  is-least-upper-bound-family-of-elements-Large-Suplattice =
    is-least-upper-bound-family-of-elements-Large-Poset
      ( large-poset-Large-Suplattice L)

  is-least-upper-bound-sup-Large-Suplattice :
    {l1 l2 : Level} {I : UU l1} (x : I → type-Large-Suplattice l2) →
    is-least-upper-bound-family-of-elements-Large-Suplattice x
      ( sup-Large-Suplattice x)
  is-least-upper-bound-sup-Large-Suplattice x =
     is-least-upper-bound-sup-has-least-upper-bound-family-of-elements-Large-Poset
       ( has-least-upper-bounds-Large-Suplattice L x)
```
