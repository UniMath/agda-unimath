# Global subuniverses

```agda
module foundation.global-subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.iterated-dependent-product-types
open import foundation.subuniverses
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.fibers-of-maps
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

**Global subuniverses** are [subtypes](foundation-core.subtypes.md) of the large
universe that are defined at every level, and are closed under
[equivalences of types](foundation-core.equivalences.md). This does not follow
from [univalence](foundation.univalence.md), as equivalence induction only holds
for homogeneous equivalences, i.e. equivalences in a single universe.

## Definitions

### The predicate on families of subuniverses of being closed under equivalences

```agda
module _
  (α : Level → Level) (P : (l : Level) → subuniverse l (α l))
  (l1 l2 : Level)
  where

  is-closed-under-equiv-subuniverses : UU (α l1 ⊔ α l2 ⊔ lsuc l1 ⊔ lsuc l2)
  is-closed-under-equiv-subuniverses =
    (X : UU l1) (Y : UU l2) → X ≃ Y → type-Prop (P l1 X) → type-Prop (P l2 Y)

  is-prop-is-closed-under-equiv-subuniverses :
    is-prop is-closed-under-equiv-subuniverses
  is-prop-is-closed-under-equiv-subuniverses =
    is-prop-iterated-Π 4 (λ X Y e x → is-prop-type-Prop (P l2 Y))

  is-closed-under-equiv-subuniverses-Prop :
    Prop (α l1 ⊔ α l2 ⊔ lsuc l1 ⊔ lsuc l2)
  pr1 is-closed-under-equiv-subuniverses-Prop =
    is-closed-under-equiv-subuniverses
  pr2 is-closed-under-equiv-subuniverses-Prop =
    is-prop-is-closed-under-equiv-subuniverses
```

### The global type of global subuniverses

```agda
record global-subuniverse (α : Level → Level) : UUω where
  field
    subuniverse-global-subuniverse :
      (l : Level) → subuniverse l (α l)

    is-closed-under-equiv-global-subuniverse :
      {l1 l2 : Level} →
      is-closed-under-equiv-subuniverses α subuniverse-global-subuniverse l1 l2

  is-in-global-subuniverse-Prop : {l : Level} → UU l → Prop (α l)
  is-in-global-subuniverse-Prop {l} X =
    subuniverse-global-subuniverse l X

  is-in-global-subuniverse : {l : Level} → UU l → UU (α l)
  is-in-global-subuniverse {l} X =
    is-in-subuniverse (subuniverse-global-subuniverse l) X

  is-prop-is-in-global-subuniverse :
    {l : Level} (X : UU l) → is-prop (is-in-global-subuniverse X)
  is-prop-is-in-global-subuniverse {l} X =
    is-prop-type-Prop (subuniverse-global-subuniverse l X)

  type-global-subuniverse : (l : Level) → UU (α l ⊔ lsuc l)
  type-global-subuniverse l =
    type-subuniverse (subuniverse-global-subuniverse l)

  inclusion-global-subuniverse :
    {l : Level} → type-global-subuniverse l → UU l
  inclusion-global-subuniverse {l} =
    inclusion-subuniverse (subuniverse-global-subuniverse l)

  is-in-global-subuniverse-inclusion-global-subuniverse :
    {l : Level} (X : type-global-subuniverse l) →
    is-in-global-subuniverse (inclusion-global-subuniverse X)
  is-in-global-subuniverse-inclusion-global-subuniverse {l} =
    is-in-subuniverse-inclusion-subuniverse (subuniverse-global-subuniverse l)

open global-subuniverse public
```

### The predicate of essentially being in a subuniverse

We say a type is _essentially in_ a global universe at universe level `l` if it
is essentially in the subuniverse at level `l`.

```agda
module _
  {α : Level → Level} (P : global-subuniverse α)
  {l1 : Level} (l2 : Level) (X : UU l1)
  where

  is-essentially-in-global-subuniverse : UU (α l2 ⊔ l1 ⊔ lsuc l2)
  is-essentially-in-global-subuniverse =
    is-essentially-in-subuniverse (subuniverse-global-subuniverse P l2) X

  is-prop-is-essentially-in-global-subuniverse :
    is-prop is-essentially-in-global-subuniverse
  is-prop-is-essentially-in-global-subuniverse =
    is-prop-is-essentially-in-subuniverse
      ( subuniverse-global-subuniverse P l2) X

  is-essentially-in-global-subuniverse-Prop : Prop (α l2 ⊔ l1 ⊔ lsuc l2)
  is-essentially-in-global-subuniverse-Prop =
    is-essentially-in-subuniverse-Prop (subuniverse-global-subuniverse P l2) X
```

## Properties

### Global subuniverses are closed under equivalences between types in a single universe

This is true for any family of subuniverses indexed by universe levels.

```agda
module _
  {α : Level → Level} (P : global-subuniverse α)
  {l : Level} {X Y : UU l}
  where

  is-in-global-subuniverse-equiv-Level :
    X ≃ Y → is-in-global-subuniverse P X → is-in-global-subuniverse P Y
  is-in-global-subuniverse-equiv-Level =
    is-in-subuniverse-equiv (subuniverse-global-subuniverse P l)

  is-in-global-subuniverse-equiv-Level' :
    X ≃ Y → is-in-global-subuniverse P Y → is-in-global-subuniverse P X
  is-in-global-subuniverse-equiv-Level' =
    is-in-subuniverse-equiv' (subuniverse-global-subuniverse P l)
```

### Characterization of the identity type of global subuniverses at a universe level

```agda
module _
  {α : Level → Level} {l : Level} (P : global-subuniverse α)
  where

  equiv-global-subuniverse-Level : (X Y : type-global-subuniverse P l) → UU l
  equiv-global-subuniverse-Level =
    equiv-subuniverse (subuniverse-global-subuniverse P l)

  equiv-eq-global-subuniverse-Level :
    (X Y : type-global-subuniverse P l) →
    X ＝ Y → equiv-global-subuniverse-Level X Y
  equiv-eq-global-subuniverse-Level =
    equiv-eq-subuniverse (subuniverse-global-subuniverse P l)

  abstract
    is-equiv-equiv-eq-global-subuniverse-Level :
      (X Y : type-global-subuniverse P l) →
      is-equiv (equiv-eq-global-subuniverse-Level X Y)
    is-equiv-equiv-eq-global-subuniverse-Level =
      is-equiv-equiv-eq-subuniverse (subuniverse-global-subuniverse P l)

  extensionality-global-subuniverse-Level :
    (X Y : type-global-subuniverse P l) →
    (X ＝ Y) ≃ equiv-global-subuniverse-Level X Y
  extensionality-global-subuniverse-Level =
    extensionality-subuniverse (subuniverse-global-subuniverse P l)

  eq-equiv-global-subuniverse-Level :
    {X Y : type-global-subuniverse P l} →
    equiv-global-subuniverse-Level X Y → X ＝ Y
  eq-equiv-global-subuniverse-Level =
    eq-equiv-subuniverse (subuniverse-global-subuniverse P l)

  compute-eq-equiv-id-equiv-global-subuniverse-Level :
    {X : type-global-subuniverse P l} →
    eq-equiv-global-subuniverse-Level {X} {X} (id-equiv {A = pr1 X}) ＝ refl
  compute-eq-equiv-id-equiv-global-subuniverse-Level =
    compute-eq-equiv-id-equiv-subuniverse (subuniverse-global-subuniverse P l)
```

### Equivalences of families of types in a global subuniverse

```agda
fam-global-subuniverse :
  {α : Level → Level} (P : global-subuniverse α)
  {l1 : Level} (l2 : Level) (X : UU l1) → UU (α l2 ⊔ l1 ⊔ lsuc l2)
fam-global-subuniverse P l2 X = X → type-global-subuniverse P l2

module _
  {α : Level → Level} (P : global-subuniverse α)
  {l1 : Level} (l2 : Level) {X : UU l1}
  (Y Z : fam-global-subuniverse P l2 X)
  where

  equiv-fam-global-subuniverse : UU (l1 ⊔ l2)
  equiv-fam-global-subuniverse =
    equiv-fam-subuniverse (subuniverse-global-subuniverse P l2) Y Z

  equiv-eq-fam-global-subuniverse :
    Y ＝ Z → equiv-fam-global-subuniverse
  equiv-eq-fam-global-subuniverse =
    equiv-eq-fam-subuniverse (subuniverse-global-subuniverse P l2) Y Z

  is-equiv-equiv-eq-fam-global-subuniverse :
    is-equiv equiv-eq-fam-global-subuniverse
  is-equiv-equiv-eq-fam-global-subuniverse =
    is-equiv-equiv-eq-fam-subuniverse (subuniverse-global-subuniverse P l2) Y Z

  extensionality-fam-global-subuniverse :
    (Y ＝ Z) ≃ equiv-fam-global-subuniverse
  extensionality-fam-global-subuniverse =
    extensionality-fam-subuniverse (subuniverse-global-subuniverse P l2) Y Z

  eq-equiv-fam-global-subuniverse : equiv-fam-global-subuniverse → Y ＝ Z
  eq-equiv-fam-global-subuniverse =
    map-inv-is-equiv is-equiv-equiv-eq-fam-global-subuniverse
```

## See also

- [Large categories](category-theory.large-categories.md)
- [Cumulative large sets](foundation.cumulative-large-sets.md)
