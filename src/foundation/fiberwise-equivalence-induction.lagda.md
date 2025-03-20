# Fiberwise equivalence induction

```agda
module foundation.fiberwise-equivalence-induction where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.families-of-equivalences
open import foundation.identity-systems
open import foundation.identity-types
-- open import foundation.subuniverses
-- open import foundation.univalence
-- open import foundation.universal-property-identity-systems
open import foundation.universe-levels

-- open import foundation-core.commuting-triangles-of-maps
-- open import foundation-core.contractible-maps
-- open import foundation-core.function-types
-- open import foundation-core.postcomposition-functions
-- open import foundation-core.sections
-- open import foundation-core.torsorial-type-families
```

</details>

## Idea

## Definitions

### Evaluation at the family of identity equivalences

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {P : A → UU l2}
  (R : (Q : A → UU l2) → fam-equiv P Q → UU l3)
  where

  ev-id-fam-equiv :
    ((Q : A → UU l2) → (e : fam-equiv P Q) → R Q e) →
    R P id-fam-equiv
  ev-id-fam-equiv r = r P id-fam-equiv
```

### The induction principle of families of equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} (P : A → UU l2)
  where

  induction-principle-fam-equiv : UUω
  induction-principle-fam-equiv =
    is-identity-system (λ (Q : A → UU l2) → fam-equiv P Q) P id-fam-equiv

  induction-principle-fam-equiv' : UUω
  induction-principle-fam-equiv' =
    is-identity-system (λ (Q : A → UU l2) → fam-equiv Q P) P id-fam-equiv
```

## Theorems

### Induction on families of equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} {P : A → UU l2}
  where

  abstract
    is-identity-system-fam-equiv : induction-principle-fam-equiv P
    is-identity-system-fam-equiv =
      is-identity-system-is-torsorial P
        ( id-fam-equiv)
        ( is-torsorial-fam-equiv)

    is-identity-system-fam-equiv' : induction-principle-fam-equiv' P
    is-identity-system-fam-equiv' =
      is-identity-system-is-torsorial P
        ( id-fam-equiv)
        ( is-torsorial-fam-equiv')

module _
  {l1 l2 l3 : Level} {A : UU l1} {P : A → UU l2}
  (R : (Q : A → UU l2) → fam-equiv P Q → UU l3)
  (r : R P id-fam-equiv)
  where

  abstract
    ind-fam-equiv :
      {Q : A → UU l2} (e : fam-equiv P Q) → R Q e
    ind-fam-equiv {Q = Q} e =
      pr1 (is-identity-system-fam-equiv R) r Q e

    compute-ind-fam-equiv :
      ind-fam-equiv id-fam-equiv ＝ r
    compute-ind-fam-equiv =
      pr2 (is-identity-system-fam-equiv R) r

module _
  {l1 l2 l3 : Level} {A : UU l1} {P : A → UU l2}
  (R : (Q : A → UU l2) → fam-equiv Q P → UU l3)
  (r : R P id-fam-equiv)
  where

  abstract
    ind-fam-equiv' :
      {Q : A → UU l2} (e : fam-equiv Q P) → R Q e
    ind-fam-equiv' {Q = Q} e =
      pr1 (is-identity-system-fam-equiv' R) r Q e

    compute-ind-fam-equiv' :
      ind-fam-equiv' id-fam-equiv ＝ r
    compute-ind-fam-equiv' =
      pr2 (is-identity-system-fam-equiv' R) r
```
