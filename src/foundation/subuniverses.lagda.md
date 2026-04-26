# Subuniverses

```agda
module foundation.subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.equality-dependent-function-types
open import foundation.equivalences
open import foundation.fundamental-theorem-of-identity-types
open import foundation.subtype-identity-principle
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.embeddings
open import foundation-core.fibers-of-maps
open import foundation-core.functoriality-dependent-pair-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
```

</details>

## Idea

**Subuniverses** are [subtypes](foundation-core.subtypes.md) of the universe.

## Definitions

### Subuniverses

```agda
is-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) → UU (lsuc l1 ⊔ l2)
is-subuniverse P = is-subtype P

subuniverse :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
subuniverse l1 l2 = subtype l2 (UU l1)

is-subtype-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  is-prop (is-in-subtype P X)
is-subtype-subuniverse P X = is-prop-is-in-subtype P X

module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  where

  type-subuniverse : UU (lsuc l1 ⊔ l2)
  type-subuniverse = type-subtype P

  is-in-subuniverse : UU l1 → UU l2
  is-in-subuniverse = is-in-subtype P

  is-prop-is-in-subuniverse : (X : UU l1) → is-prop (is-in-subuniverse X)
  is-prop-is-in-subuniverse = is-prop-is-in-subtype P

  inclusion-subuniverse : type-subuniverse → UU l1
  inclusion-subuniverse = inclusion-subtype P

  is-in-subuniverse-inclusion-subuniverse :
    (X : type-subuniverse) → is-in-subuniverse (inclusion-subuniverse X)
  is-in-subuniverse-inclusion-subuniverse = pr2

  is-emb-inclusion-subuniverse : is-emb inclusion-subuniverse
  is-emb-inclusion-subuniverse = is-emb-inclusion-subtype P

  emb-inclusion-subuniverse : type-subuniverse ↪ UU l1
  emb-inclusion-subuniverse = emb-subtype P
```

### The predicate of essentially being in a subuniverse

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  where

  is-essentially-in-subuniverse :
    {l3 : Level} (X : UU l3) → UU (lsuc l1 ⊔ l2 ⊔ l3)
  is-essentially-in-subuniverse X =
    Σ (type-subuniverse P) (λ Y → inclusion-subuniverse P Y ≃ X)

  is-proof-irrelevant-is-essentially-in-subuniverse :
    {l3 : Level} (X : UU l3) →
    is-proof-irrelevant (is-essentially-in-subuniverse X)
  is-proof-irrelevant-is-essentially-in-subuniverse X ((X' , p) , e) =
    is-torsorial-Eq-subtype
      ( is-contr-equiv'
        ( Σ (UU _) (λ T → T ≃ X'))
        ( equiv-tot (equiv-postcomp-equiv e))
        ( is-torsorial-equiv' X'))
      ( is-prop-is-in-subuniverse P)
      ( X')
      ( e)
      ( p)

  is-prop-is-essentially-in-subuniverse :
    {l3 : Level} (X : UU l3) → is-prop (is-essentially-in-subuniverse X)
  is-prop-is-essentially-in-subuniverse X =
    is-prop-is-proof-irrelevant
      ( is-proof-irrelevant-is-essentially-in-subuniverse X)

  is-essentially-in-subuniverse-Prop :
    {l3 : Level} (X : UU l3) → Prop (lsuc l1 ⊔ l2 ⊔ l3)
  pr1 (is-essentially-in-subuniverse-Prop X) =
    is-essentially-in-subuniverse X
  pr2 (is-essentially-in-subuniverse-Prop X) =
    is-prop-is-essentially-in-subuniverse X
```

- See also [univalent type families](foundation.univalent-type-families.md).

## Properties

### Subuniverses are closed under equivalences

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2) {X Y : UU l1}
  where

  is-in-subuniverse-equiv :
    X ≃ Y → is-in-subuniverse P X → is-in-subuniverse P Y
  is-in-subuniverse-equiv e = tr (is-in-subuniverse P) (eq-equiv e)

  is-in-subuniverse-equiv' :
    X ≃ Y → is-in-subuniverse P Y → is-in-subuniverse P X
  is-in-subuniverse-equiv' e = tr (is-in-subuniverse P) (inv (eq-equiv e))
```

### Characterization of the identity type of subuniverses

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  where

  equiv-subuniverse : (X Y : type-subuniverse P) → UU l1
  equiv-subuniverse X Y = (pr1 X) ≃ (pr1 Y)

  equiv-eq-subuniverse :
    (X Y : type-subuniverse P) → X ＝ Y → equiv-subuniverse X Y
  equiv-eq-subuniverse X .X refl = id-equiv

  abstract
    is-torsorial-equiv-subuniverse :
      (X : type-subuniverse P) →
      is-torsorial (λ Y → equiv-subuniverse X Y)
    is-torsorial-equiv-subuniverse (X , p) =
      is-torsorial-Eq-subtype
        ( is-torsorial-equiv X)
        ( is-subtype-subuniverse P)
        ( X)
        ( id-equiv)
        ( p)

    is-torsorial-equiv-subuniverse' :
      (X : type-subuniverse P) →
      is-torsorial (λ Y → equiv-subuniverse Y X)
    is-torsorial-equiv-subuniverse' (X , p) =
      is-torsorial-Eq-subtype
        ( is-torsorial-equiv' X)
        ( is-subtype-subuniverse P)
        ( X)
        ( id-equiv)
        ( p)

  abstract
    is-equiv-equiv-eq-subuniverse :
      (X Y : type-subuniverse P) → is-equiv (equiv-eq-subuniverse X Y)
    is-equiv-equiv-eq-subuniverse X =
      fundamental-theorem-id
        ( is-torsorial-equiv-subuniverse X)
        ( equiv-eq-subuniverse X)

  extensionality-subuniverse :
    (X Y : type-subuniverse P) → (X ＝ Y) ≃ equiv-subuniverse X Y
  pr1 (extensionality-subuniverse X Y) = equiv-eq-subuniverse X Y
  pr2 (extensionality-subuniverse X Y) = is-equiv-equiv-eq-subuniverse X Y

  eq-equiv-subuniverse :
    {X Y : type-subuniverse P} → equiv-subuniverse X Y → X ＝ Y
  eq-equiv-subuniverse {X} {Y} =
    map-inv-is-equiv (is-equiv-equiv-eq-subuniverse X Y)

  compute-eq-equiv-id-equiv-subuniverse :
    {X : type-subuniverse P} →
    eq-equiv-subuniverse {X} {X} (id-equiv {A = pr1 X}) ＝ refl
  compute-eq-equiv-id-equiv-subuniverse =
    is-retraction-map-inv-equiv (extensionality-subuniverse _ _) refl
```

### Equivalences of families of types in a subuniverse

```agda
fam-subuniverse :
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) (X : UU l3) →
  UU (lsuc l1 ⊔ l2 ⊔ l3)
fam-subuniverse P X = X → type-subuniverse P

module _
  {l1 l2 l3 : Level} (P : subuniverse l1 l2) {X : UU l3}
  where

  equiv-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → UU (l1 ⊔ l3)
  equiv-fam-subuniverse Y Z = (x : X) → equiv-subuniverse P (Y x) (Z x)

  id-equiv-fam-subuniverse :
    (Y : fam-subuniverse P X) → equiv-fam-subuniverse Y Y
  id-equiv-fam-subuniverse Y x = id-equiv

  is-torsorial-equiv-fam-subuniverse :
    (Y : fam-subuniverse P X) →
    is-torsorial (equiv-fam-subuniverse Y)
  is-torsorial-equiv-fam-subuniverse Y =
    is-torsorial-Eq-Π (λ x → is-torsorial-equiv-subuniverse P (Y x))

  equiv-eq-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → Y ＝ Z → equiv-fam-subuniverse Y Z
  equiv-eq-fam-subuniverse Y .Y refl = id-equiv-fam-subuniverse Y

  is-equiv-equiv-eq-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → is-equiv (equiv-eq-fam-subuniverse Y Z)
  is-equiv-equiv-eq-fam-subuniverse Y =
    fundamental-theorem-id
      ( is-torsorial-equiv-fam-subuniverse Y)
      ( equiv-eq-fam-subuniverse Y)

  extensionality-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → (Y ＝ Z) ≃ equiv-fam-subuniverse Y Z
  pr1 (extensionality-fam-subuniverse Y Z) = equiv-eq-fam-subuniverse Y Z
  pr2 (extensionality-fam-subuniverse Y Z) =
    is-equiv-equiv-eq-fam-subuniverse Y Z

  eq-equiv-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → equiv-fam-subuniverse Y Z → (Y ＝ Z)
  eq-equiv-fam-subuniverse Y Z =
    map-inv-is-equiv (is-equiv-equiv-eq-fam-subuniverse Y Z)
```

## See also

- [Σ-closed subuniverses](foundation.sigma-closed-subuniverses.md)
