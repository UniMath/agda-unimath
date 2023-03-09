# Subuniverse

```agda
module foundation.subuniverses where
```

<details><summary>Imports</summary>

```agda
open import foundation.embeddings
open import foundation.equality-dependent-function-types
open import foundation.univalence

open import foundation-core.contractible-types
open import foundation-core.dependent-pair-types
open import foundation-core.equivalences
open import foundation-core.fundamental-theorem-of-identity-types
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subtype-identity-principle
open import foundation-core.subtypes
open import foundation-core.universe-levels
```

</details>

## Idea

Subuniverses are subtypes of the universe.

## Definitions

### Subuniverses

```agda
is-subuniverse :
  {l1 l2 : Level} (P : UU l1 → UU l2) → UU ((lsuc l1) ⊔ l2)
is-subuniverse P = is-subtype P

subuniverse :
  (l1 l2 : Level) → UU (lsuc l1 ⊔ lsuc l2)
subuniverse l1 l2 = subtype l2 (UU l1)

is-subtype-subuniverse :
  {l1 l2 : Level} (P : subuniverse l1 l2) (X : UU l1) →
  is-prop (type-Prop (P X))
is-subtype-subuniverse P X = is-prop-type-Prop (P X)

module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  where

  type-subuniverse : UU ((lsuc l1) ⊔ l2)
  type-subuniverse = type-subtype P

  is-in-subuniverse : UU l1 → UU l2
  is-in-subuniverse = is-in-subtype P

  inclusion-subuniverse : type-subuniverse → UU l1
  inclusion-subuniverse = inclusion-subtype P

  is-emb-inclusion-subuniverse : is-emb inclusion-subuniverse
  is-emb-inclusion-subuniverse = is-emb-inclusion-subtype P

  emb-inclusion-subuniverse : type-subuniverse ↪ UU l1
  emb-inclusion-subuniverse = emb-subtype P
```

### Global subuniverses

```agda
is-global-subuniverse :
  (α : Level → Level) (P : (l : Level) → subuniverse l (α l)) →
  (l1 l2 : Level) → UU _
is-global-subuniverse α P l1 l2 =
  (X : UU l1) (Y : UU l2) → X ≃ Y → type-Prop (P l1 X) → type-Prop (P l2 Y)
```

## Properties

### Subuniverses are closed under equivalences

```agda
in-subuniverse-equiv :
  {l1 l2 : Level} (P : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → P X → P Y
in-subuniverse-equiv P e = tr P (eq-equiv _ _ e)

in-subuniverse-equiv' :
  {l1 l2 : Level} (P : UU l1 → UU l2) {X Y : UU l1} → X ≃ Y → P Y → P X
in-subuniverse-equiv' P e = tr P (inv (eq-equiv _ _ e))
```

### Characterization of the identity type of subuniverses

```agda
module _
  {l1 l2 : Level} (P : subuniverse l1 l2)
  where

  equiv-subuniverse : (X Y : type-subuniverse P) → UU l1
  equiv-subuniverse X Y = (pr1 X) ≃ (pr1 Y)

  equiv-eq-subuniverse :
    (s t : type-subuniverse P) → s ＝ t → equiv-subuniverse s t
  equiv-eq-subuniverse (pair X p) .(pair X p) refl = id-equiv

  abstract
    is-contr-total-equiv-subuniverse :
      (s : type-subuniverse P) →
      is-contr (Σ (type-subuniverse P) (λ t → equiv-subuniverse s t))
    is-contr-total-equiv-subuniverse (pair X p) =
      is-contr-total-Eq-subtype
        ( is-contr-total-equiv X)
        ( is-subtype-subuniverse P)
        ( X)
        ( id-equiv)
        ( p)

  abstract
    is-equiv-equiv-eq-subuniverse :
      (s t : type-subuniverse P) → is-equiv (equiv-eq-subuniverse s t)
    is-equiv-equiv-eq-subuniverse (pair X p) =
      fundamental-theorem-id
        ( is-contr-total-equiv-subuniverse (pair X p))
        ( equiv-eq-subuniverse (pair X p))

  extensionality-subuniverse :
    (s t : type-subuniverse P) → (s ＝ t) ≃ equiv-subuniverse s t
  pr1 (extensionality-subuniverse s t) = equiv-eq-subuniverse s t
  pr2 (extensionality-subuniverse s t) = is-equiv-equiv-eq-subuniverse s t

  eq-equiv-subuniverse :
    {s t : type-subuniverse P} → equiv-subuniverse s t → s ＝ t
  eq-equiv-subuniverse {s} {t} =
    map-inv-is-equiv (is-equiv-equiv-eq-subuniverse s t)
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

  is-contr-total-equiv-fam-subuniverse :
    (Y : fam-subuniverse P X) →
    is-contr (Σ (fam-subuniverse P X) (equiv-fam-subuniverse Y))
  is-contr-total-equiv-fam-subuniverse Y =
    is-contr-total-Eq-Π
      ( λ x → equiv-subuniverse P (Y x))
      ( λ x → is-contr-total-equiv-subuniverse P (Y x))

  equiv-eq-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → Y ＝ Z → equiv-fam-subuniverse Y Z
  equiv-eq-fam-subuniverse Y .Y refl = id-equiv-fam-subuniverse Y

  is-equiv-equiv-eq-fam-subuniverse :
    (Y Z : fam-subuniverse P X) → is-equiv (equiv-eq-fam-subuniverse Y Z)
  is-equiv-equiv-eq-fam-subuniverse Y =
    fundamental-theorem-id
      ( is-contr-total-equiv-fam-subuniverse Y)
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
