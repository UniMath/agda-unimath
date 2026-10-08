# Torsorial type families

```agda
module foundation.torsorial-type-families where

open import foundation-core.torsorial-type-families public
```

<details><summary>Imports</summary>

```agda
open import foundation.contractible-types
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.fundamental-theorem-of-identity-types
open import foundation.logical-equivalences
open import foundation.universal-property-identity-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
open import foundation-core.subuniverse-of-contractible-types
open import foundation-core.type-theoretic-principle-of-choice
```

</details>

## Idea

A type family `E` over `B` is said to be **torsorial** if its
[total space](foundation.dependent-pair-types.md) is
[contractible](foundation.contractible-types.md). By the
[fundamental theorem of identity types](foundation.fundamental-theorem-of-identity-types.md)
it follows that a type family `E` is torsorial if and only if it is in the
[image](foundation.images.md) of `Id : B → (B → 𝒰)`.

## Definitions

### The predicate of being a torsorial type family over `B`

```agda
is-torsorial-Prop :
  {l1 l2 : Level} {B : UU l1} → (B → UU l2) → Prop (l1 ⊔ l2)
is-torsorial-Prop E = is-contr-Prop (Σ _ E)

is-prop-is-torsorial :
  {l1 l2 : Level} {B : UU l1} (E : B → UU l2) → is-prop (is-torsorial E)
is-prop-is-torsorial E = is-prop-type-Prop (is-torsorial-Prop E)
```

### The type of torsorial type families over `B`

```agda
torsorial-family-of-types :
  {l1 : Level} (l2 : Level) → UU l1 → UU (l1 ⊔ lsuc l2)
torsorial-family-of-types l2 B = Σ (B → UU l2) is-torsorial

module _
  {l1 l2 : Level} {B : UU l1} (T : torsorial-family-of-types l2 B)
  where

  type-torsorial-family-of-types : B → UU l2
  type-torsorial-family-of-types = pr1 T

  is-torsorial-torsorial-family-of-types :
    is-torsorial type-torsorial-family-of-types
  is-torsorial-torsorial-family-of-types = pr2 T
```

## Properties

### `fiber Id B ≃ is-torsorial B` for any type family `B` over `A`

In other words, a type family `B` over `A` is in the
[image](foundation.images.md) of `Id : A → (A → 𝒰)` if and only if `B` is
torsorial. Since being contractible is a
[proposition](foundation.propositions.md), this observation leads to an
alternative proof of the above claim that `Id : A → (A → 𝒰)` is an
[embedding](foundation.embeddings.md). Our previous proof of the fact that
`Id : A → (A → 𝒰)` is an embedding can be found in
[`foundation.universal-property-identity-types`](foundation.universal-property-identity-types.md).

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2}
  where

  is-torsorial-fiber-Id :
    {a : A} → ((x : A) → (a ＝ x) ≃ B x) → is-torsorial B
  is-torsorial-fiber-Id H =
    fundamental-theorem-id'
      ( λ x → map-equiv (H x))
      ( λ x → is-equiv-map-equiv (H x))

  fiber-Id-is-torsorial :
    is-torsorial B → Σ A (λ a → (x : A) → (a ＝ x) ≃ B x)
  pr1 (fiber-Id-is-torsorial ((a , b) , H)) = a
  pr2 (fiber-Id-is-torsorial ((a , b) , H)) =
    map-inv-distributive-Π-Σ (f , fundamental-theorem-id ((a , b) , H) f)
    where
    f : (x : A) → (a ＝ x) → B x
    f x refl = b

  compute-fiber-Id :
    (Σ A (λ a → (x : A) → (a ＝ x) ≃ B x)) ≃ is-torsorial B
  compute-fiber-Id =
    equiv-iff
      ( Σ A (λ a → (x : A) → (a ＝ x) ≃ B x) ,
        is-prop-total-family-of-equivalences-Id)
      ( is-contr-Prop (Σ A B))
      ( λ u → is-torsorial-fiber-Id (pr2 u))
      ( fiber-Id-is-torsorial)
```

### See also

- [Discrete reflexive relations](foundation.discrete-reflexive-relations.md) are
  binary torsorial type families.
