# Inhabited finite types

```agda
module univalent-combinatorics.inhabited-finite-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.inhabited-types
open import foundation.universe-levels

open import univalent-combinatorics.dependent-sum-finite-types
open import univalent-combinatorics.finite-types
```

</details>

## Idea

## Definitions

### Inhabited finite types

```agda
Inhabited-Type-𝔽 : (l : Level) → UU (lsuc l)
Inhabited-Type-𝔽 l = Σ ( 𝔽 l) ( λ X → is-inhabited (type-𝔽 X))

module _
  {l : Level} (X : Inhabited-Type-𝔽 l)
  where

  finite-type-Inhabited-Type-𝔽 : 𝔽 l
  finite-type-Inhabited-Type-𝔽 = pr1 X

  type-Inhabited-Type-𝔽 : UU l
  type-Inhabited-Type-𝔽 = type-𝔽 finite-type-Inhabited-Type-𝔽

  is-finite-Inhabited-Type-𝔽 : is-finite type-Inhabited-Type-𝔽
  is-finite-Inhabited-Type-𝔽 = is-finite-type-𝔽 finite-type-Inhabited-Type-𝔽

  is-inhabited-type-Inhabited-Type-𝔽 : is-inhabited type-Inhabited-Type-𝔽
  is-inhabited-type-Inhabited-Type-𝔽 = pr2 X

  inhabited-type-Inhabited-Type-𝔽 : Inhabited-Type l
  pr1 inhabited-type-Inhabited-Type-𝔽 = type-Inhabited-Type-𝔽
  pr2 inhabited-type-Inhabited-Type-𝔽 = is-inhabited-type-Inhabited-Type-𝔽
```

### Families of inhabited types

```agda
Fam-Inhabited-Types-𝔽 :
  {l1 : Level} → (l2 : Level) → (X : 𝔽 l1) → UU (l1 ⊔ lsuc l2)
Fam-Inhabited-Types-𝔽 l2 X = type-𝔽 X → Inhabited-Type-𝔽 l2

module _
  {l1 l2 : Level} (X : 𝔽 l1) (Y : Fam-Inhabited-Types-𝔽 l2 X)
    where

  type-Fam-Inhabited-Types-𝔽 : type-𝔽 X → UU l2
  type-Fam-Inhabited-Types-𝔽 x = type-Inhabited-Type-𝔽 (Y x)

  finite-type-Fam-Inhabited-Types-𝔽 : type-𝔽 X → 𝔽 l2
  pr1 (finite-type-Fam-Inhabited-Types-𝔽 x) = type-Fam-Inhabited-Types-𝔽 x
  pr2 (finite-type-Fam-Inhabited-Types-𝔽 x) = is-finite-Inhabited-Type-𝔽 (Y x)

  is-inhabited-type-Fam-Inhabited-Types-𝔽 :
    (x : type-𝔽 X) → is-inhabited (type-Fam-Inhabited-Types-𝔽 x)
  is-inhabited-type-Fam-Inhabited-Types-𝔽 x =
    is-inhabited-type-Inhabited-Type-𝔽 (Y x)

  total-Fam-Inhabited-Types-𝔽 : 𝔽 (l1 ⊔ l2)
  total-Fam-Inhabited-Types-𝔽 = Σ-𝔽 X finite-type-Fam-Inhabited-Types-𝔽

```
