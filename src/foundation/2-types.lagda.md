# 2-Types

```agda
module foundation.2-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.truncated-types
open import foundation.truncation-levels
open import foundation.universe-levels
```

</details>

## Definition

A 2-type is a type that is 2-truncated

```
is-2-type : {l : Level} → UU l → UU l
is-2-type = is-trunc (two-𝕋)

UU-2-Type : (l : Level) → UU (lsuc l)
UU-2-Type l = Σ (UU l) is-2-type

type-2-Type :
  {l : Level} → UU-2-Type l → UU l
type-2-Type = pr1

abstract
  is-2-type-type-2-Type :
    {l : Level} (A : UU-2-Type l) → is-2-type (type-2-Type A)
  is-2-type-type-2-Type = pr2
```
