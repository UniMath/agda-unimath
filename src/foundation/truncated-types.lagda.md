# Truncated types

```agda
module foundation.truncated-types where

open import foundation-core.truncated-types public
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.natural-numbers

open import foundation.dependent-pair-types
open import foundation.equivalences
open import foundation.logical-equivalences
open import foundation.subtype-identity-principle
open import foundation.truncation-levels
open import foundation.univalence
open import foundation.universe-levels

open import foundation-core.embeddings
open import foundation-core.identity-types
open import foundation-core.iterated-successors-truncation-levels
open import foundation-core.subtypes
open import foundation-core.torsorial-type-families
```

</details>

## Definition

### The subuniverse of truncated types is itself truncated

```agda
is-torsorial-equiv-Truncated-Type :
  {l : Level} {k : 𝕋} (A : Truncated-Type l k) →
  is-torsorial (type-equiv-Truncated-Type A)
is-torsorial-equiv-Truncated-Type A =
  is-torsorial-Eq-subtype
    ( is-torsorial-equiv (type-Truncated-Type A))
    ( is-prop-is-trunc _)
    ( type-Truncated-Type A)
    ( id-equiv)
    ( is-trunc-type-Truncated-Type A)

extensionality-Truncated-Type :
  {l : Level} {k : 𝕋} (A B : Truncated-Type l k) →
  (A ＝ B) ≃ type-equiv-Truncated-Type A B
extensionality-Truncated-Type A =
  extensionality-type-subtype
    ( is-trunc-Prop _)
    ( is-trunc-type-Truncated-Type A)
    ( id-equiv)
    ( λ X → equiv-univalence)

abstract
  is-trunc-Truncated-Type :
    {l : Level} (k : 𝕋) → is-trunc (succ-𝕋 k) (Truncated-Type l k)
  is-trunc-Truncated-Type k X Y =
    is-trunc-equiv k
      ( type-equiv-Truncated-Type X Y)
      ( extensionality-Truncated-Type X Y)
      ( is-trunc-type-equiv-Truncated-Type X Y)

Truncated-Type-Truncated-Type :
  (l : Level) (k : 𝕋) → Truncated-Type (lsuc l) (succ-𝕋 k)
pr1 (Truncated-Type-Truncated-Type l k) = Truncated-Type l k
pr2 (Truncated-Type-Truncated-Type l k) = is-trunc-Truncated-Type k
```

### The embedding of the subuniverse of truncated types into the universe

```agda
emb-type-Truncated-Type : (l : Level) (k : 𝕋) → Truncated-Type l k ↪ UU l
emb-type-Truncated-Type l k = emb-subtype (is-trunc-Prop k)
```

### If a type is `k`-truncated, then it is `k+r`-truncated

```agda
abstract
  is-trunc-iterated-succ-is-trunc :
    (k : 𝕋) (r : ℕ) {l : Level} {A : UU l} →
    is-trunc k A → is-trunc (iterate-succ-𝕋' k r) A
  is-trunc-iterated-succ-is-trunc k zero-ℕ is-trunc-A = is-trunc-A
  is-trunc-iterated-succ-is-trunc k (succ-ℕ r) is-trunc-A =
    is-trunc-iterated-succ-is-trunc (succ-𝕋 k) r
      ( is-trunc-succ-is-trunc k is-trunc-A)

truncated-type-iterated-succ-Truncated-Type :
  (k : 𝕋) (r : ℕ) {l : Level} →
  Truncated-Type l k → Truncated-Type l (iterate-succ-𝕋' k r)
pr1 (truncated-type-iterated-succ-Truncated-Type k r A) = type-Truncated-Type A
pr2 (truncated-type-iterated-succ-Truncated-Type k r A) =
  is-trunc-iterated-succ-is-trunc k r (is-trunc-type-Truncated-Type A)
```

### Two equivalent types are equivalently `k`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  equiv-is-trunc-equiv : A ≃ B → is-trunc k A ≃ is-trunc k B
  equiv-is-trunc-equiv e =
    equiv-iff-is-prop
      ( is-prop-is-trunc k A)
      ( is-prop-is-trunc k B)
      ( is-trunc-equiv' k A e)
      ( is-trunc-equiv k B e)
```

### If the domain or codomain is `k+1`-truncated, then the type of equivalences is `k+1`-truncated

```agda
module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  is-trunc-equiv-is-trunc-codomain :
    is-trunc (succ-𝕋 k) B → is-trunc (succ-𝕋 k) (A ≃ B)
  is-trunc-equiv-is-trunc-codomain is-trunc-B =
    is-trunc-type-subtype
      ( k)
      ( is-equiv-Prop)
      ( is-trunc-function-type (succ-𝕋 k) is-trunc-B)

module _
  {l1 l2 : Level} (k : 𝕋) {A : UU l1} {B : UU l2}
  where

  is-trunc-equiv-is-trunc-domain :
    is-trunc (succ-𝕋 k) A → is-trunc (succ-𝕋 k) (A ≃ B)
  is-trunc-equiv-is-trunc-domain is-trunc-A =
    is-trunc-equiv
      ( succ-𝕋 k)
      ( B ≃ A)
      ( equiv-inv-equiv)
      ( is-trunc-equiv-is-trunc-codomain k is-trunc-A)
```
