# Function types

```agda
module foundation.function-types where

open import foundation-core.function-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-dependent-functions
open import foundation.function-extensionality
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.homotopies
open import foundation-core.identity-types
open import foundation-core.transport
```

</details>

## Properties

### Transport in a family of function types

```agda
module _
  {l1 l2 l3 : Level} {A : UU l1} {x y : A} (B : A → UU l2) (C : A → UU l3)
  where

  tr-function-type :
    (p : x ＝ y) (f : B x → C x) →
    tr (λ a → B a → C a) p f ＝ (tr C p ∘ (f ∘ tr B (inv p)))
  tr-function-type refl f = refl

  compute-dependent-identification-function-type :
    (p : x ＝ y) (f : B x → C x) (g : B y → C y) →
    ((b : B x) → tr C p (f b) ＝ g (tr B p b)) ≃
    (tr (λ a → B a → C a) p f ＝ g)
  compute-dependent-identification-function-type refl f g =
    inv-equiv equiv-funext

  map-compute-dependent-identification-function-type :
    (p : x ＝ y) (f : B x → C x) (g : B y → C y) →
    ((b : B x) → tr C p (f b) ＝ g (tr B p b)) →
    (tr (λ a → B a → C a) p f ＝ g)
  map-compute-dependent-identification-function-type p f g =
    map-equiv (compute-dependent-identification-function-type p f g)
```

Relation between`compute-dependent-identification-function-type` and
`preserves-tr`

```agda
module _
  {l1 l2 l3 : Level} {I : UU l1} {i0 i1 : I} {A : I → UU l2} {B : I → UU l3}
  (f : (i : I) → A i → B i)
  where

  preserves-tr-apd-function :
    (p : i0 ＝ i1) (a : A i0) →
    map-inv-equiv
      ( compute-dependent-identification-function-type A B p (f i0) (f i1))
      ( apd f p) a ＝
    inv-htpy (preserves-tr f p) a
  preserves-tr-apd-function refl = refl-htpy
```
