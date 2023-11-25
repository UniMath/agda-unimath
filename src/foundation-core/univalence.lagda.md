# The univalence axiom

```agda
module foundation-core.univalence where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.fundamental-theorem-of-identity-types
open import foundation.universe-levels

open import foundation-core.equivalences
open import foundation-core.function-types
open import foundation-core.identity-types
open import foundation-core.torsorial-type-families
open import foundation-core.transport-along-identifications
```

</details>

## Idea

The univalence axiom characterizes the identity types of universes. It asserts
that the map `Id A B → A ≃ B` is an equivalence.

In this file, we define the statement of the axiom. The axiom itself is
postulated in [`foundation.univalence`](foundation.univalence.md) as
`univalence`.

## Statement

```agda
equiv-eq : {l : Level} {A : UU l} {B : UU l} → A ＝ B → A ≃ B
equiv-eq refl = id-equiv

map-eq : {l : Level} {A : UU l} {B : UU l} → A ＝ B → A → B
map-eq = map-equiv ∘ equiv-eq

instance-univalence : {l : Level} (A B : UU l) → UU (lsuc l)
instance-univalence A B = is-equiv (equiv-eq {A = A} {B = B})

based-univalence-axiom : {l : Level} (A : UU l) → UU (lsuc l)
based-univalence-axiom {l} A = (B : UU l) → instance-univalence A B

univalence-axiom-Level : (l : Level) → UU (lsuc l)
univalence-axiom-Level l = (A B : UU l) → instance-univalence A B

univalence-axiom : UUω
univalence-axiom = {l : Level} → univalence-axiom-Level l
```

## Properties

### The univalence axiom implies that the total space of equivalences is contractible

```agda
abstract
  is-torsorial-equiv-based-univalence :
    {l : Level} (A : UU l) →
    based-univalence-axiom A → is-torsorial (λ (B : UU l) → A ≃ B)
  is-torsorial-equiv-based-univalence A UA =
    fundamental-theorem-id' (λ B → equiv-eq) UA
```

### Contractibility of the total space of equivalences implies univalence

```agda
abstract
  based-univalence-is-torsorial-equiv :
    {l : Level} (A : UU l) →
    is-torsorial (λ (B : UU l) → A ≃ B) → based-univalence-axiom A
  based-univalence-is-torsorial-equiv A c =
    fundamental-theorem-id c (λ B → equiv-eq)
```

### Computing transport

```agda
compute-equiv-eq-ap :
  {l1 l2 : Level} {A : UU l1} {B : A → UU l2} {x y : A}
  (p : x ＝ y) → map-equiv (equiv-eq (ap B p)) ＝ tr B p
compute-equiv-eq-ap refl = refl
```
