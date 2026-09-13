# The subuniverse of contractible types

```agda
module foundation.subuniverse-of-contractible-types where

open import foundation-core.subuniverse-of-contractible-types public
```

<details><summary>Imports</summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.equivalences-contractible-types
open import foundation.logical-equivalences
open import foundation.raising-universe-levels-unit-type
open import foundation.subuniverses
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
open import foundation-core.identity-types
open import foundation-core.propositions
```

</details>

## Idea

Since being [contractible](foundation-core.contractible-types.md) is a
[property](foundation-core.propositions.md), we obtain a
[subuniverse](foundation.subuniverses.md) of contractible types.

## Definition

### The subuniverse of contractible types

```agda
Contr : (l : Level) → UU (lsuc l)
Contr l = type-subuniverse is-contr-Prop

type-Contr : {l : Level} → Contr l → UU l
type-Contr A = pr1 A

abstract
  is-contr-type-Contr :
    {l : Level} (A : Contr l) → is-contr (type-Contr A)
  is-contr-type-Contr A = pr2 A

equiv-Contr :
  {l1 l2 : Level} (X : Contr l1) (Y : Contr l2) → UU (l1 ⊔ l2)
equiv-Contr X Y = type-Contr X ≃ type-Contr Y

equiv-eq-Contr :
  {l1 : Level} (X Y : Contr l1) → X ＝ Y → equiv-Contr X Y
equiv-eq-Contr X Y = equiv-eq-subuniverse is-contr-Prop X Y

abstract
  is-equiv-equiv-eq-Contr :
    {l1 : Level} (X Y : Contr l1) → is-equiv (equiv-eq-Contr X Y)
  is-equiv-equiv-eq-Contr X Y =
    is-equiv-equiv-eq-subuniverse is-contr-Prop X Y

eq-equiv-Contr :
  {l1 : Level} {X Y : Contr l1} → equiv-Contr X Y → X ＝ Y
eq-equiv-Contr = eq-equiv-subuniverse is-contr-Prop

abstract
  center-Contr : (l : Level) → Contr l
  center-Contr l = pair (raise-unit l) is-contr-raise-unit

  contraction-Contr :
    {l : Level} (A : Contr l) → center-Contr l ＝ A
  contraction-Contr A =
    eq-equiv-Contr
      ( equiv-is-contr is-contr-raise-unit (is-contr-type-Contr A))

abstract
  is-contr-Contr : (l : Level) → is-contr (Contr l)
  is-contr-Contr l = pair (center-Contr l) contraction-Contr
```

### If two types are equivalent then so are the propositions that they are in the subuniverse of contractible types

```agda
equiv-is-contr-equiv :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} → A ≃ B → is-contr A ≃ is-contr B
equiv-is-contr-equiv {A = A} {B = B} e =
  equiv-iff-is-prop
    ( is-property-is-contr)
    ( is-property-is-contr)
    ( is-contr-retract-of A
      ( map-inv-equiv e , map-equiv e , is-section-map-inv-equiv e))
    ( is-contr-retract-of B
      ( map-equiv e , map-inv-equiv e , is-retraction-map-inv-equiv e))
```
