# Wide global function classes

```agda
module orthogonal-factorization-systems.wide-global-function-classes where
```

<details><summary>Imports</summary>

```agda
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.embeddings
open import foundation.function-types
open import foundation.propositions
open import foundation.universe-levels

open import orthogonal-factorization-systems.function-classes
open import orthogonal-factorization-systems.global-function-classes
```

</details>

## Idea

We say a
[global function class](orthogonal-factorization-systems.function-classes.md) is
**wide** if it contains all [equivalences](foundation-core.equivalences.md) and
is composition closed. This means it is morally a wide sub-∞-category of the
∞-category of types.

## Definition

```agda
record wide-global-function-class (β : Level → Level → Level) : UUω where
  field

    global-function-class-wide-global-function-class :
      global-function-class β

    has-equivalences-wide-global-function-class :
      has-equivalences-global-function-class
        global-function-class-wide-global-function-class

    is-closed-under-composition-wide-global-function-class :
      is-closed-under-composition-global-function-class
        global-function-class-wide-global-function-class

open wide-global-function-class public

function-class-wide-global-function-class :
  {β : Level → Level → Level} (P : wide-global-function-class β) →
  {l1 l2 : Level} → function-class l1 l2 (β l1 l2)
function-class-wide-global-function-class P =
  function-class-global-function-class
    ( global-function-class-wide-global-function-class P)

type-wide-global-function-class :
  {β : Level → Level → Level} (P : wide-global-function-class β)
  {l1 l2 : Level} (A : UU l1) (B : UU l2) → UU (β l1 l2 ⊔ l1 ⊔ l2)
type-wide-global-function-class P =
  type-function-class (function-class-wide-global-function-class P)

module _
  {β : Level → Level → Level} (P : wide-global-function-class β)
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-in-wide-global-function-class : (A → B) → UU (β l1 l2)
  is-in-wide-global-function-class =
    is-in-function-class (function-class-wide-global-function-class P)

  is-prop-is-in-wide-global-function-class :
    (f : A → B) → is-prop (is-in-wide-global-function-class f)
  is-prop-is-in-wide-global-function-class =
    is-prop-is-in-function-class (function-class-wide-global-function-class P)

  inclusion-wide-global-function-class :
    type-wide-global-function-class P A B → A → B
  inclusion-wide-global-function-class =
    inclusion-function-class (function-class-wide-global-function-class P)

  is-emb-inclusion-wide-global-function-class :
    is-emb inclusion-wide-global-function-class
  is-emb-inclusion-wide-global-function-class =
    is-emb-inclusion-function-class
      ( function-class-wide-global-function-class P)

  emb-wide-global-function-class :
    type-wide-global-function-class P A B ↪ (A → B)
  emb-wide-global-function-class =
    emb-function-class (function-class-wide-global-function-class P)
```
