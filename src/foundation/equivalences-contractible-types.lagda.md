# Equivalences between contractible types

```agda
module foundation.equivalences-contractible-types where
```

<details><summary>Imports<summary>

```agda
open import foundation.dependent-pair-types
open import foundation.dependent-products-contractible-types
open import foundation.universe-levels

open import foundation-core.contractible-types
open import foundation-core.equivalences
```

</details>

## Idea

[Equivalences](foundation-core.equivalences.md) between [contractible types](foundation-core.contractible-types.md) enjoy some properties, which we will study here. For instance, for any map `f : A → B`, if two out of three of the following properties hold, then so does the third:

1. The type `A` is contractible.
2. The type `B` is contractible.
3. The map `f` is an equivalence.

Moreover, if `A` and `B` are contractible, then the type of equivalences between them is contractible.

## Properties

### Contractible types are closed under equivalences

```agda
module _
  {l1 l2 : Level} {A : UU l1} (B : UU l2)
  where

  abstract
    is-contr-is-equiv :
      (f : A → B) → is-equiv f → is-contr B → is-contr A
    is-contr-is-equiv f H =
      is-contr-retract-of B (f , retraction-is-equiv H)

  abstract
    is-contr-equiv :
      A ≃ B → is-contr B → is-contr A
    is-contr-equiv (e , H) =
      is-contr-is-equiv e H

module _
  {l1 l2 : Level} (A : UU l1) {B : UU l2}
  where

  abstract
    is-contr-is-equiv' :
      (f : A → B) → is-equiv f → is-contr A → is-contr B
    is-contr-is-equiv' f H =
      is-contr-is-equiv A
        ( map-inv-is-equiv H)
        ( is-equiv-map-inv-is-equiv H)

  abstract
    is-contr-equiv' :
      (e : A ≃ B) → is-contr A → is-contr B
    is-contr-equiv' (e , H) = is-contr-is-equiv' e H

module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  abstract
    is-equiv-is-contr :
      (f : A → B) → is-contr A → is-contr B → is-equiv f
    is-equiv-is-contr f H K =
      is-equiv-is-invertible
        ( λ y → center H)
        ( λ y → eq-is-contr K)
        ( contraction H)

  equiv-is-contr :
    is-contr A → is-contr B → A ≃ B
  pr1 (equiv-is-contr H K) a =
    center K
  pr2 (equiv-is-contr H K) =
    is-equiv-is-contr _ H K
```

### The type of equivalences between contractible types is contractible

```agda
module _
  {l1 l2 : Level} {A : UU l1} {B : UU l2}
  where

  is-contr-equiv-is-contr :
    is-contr A → is-contr B → is-contr (A ≃ B)
  is-contr-equiv-is-contr (a , α) (b , β) =
    is-contr-Σ
      ( is-contr-function-type (b , β))
      ( λ x → b)
      ( is-contr-product
        ( is-contr-Σ
          ( is-contr-function-type (a , α))
          ( λ y → a)
          ( is-contr-Π (is-prop-is-contr (b , β) b)))
        ( is-contr-Σ
          ( is-contr-function-type (a , α))
          ( λ y → a)
          ( is-contr-Π (is-prop-is-contr (a , α) a))))
```

