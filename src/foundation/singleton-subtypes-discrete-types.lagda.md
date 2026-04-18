# Singleton subtypes of discrete types

```agda
module foundation.singleton-subtypes-discrete-types where
```

<details><summary>Imports</summary>

```agda
open import foundation.action-on-identifications-functions
open import foundation.decidable-subtypes
open import foundation.dependent-pair-types
open import foundation.discrete-types
open import foundation.functoriality-coproduct-types
open import foundation.identity-types
open import foundation.singleton-subtypes
open import foundation.universe-levels

open import foundation-core.subtypes
open import foundation-core.transport-along-identifications
```

</details>

## Idea

[Singleton subtypes](foundation.singleton-subtypes.md) on
[discrete types](foundation.discrete-types.md) are
[decidable subtypes](foundation.decidable-subtypes.md).

## Properties

### Any singleton subtype of a discrete type is decidable

```agda
module _
  {l1 l2 : Level}
  (XD@(X , decide-eq-X) : Discrete-Type l1)
  (S : subtype l2 X)
  (((x , x∈S) , is-center-x) : is-singleton-subtype S)
  where

  is-decidable-is-singleton-subtype-Discrete-Type : is-decidable-subtype S
  is-decidable-is-singleton-subtype-Discrete-Type y =
    map-coproduct
      ( λ x=y → tr (is-in-subtype S) x=y x∈S)
      ( λ x≠y y∈S → x≠y (ap (inclusion-subtype S) (is-center-x (y , y∈S))))
      ( decide-eq-X x y)
```

### The standard decidable singleton subtype associated with an element of a discrete type

```agda
module _
  {l : Level}
  (XD@(X , decide-eq-X) : Discrete-Type l)
  where

  decidable-standard-singleton-subtype-Discrete-Type :
    X → decidable-subtype l X
  decidable-standard-singleton-subtype-Discrete-Type y x =
    ( x ＝ y ,
      is-set-type-Discrete-Type XD x y ,
      decide-eq-X x y)
```
