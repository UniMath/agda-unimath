# Strongly extensional maps

```agda
open import foundation.function-extensionality-axiom

module
  foundation.strongly-extensional-maps
  (funext : function-extensionality)
  where
```

<details><summary>Imports</summary>

```agda
open import foundation.apartness-relations funext
open import foundation.universe-levels
```

</details>

## Idea

Consider a function `f : A → B` between types equipped with apartness relations.
Then we say that `f` is **strongly extensional** if

```text
  f x # f y → x # y
```

## Definition

```agda
strongly-extensional :
  {l1 l2 l3 l4 : Level} (A : Type-With-Apartness l1 l2)
  (B : Type-With-Apartness l3 l4) →
  (type-Type-With-Apartness A → type-Type-With-Apartness B) → UU (l1 ⊔ l2 ⊔ l4)
strongly-extensional A B f =
  (x y : type-Type-With-Apartness A) →
  apart-Type-With-Apartness B (f x) (f y) → apart-Type-With-Apartness A x y
```

## Properties

```text
is-strongly-extensional :
  {l1 l2 l3 l4 : Level} (A : Type-With-Apartness l1 l2)
  (B : Type-With-Apartness l3 l4) →
  (f : type-Type-With-Apartness A → type-Type-With-Apartness B) →
  strongly-extensional A B f
is-strongly-extensional A B f x y H = {!!}
```
