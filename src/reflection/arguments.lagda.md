# Arguments

```agda
module reflection.arguments where
```

<details><summary>Imports</summary>

```agda
open import foundation.universe-levels
```

</details>

## Idea

An argument to a function is a term together with some information about it. The
argument has three properties:

1. Visibility: whether they are visible, hidden, or an instance
2. Relevance: whether they are relevant or not (see,
   [docs](https://agda.readthedocs.io/en/latest/language/irrelevance.html))
3. Quantity: whether they are run-time relevant or not (see,
   [docs](https://agda.readthedocs.io/en/latest/language/runtime-irrelevance.html))

The properties of `Relevance` and `Quantity` are combined in one, called
`Modality`.

For concrete examples, see
[`reflection.definitions`](reflection.definitions.md).

## Definitions

```agda
data Visibility : UU lzero where
  visible hidden instance′ : Visibility

data Relevance : UU lzero where
  relevant irrelevant : Relevance

data Quantity : UU lzero where
  quantity-0 quantity-ω : Quantity

data Modality : UU lzero where
  modality : (r : Relevance) (q : Quantity) → Modality

data ArgInfo : UU lzero where
  arg-info : (v : Visibility) (m : Modality) → ArgInfo

data Arg {l} (A : UU l) : UU l where
  arg : (i : ArgInfo) (x : A) → Arg A
```

<details><summary>Bindings</summary>

```agda
{-# BUILTIN HIDING Visibility #-}
{-# BUILTIN VISIBLE visible #-}
{-# BUILTIN HIDDEN hidden #-}
{-# BUILTIN INSTANCE instance′ #-}

{-# BUILTIN RELEVANCE Relevance #-}
{-# BUILTIN RELEVANT relevant #-}
{-# BUILTIN IRRELEVANT irrelevant #-}

{-# BUILTIN QUANTITY Quantity #-}
{-# BUILTIN QUANTITY-0 quantity-0 #-}
{-# BUILTIN QUANTITY-ω quantity-ω #-}

{-# BUILTIN MODALITY Modality #-}
{-# BUILTIN MODALITY-CONSTRUCTOR modality #-}

{-# BUILTIN ARGINFO ArgInfo #-}
{-# BUILTIN ARGARGINFO arg-info #-}

{-# BUILTIN ARG Arg #-}
{-# BUILTIN ARGARG arg #-}
```

</details>

## Helpers

We create helper patterns for the two most common type of arguments.

```agda
-- visible-Arg : {l : Level} {A : UU l} → A → Arg A
pattern visible-Arg t = arg (arg-info visible (modality relevant quantity-ω)) t

-- hidden-Arg : {l : Level} {A : UU l} → A → Arg A
pattern hidden-Arg t = arg (arg-info hidden (modality relevant quantity-ω)) t
```
