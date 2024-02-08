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

The properties of `Relevance-Argument-Agda` and `Quantity-Argument-Agda` are
combined in one, called `Modality-Argument-Agda`.

For concrete examples, see
[`reflection.definitions`](reflection.definitions.md).

## Definitions

```agda
data Visibility-Argument-Agda : UU lzero where
  visible-Visibility-Argument-Agda : Visibility-Argument-Agda
  hidden-Visibility-Argument-Agda : Visibility-Argument-Agda
  instance-Visibility-Argument-Agda : Visibility-Argument-Agda

data Relevance-Argument-Agda : UU lzero where
  relevant-Relevance-Argument-Agda : Relevance-Argument-Agda
  irrelevant-Relevance-Argument-Agda : Relevance-Argument-Agda

data Quantity-Argument-Agda : UU lzero where
  zero-Quantity-Argument-Agda : Quantity-Argument-Agda
  omega-Quantity-Argument-Agda : Quantity-Argument-Agda

data Modality-Argument-Agda : UU lzero where
  cons-Modality-Argument-Agda :
    Relevance-Argument-Agda → Quantity-Argument-Agda → Modality-Argument-Agda

data Info-Argument-Agda : UU lzero where
  cons-Info-Argument-Agda :
    Visibility-Argument-Agda → Modality-Argument-Agda → Info-Argument-Agda

data Argument-Agda {l : Level} (A : UU l) : UU l where
  cons-Argument-Agda : Info-Argument-Agda → A → Argument-Agda A
```

<details><summary>Bindings</summary>

```agda
{-# BUILTIN HIDING Visibility-Argument-Agda #-}
{-# BUILTIN VISIBLE visible-Visibility-Argument-Agda #-}
{-# BUILTIN HIDDEN hidden-Visibility-Argument-Agda #-}
{-# BUILTIN INSTANCE instance-Visibility-Argument-Agda #-}

{-# BUILTIN RELEVANCE Relevance-Argument-Agda #-}
{-# BUILTIN RELEVANT relevant-Relevance-Argument-Agda #-}
{-# BUILTIN IRRELEVANT irrelevant-Relevance-Argument-Agda #-}

{-# BUILTIN QUANTITY Quantity-Argument-Agda #-}
{-# BUILTIN QUANTITY-0 zero-Quantity-Argument-Agda #-}
{-# BUILTIN QUANTITY-ω omega-Quantity-Argument-Agda #-}

{-# BUILTIN MODALITY Modality-Argument-Agda #-}
{-# BUILTIN MODALITY-CONSTRUCTOR cons-Modality-Argument-Agda #-}

{-# BUILTIN ARGINFO Info-Argument-Agda #-}
{-# BUILTIN ARGARGINFO cons-Info-Argument-Agda #-}

{-# BUILTIN ARG Argument-Agda #-}
{-# BUILTIN ARGARG cons-Argument-Agda #-}
```

</details>

## Helpers

We create helper patterns for the two most common type of arguments.

```agda
-- visible-Argument-Agda : {l : Level} {A : UU l} → A → Argument-Agda A
pattern visible-Argument-Agda t =
  cons-Argument-Agda
    ( cons-Info-Argument-Agda
      ( visible-Visibility-Argument-Agda)
      ( cons-Modality-Argument-Agda
        ( relevant-Relevance-Argument-Agda)
        ( omega-Quantity-Argument-Agda)))
    ( t)

-- hidden-Argument-Agda : {l : Level} {A : UU l} → A → Argument-Agda A
pattern hidden-Argument-Agda t =
  cons-Argument-Agda
    ( cons-Info-Argument-Agda
      ( hidden-Visibility-Argument-Agda)
      ( cons-Modality-Argument-Agda
        ( relevant-Relevance-Argument-Agda)
        ( omega-Quantity-Argument-Agda)))
    ( t)
```
