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

1. Visibility-Argument-Agda: whether they are visible, hidden, or an instance
2. Relevance-Argument-Agda: whether they are relevant or not (see,
   [docs](https://agda.readthedocs.io/en/latest/language/irrelevance.html))
3. Quantity-Argument-Agda: whether they are run-time relevant or not (see,
   [docs](https://agda.readthedocs.io/en/latest/language/runtime-irrelevance.html))

The properties of `Relevance-Argument-Agda` and `Quantity-Argument-Agda` are
combined in one, called `Modality-Argument-Agda`.

For concrete examples, see
[`reflection.definitions`](reflection.definitions.md).

## Definitions

```agda
data Visibility-Argument-Agda : UU lzero where
  visible hidden instance′ : Visibility-Argument-Agda

data Relevance-Argument-Agda : UU lzero where
  relevant irrelevant : Relevance-Argument-Agda

data Quantity-Argument-Agda : UU lzero where
  quantity-0 quantity-ω : Quantity-Argument-Agda

data Modality-Argument-Agda : UU lzero where
  modality :
    (r : Relevance-Argument-Agda)
    (q : Quantity-Argument-Agda) →
    Modality-Argument-Agda

data Info-Argument-Agda : UU lzero where
  arg-info :
    (v : Visibility-Argument-Agda)
    (m : Modality-Argument-Agda) →
    Info-Argument-Agda

data Argument-Agda {l} (A : UU l) : UU l where
  arg : (i : Info-Argument-Agda) (x : A) → Argument-Agda A
```

<details><summary>Bindings</summary>

```agda
{-# BUILTIN HIDING Visibility-Argument-Agda #-}
{-# BUILTIN VISIBLE visible #-}
{-# BUILTIN HIDDEN hidden #-}
{-# BUILTIN INSTANCE instance′ #-}

{-# BUILTIN RELEVANCE Relevance-Argument-Agda #-}
{-# BUILTIN RELEVANT relevant #-}
{-# BUILTIN IRRELEVANT irrelevant #-}

{-# BUILTIN QUANTITY Quantity-Argument-Agda #-}
{-# BUILTIN QUANTITY-0 quantity-0 #-}
{-# BUILTIN QUANTITY-ω quantity-ω #-}

{-# BUILTIN MODALITY Modality-Argument-Agda #-}
{-# BUILTIN MODALITY-CONSTRUCTOR modality #-}

{-# BUILTIN ARGINFO Info-Argument-Agda #-}
{-# BUILTIN ARGARGINFO arg-info #-}

{-# BUILTIN ARG Argument-Agda #-}
{-# BUILTIN ARGARG arg #-}
```

</details>

## Helpers

We create helper patterns for the two most common type of arguments.

```agda
-- visible-Argument-Agda : {l : Level} {A : UU l} → A → Argument-Agda A
pattern visible-Argument-Agda t =
  arg (arg-info visible (modality relevant quantity-ω)) t

-- hidden-Argument-Agda : {l : Level} {A : UU l} → A → Argument-Agda A
pattern hidden-Argument-Agda t =
  arg (arg-info hidden (modality relevant quantity-ω)) t
```
