# The type checking monad

```agda
{-# OPTIONS --no-exact-split #-}

module reflection.type-checking-monad where
```

<details><summary>Imports</summary>

```agda
open import elementary-number-theory.addition-natural-numbers
open import elementary-number-theory.natural-numbers

open import foundation.booleans
open import foundation.cartesian-product-types
open import foundation.dependent-pair-types
open import foundation.identity-types
open import foundation.unit-type
open import foundation.universe-levels

open import lists.lists

open import primitives.strings

open import reflection.arguments
open import reflection.definitions
open import reflection.metavariables
open import reflection.names
open import reflection.terms
```

</details>

## Idea

The type-checking monad `type-Type-Checker` allows us to interact directly with
Agda's type checking mechanism. Additionally to primitives (see below), Agda
includes the the keyword `unquote` to manually unquote an element from
`type-Type-Checker unit`.

## Definitions

```agda
data Error-Part : UU lzero where
  string-Error-Part : String → Error-Part
  term-Error-Part : Term-Agda → Error-Part
  pattern-Error-Part : Pattern-Agda → Error-Part
  name-Error-Part : Name-Agda → Error-Part

postulate
  -- The type checking monad
  type-Type-Checker :
    {l : Level} → UU l → UU l
  return-Type-Checker :
    {l : Level} {A : UU l} → A → type-Type-Checker A
  bind-Type-Checker :
    {l1 l2 : Level} {A : UU l1} {B : UU l2} →
    type-Type-Checker A → (A → type-Type-Checker B) → type-Type-Checker B
  -- Tries the unify the first term with the second
  unify :
    Term-Agda → Term-Agda → type-Type-Checker unit
  -- Gives an error
  type-error :
    {l : Level} {A : UU l} → list Error-Part → type-Type-Checker A
  -- Infers the type of a goal
  infer-type :
    Term-Agda → type-Type-Checker Term-Agda
  check-type :
    Term-Agda → Term-Agda → type-Type-Checker Term-Agda
  normalize :
    Term-Agda → type-Type-Checker Term-Agda
  reduce :
    Term-Agda → type-Type-Checker Term-Agda
  -- Tries the first computation, if it fails tries the second
  catch-Type-Checker :
    {l : Level} {A : UU l} →
    type-Type-Checker A → type-Type-Checker A → type-Type-Checker A
  quote-Type-Checker :
    {l : Level} {A : UU l} → A → type-Type-Checker Term-Agda
  unquote-Type-Checker :
    {l : Level} {A : UU l} → Term-Agda → type-Type-Checker A
  quoteω-Type-Checker :
    {A : UUω} → A → type-Type-Checker Term-Agda
  get-context :
    type-Type-Checker Telescope-Agda
  extend-context :
    {l : Level} {A : UU l} →
    String → Argument-Agda Term-Agda → type-Type-Checker A → type-Type-Checker A
  in-context :
    {l : Level} {A : UU l} →
    Telescope-Agda → type-Type-Checker A → type-Type-Checker A
  fresh-name :
    String → type-Type-Checker Name-Agda
  declare-definition :
    Argument-Agda Name-Agda → Term-Agda → type-Type-Checker unit
  declare-postulate :
    Argument-Agda Name-Agda → Term-Agda → type-Type-Checker unit
  define-function :
    Name-Agda → list Clause-Agda → type-Type-Checker unit
  get-type :
    Name-Agda → type-Type-Checker Term-Agda
  get-definition :
    Name-Agda → type-Type-Checker Definition-Agda
  block-Type-Checker :
    {l : Level} {A : UU l} → Blocker-Agda → type-Type-Checker A
  commit-Type-Checker :
    type-Type-Checker unit
  is-macro :
    Name-Agda → type-Type-Checker bool

  format-error :
    list Error-Part → type-Type-Checker String

  -- Prints the third argument if the corresponding verbosity Level is turned
  -- on (with the -v flag to Agda).
  debug-print :
    String → ℕ → list Error-Part → type-Type-Checker unit

  -- If 'true', makes the following primitives also normalize
  -- their results: infer-type, check-type, quote-Type-Checker, get-type, and get-context
  with-normalization :
    {l : Level} {A : UU l} → bool → type-Type-Checker A → type-Type-Checker A
  ask-normalization : type-Type-Checker bool

  -- If 'true', makes the following primitives to reconstruct hidden arguments:
  -- get-definition, normalize, reduce, infer-type, check-type and get-context
  with-reconstructed :
    {l : Level} {A : UU l} → bool → type-Type-Checker A → type-Type-Checker A
  ask-reconstructed : type-Type-Checker bool

  -- Whether implicit arguments at the end should be turned into metavariables
  with-expand-last :
    {l : Level} {A : UU l} → bool → type-Type-Checker A → type-Type-Checker A
  ask-expand-last : type-Type-Checker bool

  -- White/blacklist specific definitions for reduction while executing the type-Type-Checker computation
  -- 'true' for whitelist, 'false' for blacklist
  with-reduce-definitions :
    {l : Level} {A : UU l} →
    bool × list Name-Agda → type-Type-Checker A → type-Type-Checker A
  ask-reduce-definitions :
    type-Type-Checker (bool × list Name-Agda)

  -- Fail if the given computation gives rise to new, unsolved
  -- "blocking" constraints.
  no-constraints :
    {l : Level} {A : UU l} → type-Type-Checker A → type-Type-Checker A

  -- Run the given type-Type-Checker action and return the first component. Resets to
  -- the old type-Type-Checker state if the second component is 'false', or keep the
  -- new type-Type-Checker state if it is 'true'.
  run-speculative :
    {l : Level} {A : UU l} → type-Type-Checker (A × bool) → type-Type-Checker A

  -- Get a list of all possible instance candidates for the given metavariable
  -- variable (it does not have to be an instance metavariable).
  get-instances :
    Metavariable-Agda → type-Type-Checker (list Term-Agda)

  declare-data :
    Name-Agda → ℕ → Term-Agda → type-Type-Checker unit
  define-data :
    Name-Agda →
    list (Name-Agda × Quantity-Argument-Agda × Term-Agda) →
    type-Type-Checker unit
```

## Bindings

```agda
{-# BUILTIN AGDAERRORPART Error-Part #-}
{-# BUILTIN AGDAERRORPARTSTRING string-Error-Part #-}
{-# BUILTIN AGDAERRORPARTTERM term-Error-Part #-}
{-# BUILTIN AGDAERRORPARTPATT pattern-Error-Part #-}
{-# BUILTIN AGDAERRORPARTNAME name-Error-Part #-}

{-# BUILTIN AGDATCM type-Type-Checker #-}
{-# BUILTIN AGDATCMRETURN return-Type-Checker #-}
{-# BUILTIN AGDATCMBIND bind-Type-Checker #-}
{-# BUILTIN AGDATCMUNIFY unify #-}
{-# BUILTIN AGDATCMTYPEERROR type-error #-}
{-# BUILTIN AGDATCMINFERTYPE infer-type #-}
{-# BUILTIN AGDATCMCHECKTYPE check-type #-}
{-# BUILTIN AGDATCMNORMALISE normalize #-}
{-# BUILTIN AGDATCMREDUCE reduce #-}
{-# BUILTIN AGDATCMCATCHERROR catch-Type-Checker #-}
{-# BUILTIN AGDATCMQUOTETERM quote-Type-Checker #-}
{-# BUILTIN AGDATCMUNQUOTETERM unquote-Type-Checker #-}
{-# BUILTIN AGDATCMQUOTEOMEGATERM quoteω-Type-Checker #-}
{-# BUILTIN AGDATCMGETCONTEXT get-context #-}
{-# BUILTIN AGDATCMEXTENDCONTEXT extend-context #-}
{-# BUILTIN AGDATCMINCONTEXT in-context #-}
{-# BUILTIN AGDATCMFRESHNAME fresh-name #-}
{-# BUILTIN AGDATCMDECLAREDEF declare-definition #-}
{-# BUILTIN AGDATCMDECLAREPOSTULATE declare-postulate #-}
{-# BUILTIN AGDATCMDEFINEFUN define-function #-}
{-# BUILTIN AGDATCMGETTYPE get-type #-}
{-# BUILTIN AGDATCMGETDEFINITION get-definition #-}
{-# BUILTIN AGDATCMBLOCK block-Type-Checker #-}
{-# BUILTIN AGDATCMCOMMIT commit-Type-Checker #-}
{-# BUILTIN AGDATCMISMACRO is-macro #-}
{-# BUILTIN AGDATCMWITHNORMALISATION with-normalization #-}
{-# BUILTIN AGDATCMFORMATERRORPARTS format-error #-}
{-# BUILTIN AGDATCMDEBUGPRINT debug-print #-}
{-# BUILTIN AGDATCMWITHRECONSTRUCTED with-reconstructed #-}
{-# BUILTIN AGDATCMWITHEXPANDLAST with-expand-last #-}
{-# BUILTIN AGDATCMWITHREDUCEDEFS with-reduce-definitions #-}
{-# BUILTIN AGDATCMASKNORMALISATION ask-normalization #-}
{-# BUILTIN AGDATCMASKRECONSTRUCTED ask-reconstructed #-}
{-# BUILTIN AGDATCMASKEXPANDLAST ask-expand-last #-}
{-# BUILTIN AGDATCMASKREDUCEDEFS ask-reduce-definitions #-}
{-# BUILTIN AGDATCMNOCONSTRAINTS no-constraints #-}
{-# BUILTIN AGDATCMRUNSPECULATIVE run-speculative #-}
{-# BUILTIN AGDATCMGETINSTANCES get-instances #-}
{-# BUILTIN AGDATCMDECLAREDATA declare-data #-}
{-# BUILTIN AGDATCMDEFINEDATA define-data #-}
```

## Monad syntax

```agda
infixl 15 _<|>_
_<|>_ :
  {l : Level} {A : UU l} →
  type-Type-Checker A → type-Type-Checker A → type-Type-Checker A
_<|>_ = catch-Type-Checker

infixl 10 _>>=_ _>>_ _<&>_
_>>=_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-Type-Checker A → (A → type-Type-Checker B) → type-Type-Checker B
_>>=_ = bind-Type-Checker

_>>_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-Type-Checker A → type-Type-Checker B → type-Type-Checker B
xs >> ys = bind-Type-Checker xs (λ _ → ys)

_<&>_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  type-Type-Checker A → (A → B) → type-Type-Checker B
xs <&> f = bind-Type-Checker xs (λ x → return-Type-Checker (f x))
```

## Examples

The following examples show how the type-checking monad can be used. They were
adapted from alhassy's
[_gentle intro to reflection_](https://github.com/alhassy/gentle-intro-to-reflection).

### Unifying a goal with a constant

#### Manually

```agda
private
  num-Type-Checker : Term-Agda → type-Type-Checker unit
  num-Type-Checker h = unify (quoteTerm 314) h

  _ : unquote num-Type-Checker ＝ 314
  _ = refl
```

#### By use of a macro

```agda
  macro
    num-Type-Checker' : Term-Agda → type-Type-Checker unit
    num-Type-Checker' h = unify (quoteTerm 1) h

  _ : num-Type-Checker' ＝ 1
  _ = refl
```

### Modifying a term

```agda
  macro
    swap-add : Term-Agda → Term-Agda → type-Type-Checker unit
    swap-add (definition-Term-Agda (quote add-ℕ) (cons a (cons b nil))) hole =
      unify hole (definition-Term-Agda (quote add-ℕ) (cons b (cons a nil)))
    {-# CATCHALL #-}
    swap-add v hole = unify hole v

  ex1 : (a b : ℕ) → swap-add (add-ℕ a b) ＝ (add-ℕ b a)
  ex1 a b = refl

  ex2 : (a b : ℕ) → swap-add a ＝ a
  ex2 a b = refl
```

### Trying a path

The following example tries to solve a goal by using the path `p` or `inv p`.
This example was adapted from

```agda
  private
    infixr 10 _∷_
    pattern _∷_ x xs = cons x xs

  ＝-type-info :
    Term-Agda →
    type-Type-Checker
      ( Argument-Agda Term-Agda ×
        ( Argument-Agda Term-Agda ×
          ( Term-Agda × Term-Agda)))
  ＝-type-info
    ( definition-Term-Agda
      ( quote _＝_)
      ( 𝓁 ∷ 𝒯 ∷ (cons-Argument-Agda _ l) ∷ (cons-Argument-Agda _ r) ∷ nil)) =
    return-Type-Checker (𝓁 , 𝒯 , l , r)
  ＝-type-info _ =
    type-error (unit-list (string-Error-Part "Term-Agda is not a ＝-type."))

  macro
    try-path! : Term-Agda → Term-Agda → type-Type-Checker unit
    try-path! p goal =
      ( unify goal p) <|>
      ( do
        p-type ← infer-type p
        𝓁 , 𝒯 , l , r ← ＝-type-info p-type
        unify goal
          ( definition-Term-Agda (quote inv)
            ( 𝓁 ∷
              𝒯 ∷
              hidden-Argument-Agda l ∷
              hidden-Argument-Agda r ∷
              visible-Argument-Agda p ∷
              nil)))

  module _ (a b : ℕ) (p : a ＝ b) where
    ex3 : a ＝ b
    ex3 = try-path! p

    ex4 : b ＝ a
    ex4 = try-path! p
```

### Getting the left-hand side and right-hand side of a goal

```agda
boundary-Type-Checker : Term-Agda → type-Type-Checker (Term-Agda × Term-Agda)
boundary-Type-Checker
  ( definition-Term-Agda
    ( quote Id)
    ( 𝓁 ∷ 𝒯 ∷ cons-Argument-Agda _ l ∷ cons-Argument-Agda _ r ∷ nil)) =
  return-Type-Checker (l , r)
boundary-Type-Checker t =
  type-error
    ( string-Error-Part "The term\n " ∷
      term-Error-Part t ∷
      string-Error-Part "\nis not a ＝-type." ∷
      nil)
```
