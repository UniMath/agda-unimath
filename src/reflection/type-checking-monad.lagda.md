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

The type-checking monad `TC` allows us to interact directly with Agda's type
checking mechanism. Additionally to primitives (see below), Agda includes the
the keyword `unquote` to manually unquote an element from `TC unit`.

## Definition

```agda
data ErrorPart : UU lzero where
  strErr : String → ErrorPart
  termErr : Term → ErrorPart
  pattErr : Pattern → ErrorPart
  nameErr : Name → ErrorPart

postulate
  -- The type checking monad
  TC : ∀ {a} → UU a → UU a
  returnTC : ∀ {a} {A : UU a} → A → TC A
  bindTC : ∀ {a b} {A : UU a} {B : UU b} → TC A → (A → TC B) → TC B
  -- Tries the unify the first term with the second
  unify : Term → Term → TC unit
  -- Gives an error
  typeError : ∀ {a} {A : UU a} → list ErrorPart → TC A
  -- Infers the type of a goal
  inferType : Term → TC Term
  checkType : Term → Term → TC Term
  normalise : Term → TC Term
  reduce : Term → TC Term
  -- Tries the first computation, if it fails tries the second
  catchTC : ∀ {a} {A : UU a} → TC A → TC A → TC A
  quoteTC : ∀ {a} {A : UU a} → A → TC Term
  unquoteTC : ∀ {a} {A : UU a} → Term → TC A
  quoteωTC : ∀ {A : UUω} → A → TC Term
  getContext : TC Telescope
  extendContext : ∀ {a} {A : UU a} → String → Arg Term → TC A → TC A
  inContext : ∀ {a} {A : UU a} → Telescope → TC A → TC A
  freshName : String → TC Name
  declareDef : Arg Name → Term → TC unit
  declarePostulate : Arg Name → Term → TC unit
  defineFun : Name → list Clause → TC unit
  getType : Name → TC Term
  getDefinition : Name → TC Definition
  blockOnMeta : ∀ {a} {A : UU a} → Meta → TC A
  commitTC : TC unit
  isMacro : Name → TC bool

  formatErrorParts : list ErrorPart → TC String

  -- Prints the third argument if the corresponding verbosity level is turned
  -- on (with the -v flag to Agda).
  debugPrint : String → ℕ → list ErrorPart → TC unit

  -- If 'true', makes the following primitives also normalise
  -- their results: inferType, checkType, quoteTC, getType, and getContext
  withNormalisation : ∀ {a} {A : UU a} → bool → TC A → TC A
  askNormalisation : TC bool

  -- If 'true', makes the following primitives to reconstruct hidden arguments:
  -- getDefinition, normalise, reduce, inferType, checkType and getContext
  withReconstructed : ∀ {a} {A : UU a} → bool → TC A → TC A
  askReconstructed : TC bool

  -- Whether implicit arguments at the end should be turned into metavariables
  withExpandLast : ∀ {a} {A : UU a} → bool → TC A → TC A
  askExpandLast : TC bool

  -- White/blacklist specific definitions for reduction while executing the TC computation
  -- 'true' for whitelist, 'false' for blacklist
  withReduceDefs : ∀ {a} {A : UU a} → (Σ bool λ _ → list Name) → TC A → TC A
  askReduceDefs : TC (Σ bool λ _ → list Name)

  -- Fail if the given computation gives rise to new, unsolved
  -- "blocking" constraints.
  noConstraints : ∀ {a} {A : UU a} → TC A → TC A

  -- Run the given TC action and return the first component. Resets to
  -- the old TC state if the second component is 'false', or keep the
  -- new TC state if it is 'true'.
  runSpeculative : ∀ {a} {A : UU a} → TC (Σ A λ _ → bool) → TC A

  -- Get a list of all possible instance candidates for the given meta
  -- variable (it does not have to be an instance meta).
  getInstances : Meta → TC (list Term)

  declareData : Name → ℕ → Term → TC unit
  defineData : Name → list (Σ Name (λ _ → Term)) → TC unit
```

<details><summary>Bindings</summary>

```agda
{-# BUILTIN AGDAERRORPART ErrorPart #-}
{-# BUILTIN AGDAERRORPARTSTRING strErr #-}
{-# BUILTIN AGDAERRORPARTTERM termErr #-}
{-# BUILTIN AGDAERRORPARTPATT pattErr #-}
{-# BUILTIN AGDAERRORPARTNAME nameErr #-}

{-# BUILTIN AGDATCM TC #-}
{-# BUILTIN AGDATCMRETURN returnTC #-}
{-# BUILTIN AGDATCMBIND bindTC #-}
{-# BUILTIN AGDATCMUNIFY unify #-}
{-# BUILTIN AGDATCMTYPEERROR typeError #-}
{-# BUILTIN AGDATCMINFERTYPE inferType #-}
{-# BUILTIN AGDATCMCHECKTYPE checkType #-}
{-# BUILTIN AGDATCMNORMALISE normalise #-}
{-# BUILTIN AGDATCMREDUCE reduce #-}
{-# BUILTIN AGDATCMCATCHERROR catchTC #-}
{-# BUILTIN AGDATCMQUOTETERM quoteTC #-}
{-# BUILTIN AGDATCMUNQUOTETERM unquoteTC #-}
{-# BUILTIN AGDATCMQUOTEOMEGATERM quoteωTC #-}
{-# BUILTIN AGDATCMGETCONTEXT getContext #-}
{-# BUILTIN AGDATCMEXTENDCONTEXT extendContext #-}
{-# BUILTIN AGDATCMINCONTEXT inContext #-}
{-# BUILTIN AGDATCMFRESHNAME freshName #-}
{-# BUILTIN AGDATCMDECLAREDEF declareDef #-}
{-# BUILTIN AGDATCMDECLAREPOSTULATE declarePostulate #-}
{-# BUILTIN AGDATCMDEFINEFUN defineFun #-}
{-# BUILTIN AGDATCMGETTYPE getType #-}
{-# BUILTIN AGDATCMGETDEFINITION getDefinition #-}
{-# BUILTIN AGDATCMBLOCKONMETA blockOnMeta #-}
{-# BUILTIN AGDATCMCOMMIT commitTC #-}
{-# BUILTIN AGDATCMISMACRO isMacro #-}
{-# BUILTIN AGDATCMWITHNORMALISATION withNormalisation #-}
{-# BUILTIN AGDATCMFORMATERRORPARTS formatErrorParts #-}
{-# BUILTIN AGDATCMDEBUGPRINT debugPrint #-}
-- {-# BUILTIN AGDATCMWITHRECONSTRUCTED withReconstructed #-}
-- {-# BUILTIN AGDATCMWITHEXPANDLAST withExpandLast #-}
-- {-# BUILTIN AGDATCMWITHREDUCEDEFS withReduceDefs #-}
-- {-# BUILTIN AGDATCMASKNORMALISATION askNormalisation #-}
-- {-# BUILTIN AGDATCMASKRECONSTRUCTED askReconstructed #-}
-- {-# BUILTIN AGDATCMASKEXPANDLAST askExpandLast #-}
-- {-# BUILTIN AGDATCMASKREDUCEDEFS askReduceDefs #-}
{-# BUILTIN AGDATCMNOCONSTRAINTS noConstraints #-}
{-# BUILTIN AGDATCMRUNSPECULATIVE runSpeculative #-}
{-# BUILTIN AGDATCMGETINSTANCES getInstances #-}
{-# BUILTIN AGDATCMDECLAREDATA declareData #-}
{-# BUILTIN AGDATCMDEFINEDATA defineData #-}
```

</details>

## Monad syntax

```agda
infixl 3 _<|>_
_<|>_ : {l : Level} {A : UU l} → TC A → TC A → TC A
_<|>_ = catchTC

infixl 1 _>>=_ _>>_ _<&>_
_>>=_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  TC A → (A → TC B) → TC B
_>>=_ = bindTC

_>>_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  TC A → TC B → TC B
xs >> ys = bindTC xs (λ _ → ys)

_<&>_ :
  {l1 l2 : Level} {A : UU l1} {B : UU l2} →
  TC A → (A → B) → TC B
xs <&> f = bindTC xs (λ x → returnTC (f x))
```

## Examples

The following examples show how the type-checking monad can be used. They were
adapted from alhassy's
[_gentle intro to reflection_](https://github.com/alhassy/gentle-intro-to-reflection).

### Unifying a goal with a constant

#### Manually

```agda
private
  numTCM : Term → TC unit
  numTCM h = unify (quoteTerm 314) h

  _ : unquote numTCM ＝ 314
  _ = refl
```

#### By use of a macro

```agda
  macro
    numTCM' : Term → TC unit
    numTCM' h = unify (quoteTerm 1) h

  _ : numTCM' ＝ 1
  _ = refl
```

### Modifying a term

```agda
  macro
    swap-add : Term → Term → TC unit
    swap-add (def (quote add-ℕ) (cons a (cons b nil))) hole =
      unify hole (def (quote add-ℕ) (cons b (cons a nil)))
    {-# CATCHALL #-}
    swap-add v hole = unify hole v

  ex1 : (a b : ℕ) → swap-add (add-ℕ a b) ＝ (add-ℕ b a)
  ex1 a b = refl

  ex2 : (a b : ℕ) → swap-add a ＝ a
  ex2 a b = refl
```

### Trying a path

The following example tries to solve a goal by using path `p` or `inv p`. This
example was addapted from

```agda
  private
    infixr 10 _∷_
    pattern _∷_ x xs = cons x xs

  ＝-type-info : Term → TC (Arg Term × (Arg Term × (Term × Term)))
  ＝-type-info
    ( def (quote _＝_) (𝓁 ∷ 𝒯 ∷ (arg _ l) ∷ (arg _ r) ∷ nil)) =
    returnTC (𝓁 , 𝒯 , l , r)
  ＝-type-info _ = typeError (unit-list (strErr "Term is not a ＝-type."))

  macro
    try-path! : Term → Term → TC unit
    try-path! p goal =
      ( unify goal p) <|>
      ( do
        p-type ← inferType p
        𝓁 , 𝒯 , l , r ← ＝-type-info p-type
        unify goal
          ( def (quote inv)
            ( 𝓁 ∷ 𝒯 ∷ hidden-Arg l ∷ hidden-Arg r ∷ visible-Arg p ∷ nil)))

  module _ (a b : ℕ) (p : a ＝ b) where
    ex3 : Id a b
    ex3 = try-path! p

    ex4 : Id b a
    ex4 = try-path! p
```

### Getting the lhs and rhs of a goal

```agda
boundary-TCM : Term → TC (Term × Term)
boundary-TCM
  ( def
    ( quote Id)
    ( 𝓁 ∷ 𝒯 ∷ arg _ l ∷ arg _ r ∷ nil)) =
  returnTC (l , r)
boundary-TCM t =
  typeError
    ( strErr "The term\n " ∷
      termErr t ∷
      strErr "\nis not a ＝-type." ∷
      nil)
```
