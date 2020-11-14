{- |
   Module     : Polysemy.Methodology.Composite
   License    : MIT
   Maintainer : dan.firth@homotopic.tech
   Stability  : experimental

Functions for combining polysemy-methodology with composite.
-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
module Polysemy.Methodology.Composite (
  runMethodologyRmap
, runCoRecMethodologyAsCases
, runCoRecMethodologyAsCases'
, diffractMethodology
, diffractMethodology'
, runInputCase'
, pickCoRecConstructor
, separateRecInitial
, separateRecInitial'
, stripRecInitial
, endRecInitial
, runRecInitialAsInputCompose
, runRecInitialAsInputCompose'
, separateRecTerminal
, separateRecTerminal'
, stripRecTerminal
, endRecTerminal
, fmapCMethodology
, fmapCMethodology'
) where

import Control.Arrow
import Composite.CoRecord
import Data.Vinyl
import Data.Vinyl.Functor
import Polysemy
import Polysemy.Extra
import Polysemy.Input
import Polysemy.Methodology

-- | Run a `Methodology` between two `Rec`s according to a natural transformation
-- between the interpretation functors.
--
-- @since 0.1.4.0
runMethodologyRmap :: forall f g xs r a. RMap xs =>
                      (forall y. f y -> g y)
                   -> Sem (Methodology (Rec f xs) (Rec g xs) ': r) a
                   -> Sem r a
runMethodologyRmap f = runMethodologyPure (rmap f)
{-# INLINE runMethodologyRmap #-}

-- | Run a `Methodology` from a `CoRec` to an `Input` of `Cases'`. You can then use `Polysemy.Vinyl.separateRecInput` and `Polysemy.Vinyl.stripRecInput`
-- to deal with the cases individually.
--
-- @since 0.1.0.0
runCoRecMethodologyAsCases :: forall f zs c x xs r a.
                              (zs ~ (x ': xs), RecApplicative zs, Members '[Input (Cases' f zs c)] r)
                           => Sem (Methodology (CoRec f zs) c ': r) a
                              -- ^ The Methodology to decompose.
                           -> Sem r a
runCoRecMethodologyAsCases = interpret \case
  Process b -> do
    x <- input @(Cases' f zs c)
    return $ foldCoRec x b
{-# INLINE runCoRecMethodologyAsCases #-}

-- | Reinterpreting version of `runCoRecMethodologyAsCases`.
--
--
-- @since 0.1.0.0
runCoRecMethodologyAsCases' :: forall f zs c x xs r a.
                               (zs ~ (x ': xs), RecApplicative zs)
                            => Sem (Methodology (CoRec f zs) c ': r) a
                               -- ^ The Methodology to decompose.
                            -> Sem (Input (Cases' f zs c) ': r) a
runCoRecMethodologyAsCases' = reinterpret \case
  Process b -> do
    x <- input @(Cases' f zs c)
    return $ foldCoRec x b
{-# INLINE runCoRecMethodologyAsCases' #-}

-- | Diffraction is a combination of a `cutMethodology'`, an `mconcatMethodology'` and a `runCoRecMethodologyAsCases`.
--
-- This effectively allows you to make several ad-hoc constructors for d and fully consumes the second half of the cut.
-- This turns out to be quite a good way to start a simple pipeline.
--
-- @since 0.1.0.0
diffractMethodology :: forall b f zs d x xs r a.
                       (Monoid d, zs ~ (x ': xs)
                      , RecApplicative zs
                      , Members '[ Methodology b [CoRec f zs]
                                 , Input (Cases' f zs d)] r)
                    => Sem (Methodology b d ': r) a
                       -- ^ The Methodology to decompose.
                    -> Sem r a
diffractMethodology = cutMethodology' @b @[CoRec f zs] @d
                  >>> reinterpretUnder mconcatMethodology'
                  >>> reinterpretUnder runCoRecMethodologyAsCases'
                  >>> subsume >>> subsume
{-# INLINE diffractMethodology #-}

-- | Reinterpreting version of `diffractMethodology`.
--
-- @since 0.1.0.0
diffractMethodology' :: forall b f zs d x xs r a.
                        (Monoid d, zs ~ (x ': xs), RecApplicative zs)
                     => Sem (Methodology b d ': r) a
                        -- ^ The Methodology to decompose.
                     -> Sem (Methodology b [CoRec f zs] ': Input (Cases' f zs d) ': r) a
diffractMethodology' = cutMethodology' @b @[CoRec f zs] @d
                   >>> reinterpretUnder mconcatMethodology'
                   >>> reinterpretUnder runCoRecMethodologyAsCases'
{-# INLINE diffractMethodology' #-}

-- | Run a `Case'` using `runInputConst` and a function eliminating the `Case'`.
--
-- @since 0.1.1.0
runInputCase' :: forall b f t r a.
                 (f b -> t)
              -> Sem (Input (Case' f t b) ': r) a
              -> Sem r a
runInputCase' f = runInputConst (Case' f)
{-# INLINE runInputCase' #-}

-- | Take a `Methodology` into a `CoRec` and choose a constructor.
--
-- @since 0.1.4.0
pickCoRecConstructor :: forall x f b xs r a. x ∈ xs =>
                        Sem (Methodology b (CoRec f xs) ': r) a
                     -> Sem (Methodology b (f x) ': r) a
pickCoRecConstructor = cutMethodology'
                   >>> rotateEffects2
                   >>> runMethodologyPure CoVal
{-# INLINE pickCoRecConstructor #-}

-- | Factor a `Methodology` with a `Rec` in the result by a `Methodology` to the first variable.
--
-- @since 0.1.3.0
separateRecInitial :: forall b f x xs r a.
                      Members '[Methodology b (f x), Methodology b (Rec f xs)] r
                   => Sem (Methodology b (Rec f (x ': xs)) ': r) a
                      -- ^ The Methodology to decompose.
                   -> Sem r a
separateRecInitial = interpret \case
  Process b -> do
    k   <- process @b @(f x) b
    k'  <- process @b @(Rec f xs) b
    return $ k :& k'
{-# INLINE separateRecInitial #-}

-- | Reinterpreting version of `separateRecInitial`. This assumes you want to handle
-- the separated case first.
--
-- @since 0.1.3.0
separateRecInitial' :: forall b f x xs r a.
                       Sem (Methodology b (Rec f (x ': xs)) ': r) a
                    -> Sem (Methodology b (f x) ': Methodology b (Rec f xs)': r) a
separateRecInitial' = reinterpret2 \case
  Process b -> do
    k   <- process @b @(f x) b
    k'  <- raise $ process @b @(Rec f xs) b
    return $ k :& k'
{-# INLINE separateRecInitial' #-}

-- | Like `separateRecInitial`, but reinterprets the rest of the `Rec` whilst pushing
-- the separated `Methodology` into the stack. Useful for exhausting the `Rec` and
-- dealing with the cases later.
--
-- @since 0.1.3.0
stripRecInitial :: forall b f x xs r a.
                   Members '[Methodology b (f x)] (Methodology b (Rec f xs) ': r)
                => Sem (Methodology b (Rec f (x ': xs)) ': r) a
                -> Sem (Methodology b (Rec f xs)': r) a
stripRecInitial = reinterpret \case
  Process b -> do
    k   <- process @b @(f x) b
    k'  <- process @b @(Rec f xs) b
    return $ k :& k'
{-# INLINE stripRecInitial #-}

-- | Discard a depleted `Methodology` into a `Rec` by returning `RNil`.
--
-- @since 0.1.3.0
endRecInitial :: Sem (Methodology b (Rec f '[]) ': r) a -> Sem r a
endRecInitial = interpret \case
  Process _ -> return RNil
{-# INLINE endRecInitial #-}

-- | Run a `Methodology` into a `Rec` as an `Input` over a `(->)` functor.
--
-- @since 0.1.3.0
runRecInitialAsInputCompose :: forall b f xs r a. (RMap xs,
                               Members '[ Input (Rec (Compose ((->) b) f) xs)] r)
                            => Sem (Methodology b (Rec f xs) ': r) a
                            -> Sem r a
runRecInitialAsInputCompose = interpret \case
  Process b -> do
    z <- input @(Rec (Compose ((->) b) f) xs)
    return $ rmap (($ b) . getCompose) z
{-# INLINE runRecInitialAsInputCompose #-}

-- | Reinterpreting version of `runRecInitialAsInputCompose`.
--
-- @since 0.1.3.0
runRecInitialAsInputCompose' :: forall b f xs r a. (RMap xs)
                             => Sem (Methodology b (Rec f xs) ': r) a
                             -> Sem (Input (Rec (Compose ((->) b) f) xs) ': r) a
runRecInitialAsInputCompose' = reinterpret \case
  Process b -> do
    z <- input @(Rec (Compose ((->) b) f) xs)
    return $ rmap (($ b) . getCompose) z
{-# INLINE runRecInitialAsInputCompose' #-}

-- | Factor a `Methodology` from a `Rec` by a `Methodology` from the first variable.
--
-- since @0.1.3.0
separateRecTerminal :: forall x c f xs r a. (Monoid c,
                       Members '[Methodology (f x) c, Methodology (Rec f xs) c] r)
                    => Sem (Methodology (Rec f (x ': xs)) c ': r) a
                    -> Sem r a
separateRecTerminal = interpret \case
  Process (b :& bs) -> do
    k   <- process @(f x) b
    k'  <- process @(Rec f xs) @c bs
    return $ k <> k'
{-# INLINE separateRecTerminal #-}

-- | Reinterpreted version of `separateRecTerminal`.
--
-- since @0.1.3.0
separateRecTerminal' :: forall x c f xs r a. Monoid c
                     => Sem (Methodology (Rec f (x ': xs)) c ': r) a
                     -> Sem (Methodology (f x) c ': Methodology (Rec f xs) c ': r) a
separateRecTerminal' = reinterpret2 \case
  Process (b :& bs) -> do
    k   <- process @(f x) b
    k'  <- raise $ process @(Rec f xs) @c bs
    return $ k <> k'
{-# INLINE separateRecTerminal' #-}

-- | Like `separateRecTerminal, but reinterprets the rest of the `Rec` whilst pushing
-- the separated `Methodology` into the stack. Useful for exhausting the `Rec` and
-- dealing with the cases later.
--
-- since @0.1.3.0
stripRecTerminal :: forall x c f xs r a. (Monoid c,
                    Members '[Methodology (f x) c] (Methodology (Rec f xs) c ': r))
                 => Sem (Methodology (Rec f (x ': xs)) c ': r) a
                 -> Sem (Methodology (Rec f xs) c ': r) a
stripRecTerminal = reinterpret \case
  Process (b :& bs) -> do
    k   <- process @(f x) b
    k'  <- process @(Rec f xs) @c bs
    return $ k <> k'
{-# INLINE stripRecTerminal #-}

-- | Discard a depleted `Methodology` fom a `Rec` by returning `mempty`.
--
-- @since 0.1.3.0
endRecTerminal :: Monoid b => Sem (Methodology (Rec f '[]) b ': r) a -> Sem r a
endRecTerminal = interpret \case
  Process _ -> return mempty
{-# INLINE endRecTerminal #-}

-- | Like `fmapMethodology`, but used with a `Compose`d functor to strip the top
-- layer from the functor.
--
-- @since 0.1.4.0
fmapCMethodology :: forall f g h b c r a. Traversable f =>
                     Sem (Methodology ((f :. g) b) ((f :. h) c) ': r) a
                  -> Sem (Methodology (g b) (h c) ': r) a
fmapCMethodology = reinterpret \case
  Process b -> Compose <$> traverse (process @(g b) @(h c)) (getCompose b)
{-# INLINE fmapCMethodology #-}

-- | Reinterpreting version of `fmapCMethodology`.
--
-- @since 0.1.4.0
fmapCMethodology' :: forall f g h b c r a. Traversable f =>
                     Sem (Methodology ((f :. g) b) ((f :. h) c) ': r) a
                  -> Sem (Methodology (g b) (h c) ': r) a
fmapCMethodology' = reinterpret \case
  Process b -> Compose <$> traverse (process @(g b) @(h c)) (getCompose b)
{-# INLINE fmapCMethodology' #-}
